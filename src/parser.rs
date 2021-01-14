use nom::{
    call, char, complete, delimited, do_parse, escaped_transform,
    many0, flat_map, map, named, named_args, none_of, opt,
    separated_list, separated_pair, tag, take, take_while_m_n,
    take_while1, take_while, tuple, terminated, Err, IResult,
    parse_to, preceded, verify, Slice,
};
use nom_locate::LocatedSpan;
use indexmap::IndexMap;
use vecshard::{ VecShard, ShardExt };
use itertools::Itertools;
use derive_more::{ DebugCustom, Display };
use anyhow::{anyhow, Context, Error, Result};
use yansi::Paint;

use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Write;
use std::rc::Rc;

use crate::ast;
use crate::infer;
use crate::ast::{ Ident, IAstNode, AstNodeID };
use ast::Symbols;

#[derive(DebugCustom)]
#[debug(fmt = "File({:?})", path)]
pub struct File {
    pub prog: String,
    pub path: String,
}

pub type Span<'a> = LocatedSpan<&'a str, ErrorTrackerRef<'a>>;

fn range_span<'a, 's, X>(
    a: LocatedSpan<&'a str, X>,
    b: LocatedSpan<&'a str, X>,
    ctx: &ParseContext<'a, 's>
) -> LocatedSpan<&'a str, X> {
    let a_ofs = a.location_offset();
    let b_ofs = b.location_offset();
    let b_len = b.fragment().len();
    unsafe {
        LocatedSpan::new_from_raw_offset(
            a_ofs,
            a.location_line(),
            &ctx.file.prog[a_ofs..b_ofs+b_len],
            a.extra,
        )
    }
}

trait IntoAstSpan<'a, 's> {
    fn into_ast_span(self, ctx: &RefCell<ParseContext<'a, 's>>) -> ast::Span<'a>;
}

impl<'a, 's> IntoAstSpan<'a, 's> for Span<'a> {
    fn into_ast_span(self, ctx: &RefCell<ParseContext<'a, 's>>) -> ast::Span<'a> {
        unsafe {
            ast::Span::new_from_raw_offset(
                self.location_offset(),
                self.location_line(),
                *self.fragment(),
                ctx.borrow().file,
            )
        }
    }
}

pub trait FormatAtPos<'a, 's> {
    fn format_err_at_pos(
        &self,
        msg: &str,
        underline: bool,
        ctx: &ParseContext<'a, 's>,
    ) -> Result<String>;
    fn format_note_at_pos(
        &self,
        msg: &str,
        underline: bool,
        ctx: &ParseContext<'a, 's>,
    ) -> Result<String>;
}

impl<'a, 's> FormatAtPos<'a, 's> for Span<'a> {
    fn format_err_at_pos(
        &self,
        msg: &str,
        underline: bool,
        ctx: &ParseContext<'a, 's>,
    ) -> Result<String> {
        format_at_pos(
            self,
            &Paint::red("error: ").bold().to_string(),
            7,
            msg,
            ctx.file,
            underline,
        )
    }

    fn format_note_at_pos(
        &self,
        msg: &str,
        underline: bool,
        ctx: &ParseContext<'a, 's>,
    ) -> Result<String> {
        format_at_pos(
            self,
            &Paint::yellow("note: ").bold().to_string(),
            6,
            msg,
            ctx.file,
            underline,
        )
    }
}

#[derive(Display, Debug, Clone, Hash, Eq, PartialEq)]
#[display(fmt = "{}/{}", "path.join(\":\")", id)]
pub struct Path<'a> {
    path: Vec<&'a str>,
    id: usize, // shadowing variables share the same path but different id
}

impl<'a> Path<'a> {
    fn empty_with_id(id: usize) -> Self {
        Self { path: Vec::new(), id }
    }
    fn make_unique(&mut self, ctx: &mut ParseContext) {
        self.id = ctx.gen_path_id();
    }
    fn push(&mut self, part: &'a str) {
        self.path.push(part);
    }
    fn pop(&mut self) -> Option<&'a str> {
        self.path.pop()
    }
}

#[derive(Debug, Clone, Copy)]
enum OperatorAssoc {
    Left = 0,
    Right = 1,
}

#[derive(Debug, Clone, Copy)]
struct OperatorInfo {
    precedence: usize,
    associativity: OperatorAssoc,
}

impl OperatorInfo {
    /// Absolute precedence assure's every precedence-assoc has a
    /// unique precedence. This is necessary since only once
    /// associativity is permitted per precedence level.
    fn abs_precedence(&self) -> usize {
        self.precedence * 2 + self.associativity as usize
    }
}

struct OpChain<'a> {
    first: ast::Expr<'a>,
    rest: VecShard<((Ident<'a>, OperatorInfo), ast::Expr<'a>)>,
}

impl<'a> OpChain<'a> {
    fn new(
    first: ast::Expr<'a>,
    rest: VecShard<((Ident<'a>, OperatorInfo), ast::Expr<'a>)>,
    ) -> Self {
        Self{ first, rest }
    }

    fn len(&self) -> usize {
        self.rest.len() + 1
    }

    /// Split OpChain at index.
    /// Produces: `([..idx], op, ]idx..])`. Panics if idx >= len || len == 1
    fn split_at(self, idx: usize) -> (Self, (Ident<'a>, OperatorInfo), Self) {
        assert!(idx < self.len());
        assert!(self.len() >= 2);

        let (left_rest, mut right_rest) = self.rest.split_inplace_at(idx);
        let (op, right_first) = right_rest.next().unwrap();

        (Self { first: self.first, rest: left_rest }, op,
         Self { first: right_first, rest: right_rest })
    }

    fn split_at_first_prec(self, prec: usize) ->
        Result<(Self, (Ident<'a>, OperatorInfo), Self), Self>
    {
        if self.len() == 1 {
            Err(self)
        } else {
            match self.rest.iter()
                .find_position(|((_, opinfo), _)| opinfo.abs_precedence() == prec)
            {
                Some((i, _)) => Ok(self.split_at(i)),
                None => Err(self),
            }
        }
    }

    fn split_at_last_prec(self, prec: usize) ->
        Result<(Self, (Ident<'a>, OperatorInfo), Self), Self>
    {
        if self.len() == 1 {
            Err(self)
        } else {
            match self.rest.iter().rev()
                .find_position(|((_, opinfo), _)| opinfo.abs_precedence() == prec)
            {
                Some((i, _)) => {
                    let len = self.rest.len();
                    Ok(self.split_at(len - i - 1))
                },
                None => Err(self),
            }
        }
    }

    /// Get the lowest precedence of operation in the chain. None if len == 1.
    fn lowest_prec(&self) -> Option<(usize, OperatorAssoc)> {
        self.rest.iter()
            .map(|((_, opinfo), _)| (opinfo.abs_precedence(), opinfo.associativity))
            .min_by_key(|(p, _)| *p)
    }

    fn mk_op<'sym>(
        op: Ident<'a>,
        a: ast::Expr<'a>,
        b: ast::Expr<'a>,
        ctx: &RefCell<ParseContext<'a, 'sym>>,
    ) -> ast::Expr<'a> {
        let span = range_span(a.span(), b.span(), &ctx.borrow());

        ast::Expr::FunCal(
            ast::FunCal::new(span, op, vec![a, b], &mut ctx.borrow_mut())
        )
    }

    fn foldl<'sym>(
        self,
        prec: usize,
        ctx: &RefCell<ParseContext<'a, 'sym>>
    ) -> ast::Expr<'a> {
        match self.split_at_last_prec(prec) {
            Ok((left, (op, _), right)) =>
                Self::mk_op(op, left.foldl(prec, ctx), right.fold(ctx), ctx),

            Err(this) => this.fold(ctx),
        }
    }

    fn foldr<'sym>(
        self,
        prec: usize,
        ctx: &RefCell<ParseContext<'a, 'sym>>
    ) -> ast::Expr<'a> {
        match self.split_at_first_prec(prec) {
            Ok((left, (op, _), right)) =>
                Self::mk_op(op, left.fold(ctx), right.foldr(prec, ctx), ctx),

            Err(this) => this.fold(ctx),
        }
    }

    /// Fold the OpChain into an expression tree transformingn the
    /// operations into funcals
    fn fold<'sym>(self, ctx: &RefCell<ParseContext<'a, 'sym>>) -> ast::Expr<'a> {
        let (min_prec, assoc) = if let Some(min_prec) = self.lowest_prec() {
            min_prec
        } else {
            return self.first;
        };

        match assoc {
            OperatorAssoc::Left => self.foldl(min_prec, ctx),
            OperatorAssoc::Right => self.foldr(min_prec, ctx),
        }
    }
}

#[derive(Debug)]
pub struct ParseContext<'a, 'sym> {
    tvar_gen: infer::TvarGenerator,
    next_path_id: usize,
    next_node_id: usize,
    current_path: Path<'a>,
    operators: IndexMap<Rc<Path<'a>>, OperatorInfo>,
    pub file: &'a File,
    pub symbols: &'sym mut Symbols<'a>,
}

impl<'a, 'sym> ParseContext<'a, 'sym> {
    pub fn new(
        file: &'a File,
        symbols: &'sym mut Symbols<'a>,
        tvs: infer::TvarGenerator
    ) -> Self {
        Self {
            tvar_gen: tvs,
            current_path: Path::empty_with_id(0),
            next_node_id: 0,
            next_path_id: 1,
            operators: IndexMap::new(),
            file,
            symbols,
        }
    }
    fn gen_path_id(&mut self) -> usize {
        let r = self.next_path_id;
        self.next_path_id += 1;
        r
    }
    pub fn gen_id(&mut self) -> AstNodeID {
        let r = self.next_node_id;
        self.next_node_id += 1;
        r
    }
    pub fn push_path<E>(&mut self, part: LocatedSpan<&'a str, E>) {
        self.current_path.push(part.fragment());
    }
    pub fn pop_path(&mut self) {
        self.current_path.pop();
    }
    pub fn current_path(&self) -> &Path<'a> {
        &self.current_path
    }
    pub fn mk_path<E>(&mut self, part: LocatedSpan<&'a str, E>) -> Rc<Path<'a>> {
        self.mk_path_raw(part.fragment())
    }
    pub fn mk_path_raw(&mut self, part: &'a str) -> Rc<Path<'a>> {
        let mut path = self.current_path.clone();
        path.push(part);
        path.make_unique(self);
        Rc::new(path)
    }
    pub fn insert_fundef(&mut self, path: Rc<Path<'a>>, node: Rc<ast::FunDef<'a>>) {
        self.symbols.fundefs.insert(path, node);
    }
    pub fn insert_type(&mut self, path: Rc<Path<'a>>, ty: infer::Type<'a>) {
        self.symbols.types.insert(path, ty);
    }
    pub fn insert_op_info(&mut self, path: Rc<Path<'a>>, info: OperatorInfo) {
        self.operators.insert(path, info);
    }
    pub fn get_type(&self, path: &Rc<Path<'a>>) -> Result<&infer::Type<'a>> {
        self.symbols.types.get(path).context("type not found in type registry")
    }
    pub fn get_op_info(&self, path: &Rc<Path<'a>>) -> Result<OperatorInfo> {
        self.operators.get(path)
            .with_context(|| format!("operator {} not found in registry", path))
            .map(|oi|*oi)
    }
}

impl<'a, 'sym> infer::TvarGen for ParseContext<'a, 'sym> {
    fn fresh_tvar(&mut self) -> infer::TypeVar {
        self.tvar_gen.fresh_tvar()
    }
}

// ======== File Parsing ========

#[derive(Clone, DebugCustom)]
#[debug(fmt = "ErrorTrackerRef()")]
pub struct ErrorTrackerRef<'a>(Rc<RefCell<ErrorTracker<'a>>>);

struct ErrorTracker<'a> {
    furthest_err: usize,
    errors: Vec<(Span<'a>, String)>,
}

impl<'a> ErrorTracker<'a> {
    fn new() -> Self {
        Self {
            furthest_err: 0,
            errors: vec![],
        }
    }

    fn add_err(&mut self, span: Span<'a>, desc: String) {
        let ofs = span.location_offset();

        if ofs > self.furthest_err {
            self.furthest_err = ofs;
            self.errors.clear();
        }
        if ofs == self.furthest_err {
            self.errors.push((span, desc))
        }
    }
}

// original version of eof macro in nom doesnt work without Copy being
// implemented on Span
macro_rules! eof {
    ($i:expr,) => {{
        use nom::error_position;
        use nom::InputLength;
        use nom::{error::ErrorKind, Err};

        if ($i).input_len() == 0 {
            Ok(($i.clone(), $i))
        } else {
            Err(Err::Error(error_position!($i, ErrorKind::Eof)))
        }
    }};
}

macro_rules! parse {
    ($i:expr, directive Rc<$ty:ident>, $ctx:expr) => {
        <Rc<$ty> as Directive>::parse($i, $ctx)
    };
    ($i:expr, directive $ty:ident, $ctx:expr) => {
        <$ty as Directive>::parse($i, $ctx)
    };
    ($i:expr, Rc<$ty:ident>, $ctx:expr) => {
        <Rc<ast::$ty> as Parsable>::parse($i, $ctx)
    };
    ($i:expr, $ty:ident, $ctx:expr) => {
        <ast::$ty as Parsable>::parse($i, $ctx)
    };
}

macro_rules! from_raw_ast {
    (Rc<$ty:ident>, $raw:expr, $ctx:expr, $scp:expr) => {
        <Rc<ast::$ty> as FromRawAst<'_, $ty>>::from_raw_ast($raw, $ctx, $scp)
    };
    ($ty:ident, $raw:expr, $ctx:expr, $scp:expr) => {
        <ast::$ty as FromRawAst<'_, $ty>>::from_raw_ast($raw, $ctx, $scp)
    };
}

macro_rules! shrink_span {
    ($a:expr, $b:expr) => {{
        let a_ofs = $a.location_offset();
        let b_ofs = $b.location_offset();
        $a.slice(..b_ofs-a_ofs)
    }};
}

macro_rules! get_span {
    ($i:expr, $parser:ident!($($args:tt)*)) => ({
        let (s, r) = $parser!($i.clone(), $($args)*)?;
        let range = shrink_span!($i, s);
        Ok((s, (r, range)))
    });
}

// TODO: move current_path to scope instead of parse context

macro_rules! tok {
    ($i:expr) => (tok!($i,));
    ($i:expr,) => ({
        use nom::InputLength;
        take_while_m_n!($i, 0, $i.input_len(), |c: char| c.is_whitespace())
    });
    ($i:expr, $parser:ident!($($args:tt)*)) => ({
        let (i, _) = tok!($i)?;
        $parser!(i, $($args)*)
    });
}

macro_rules! tok_tag {
    ($i:expr, $tag:expr) => {
        tok!($i, describe!(&format!("'{}'", $tag), tag!($tag)))
    };
}

macro_rules! parens {
    ($i:expr, $parser:ident!($($args:tt)*)) => {
        delimited!($i as Span<'a>, tok_tag!("("), $parser!($($args)*), tok_tag!(")"))
    };
}

macro_rules! braces {
    ($i:expr, $parser:ident!($($args:tt)*)) => {
        delimited!($i as Span<'a>, tok_tag!("{"), $parser!($($args)*), tok_tag!("}"))
    };
}

macro_rules! backticks {
    ($i:expr, $parser:ident!($($args:tt)*)) => {
        delimited!($i as Span<'a>, tok_tag!("`"), $parser!($($args)*), tok_tag!("`"))
    };
}

macro_rules! describe {
    ($i:expr, $desc:expr, $parser:ident!($($args:tt)*)) => ({
        let i = $i;
        match $parser!(i.clone(), $($args)*) {
            Err(e) => {
                i.extra.0.borrow_mut().add_err(i.clone(), $desc.to_string());
                Err(e)
            },
            o => o,
        }
    });
}

// the function version of alt properly `or`s errors together
macro_rules! alt {
    (@parser $parser:ident!($($args:tt)*) => $map:expr) => (
        |i| map!(i as Span, $parser!($($args)*), $map)
    );
    (@parser $parser:ident!($($args:tt)*)) => (
        |i| $parser!(i as Span, $($args)*)
    );

    ($i:expr, $parser:ident!($($args:tt)*) $(=> { $map:expr })?) => (
        alt!(@parser $parser!($($args)*) $(=> $map)?)($i)
    );
    ($i:expr, $($parser:ident!($($args:tt)*) $(=> { $map:expr })?)|+) => (
        nom::branch::alt(($(alt!(@parser $parser!($($args)*) $(=> $map)?)),+))($i)
    );
}

/// A directive is a phase 1 only ast node. It does not get
/// transformed into a real ast node.
pub trait Directive<'a> : Sized + Discover<'a> {
    fn parse<'sym>(i: Span<'a>, ctx: &RefCell<ParseContext<'a, 'sym>>)
        -> IResult<Span<'a>, Self>;
}

/// A parsable is first a Raw parsed type in phase 1 or parsing and
/// once globals are discovered, it gets transformed into a real ast
/// node in phase 2 (from_raw_ast).
pub trait Parsable<'a> : Sized + FromRawAst<'a, <Self as Parsable<'a>>::Raw> {
    type Raw : Discover<'a>;
    fn parse<'sym>(i: Span<'a>, ctx: &RefCell<ParseContext<'a, 'sym>>)
        -> IResult<Span<'a>, Self::Raw>;
}
macro_rules! Parser {
    (@self $ty:path,   ) => ($ty);
    (@self $ty:path, Rc) => (Rc<$ty>);
    (for directive $(<$ty:ident>)? $o:ident($ctx:ident) = $submac:ident!( $($args:tt)* ))
        => (
            impl<'a> Directive<'a> for Parser!(@self $o<'a>, $($ty)?) {
                fn parse<'sym>(
                    i: Span<'a>,
                    $ctx: &RefCell<ParseContext<'a, 'sym>>,
                ) -> IResult<Span<'a>, Self> {
                    $submac!(i, $($args)*)
                }
            }
        );
    (for $(<$ty:ident>)? $o:ident($ctx:ident) = $submac:ident!( $($args:tt)* ))
        => (
            impl<'a> Parsable<'a> for Parser!(@self ast::$o<'a>, $($ty)?) {
                type Raw = $o<'a>;
                fn parse<'sym>(
                    i: Span<'a>,
                    $ctx: &RefCell<ParseContext<'a, 'sym>>,
                ) -> IResult<Span<'a>, Self::Raw> {
                    $submac!(i, $($args)*)
                }
            }
        );
}
named!(ident_impl(Span) -> Span,
    map!(get_span!(tuple!(
        take_while!(|c: char| c == '_'),
        take_while1!(|c: char| c.is_lowercase()),
        take_while!(|c: char| c == '_' || c.is_alphanumeric())
    )), |(_, s)| s));

named!(op_ident_impl(Span) -> Span,
    map!(get_span!(
        verify!(
            take_while!(|c: char| {
                !c.is_alphanumeric() &&
                    !c.is_whitespace() &&
                    "(){}[];,`".find(c).is_none()
            }),
            |res: &Span| match *res.fragment() {
                "|" | ":" | "::" | "()" | "=" => false,
                _ => true,
            }
        )
    ), |(_, s)| s));

named_args!(ident<'a>()<Span<'a>, Span<'a>>, tok!(
    describe!("ident", alt!(
         call!(ident_impl) | backticks!(call!(op_ident_impl))
    ))));

named_args!(op_ident<'a>()<Span<'a>, Span<'a>>, tok!(
    describe!("operator ident", alt!(
        call!(op_ident_impl) | backticks!(call!(ident_impl))
    ))));

named!(ty_ident(Span) -> Span,
    tok!(describe!("type ident", map!(get_span!(alt!(
        tuple!(
            take_while!(|c: char| c == '_'),
            take_while1!(|c: char| c.is_uppercase()),
            take_while!(|c: char| c == '_' || c.is_alphanumeric())
        ) => {|_| ()} |
        tok_tag!("()") => {|_| ()}
    )), |(_, s)| s))));

pub struct VarRef<'a>(Span<'a>);
Parser!(for VarRef(_ctx) = map!(call!(ident), |i| VarRef(i)));

pub struct IntLit<'a>(Span<'a>, i32);
Parser!(for IntLit(_ctx) = tok!(map!(
    describe!("int", get_span!(flat_map!(
                take_while1!(|c: char| c.is_numeric()),
                parse_to!(i32)))),
    |(val, span)| IntLit(span, val)
)));

pub struct StrLit<'a>(Span<'a>, String);
Parser!(for StrLit(_ctx) = do_parse!(
        val: tok!(describe!(
                "string",
                get_span!(delimited!(
                        char!('"'),
                        escaped_transform!(none_of!("\\\""),
                        '\\',
                        alt!(tag!("\\") => { |_| "\\" } |
                            tag!("\"") => { |_| "\"" } |
                            tag!("n")  => { |_| "\n" })),
                            char!('"')
                ))
        )) >>
        (StrLit(val.1, val.0))));

pub struct BooLit<'a>(Span<'a>, bool);
Parser!(for BooLit(_ctx) = do_parse!(
        val: tok!(describe!(
                "bool",
                get_span!(alt!(tag!("True") => { |_| true } |
                               tag!("False") => { |_| false }))
        )) >>
        (BooLit(val.1, val.0))));

pub enum StructLitFields<'a>{
    Named(Vec<(Span<'a>, Expr<'a>)>),
    UnNamed(Vec<Expr<'a>>),
}
pub struct StructLit<'a>{
    span: Span<'a>,
    name: Span<'a>,
    fields: StructLitFields<'a>,
}
Parser!(for StructLit(ctx) = map!(tok!(get_span!(do_parse!(
    name: call!(ty_ident) >>
    fields: alt!(
        parens!(separated_list!(tok_tag!(","), parse!(Expr, ctx))) => {
            |fields| StructLitFields::UnNamed(fields)
        } |
        braces!(separated_list!(tok_tag!(","),
                                tuple!(
                                    call!(ident),
                                    tok_tag!(":"),
                                    parse!(Expr, ctx)))) => {
            |fields| StructLitFields::Named(
                fields.into_iter().map(|(n, _, e)| (n, e)).collect()
            )
        }
    ) >>
    ((name, fields))
))),
|((name, fields), span)| StructLit { span, name, fields }));

pub struct If<'a>{
    span: Span<'a>,
    clauses: Vec<(Expr<'a>, Expr<'a>)>,
    otherwise: Option<Box<Expr<'a>>>,
}
Parser!(for If(ctx) = map!(tok!(get_span!(do_parse!(
    tok_tag!("if") >>
    opt!(tok_tag!("|")) >>
    clauses: separated_list!(tok_tag!("|"), separated_pair!(parse!(Expr, ctx),
                                                            tok_tag!(":"),
                                                            parse!(Expr, ctx))) >>
    otherwise: opt!(map!(preceded!(tok_tag!("|"), parse!(Expr, ctx)), |o| Box::new(o))) >>
    (clauses, otherwise)
))),
|((clauses, otherwise), span)| If { span, clauses, otherwise }));

pub struct FunCal<'a>{
    span: Span<'a>,
    name: Span<'a>,
    args: Vec<Expr<'a>>,
}
Parser!(for FunCal(ctx) = map!(tok!(get_span!(do_parse!(
    name: call!(ident) >>
    args: parens!(separated_list!(tok_tag!(","), parse!(Expr, ctx))) >>
    (name, args)
))),
|((name, args), span)| FunCal { span, name, args }));

pub struct Block<'a>{
    span: Span<'a>,
    body: Vec<Stmt<'a>>,
    ret: Option<Box<Expr<'a>>>,
}
Parser!(for Block(ctx) = map!(tok!(get_span!(braces!(do_parse!(
    body: many0!(terminated!(parse!(Stmt, ctx), tok_tag!(";"))) >>
    ret: opt!(map!(parse!(Expr, ctx), |e| Box::new(e))) >>
    ((body, ret))
)))),
|((body, ret), span)| Block {span, body, ret}));

pub enum Expr<'a>{
    Block(Block<'a>),
    If(If<'a>),
    FunCal(FunCal<'a>),
    StructLit(StructLit<'a>),
    StrLit(StrLit<'a>),
    IntLit(IntLit<'a>),
    BooLit(BooLit<'a>),
    VarRef(VarRef<'a>),
    OpChain(Box<Expr<'a>>, Vec<(Span<'a>, Expr<'a>)>),
}

fn operation_term<'a, 'sym>(
    i: Span<'a>,
    ctx: &RefCell<ParseContext<'a, 'sym>>
) -> IResult<Span<'a>, Expr<'a>> {
    alt!(i,
         parse!(Block,       ctx) => { |b| Expr::Block(b) }
         | parse!(If,        ctx) => { |i| Expr::If(i) }
         | parse!(FunCal,    ctx) => { |f| Expr::FunCal(f) }
         | parse!(StructLit, ctx) => { |s| Expr::StructLit(s) }
         | parse!(StrLit,    ctx) => { |s| Expr::StrLit(s) }
         | parse!(IntLit,    ctx) => { |i| Expr::IntLit(i) }
         | parse!(BooLit,    ctx) => { |b| Expr::BooLit(b) }
         | parse!(VarRef,    ctx) => { |v| Expr::VarRef(v) })
}
Parser!(for Expr(ctx) = do_parse!(
    first: call!(operation_term, ctx) >>
    rest: many0!(tuple!(call!(op_ident), call!(operation_term, ctx))) >>
    (if rest.len() == 0 {
        first
    } else {
        Expr::OpChain(Box::new(first), rest)
    })
));

pub struct VarLet<'a>{
    span: Span<'a>,
    var: Span<'a>,
    val: Expr<'a>,
}
Parser!(for VarLet(ctx) = map!(tok!(get_span!(do_parse!(
    var: call!(ident) >>
    tok_tag!("=") >>
    val: parse!(Expr, ctx) >>
    ((var, val))
))),
|((var, val), span)| VarLet { span, var, val }));

pub enum Stmt<'a>{
    Expr(Expr<'a>),
    VarLet(VarLet<'a>),
}
Parser!(for Stmt(ctx) = alt!(
        parse!(VarLet, ctx) => { |v| Stmt::VarLet(v) }
      | parse!(Expr, ctx)   => { |e| Stmt::Expr(e) }
));

pub struct FunDef<'a>{
    span: Span<'a>,
    name: Span<'a>,
    argnames: Vec<Span<'a>>,
    body: Expr<'a>,
}
Parser!(for <Rc>FunDef(ctx) = map!(tok!(get_span!(do_parse!(
    name: call!(ident) >>
    argnames: parens!(separated_list!(tok_tag!(","), call!(ident))) >>
    tok_tag!("=") >>
    body: parse!(Expr, ctx) >>
    ((name, argnames, body))
))),
|((name, argnames, body), span)| FunDef { span, name, argnames, body } ));

pub struct Type<'a>{
    span: Span<'a>,
    name: Span<'a>,
    args: Vec<Type<'a>>,
}
Parser!(for Type(ctx) = map!(tok!(get_span!(do_parse!(
    name: call!(ty_ident) >>
    args: many0!(preceded!(tok_tag!("."), alt!(parens!(parse!(Type, ctx)) |
                                               parse!(Type, ctx)))) >>
    ((name, args))
))),
|((name, args), span)| Type { span, name, args }));

pub struct StructDef<'a> {
    span: Span<'a>,
    name: Span<'a>,
    field_names: Option<Vec<Span<'a>>>,
    field_types: Vec<Type<'a>>,
}
Parser!(for StructDef(ctx) = map!(tok!(get_span!(do_parse!(
    tok_tag!("struct") >>
    name: call!(ty_ident) >>
    fields: alt!(
        braces!(separated_list!(tok_tag!(","),
                                tuple!(call!(ident), tok_tag!("::"), parse!(Type, ctx)))
        ) => {|fields|{
            let mut fnames = Vec::with_capacity(fields.len());
            let mut ftypes = Vec::with_capacity(fields.len());
            for (fname, _, ftype) in fields.into_iter() {
                fnames.push(fname);
                ftypes.push(ftype);
            }
            (Some(fnames), ftypes)
        }} |
        parens!(separated_list!(tok_tag!(","), parse!(Type, ctx))) => {|fts|(None, fts)}
    ) >>
    ((name, fields.0, fields.1))
))),
|((name, field_names, field_types), span)| StructDef {
    span, name, field_names, field_types
}));

pub struct InfixDef<'a> {
    span: Span<'a>,
    name: Span<'a>,
    info: OperatorInfo,
}
Parser!(for directive InfixDef(ctx) = map!(tok!(get_span!(do_parse!(
    tok_tag!("infix") >>
    assoc: alt!(
        tok_tag!("left") => { |_| OperatorAssoc::Left } |
        tok_tag!("right") => { |_| OperatorAssoc::Right }
    ) >>
    prec: tok!(describe!("positive integer", flat_map!(
        take_while1!(|c: char| c.is_numeric()),
        parse_to!(usize)
    ))) >>
    name: call!(op_ident) >>
    ((assoc, prec, name))
))),
|((assoc, prec, name), span)| InfixDef {
    span: span,
    name: name,
    info: OperatorInfo{ associativity: assoc, precedence: prec },
}));

pub enum TopLvl<'a>{
    StructDef(StructDef<'a>),
    FunDef(FunDef<'a>),
}
Parser!(for TopLvl(ctx) =
    terminated!(
        alt!(
            parse!(Rc<FunDef>, ctx) => { |fd| TopLvl::FunDef(fd) } |
            parse!(StructDef, ctx) => { |sd| TopLvl::StructDef(sd) }
        ),
        tok_tag!(";")));

pub enum TopLvlDirective<'a>{
    InfixDef(InfixDef<'a>),
}
Parser!(for directive TopLvlDirective(ctx) =
    terminated!(
        alt!(
            parse!(directive InfixDef, ctx) => { |id| TopLvlDirective::InfixDef(id) }
        ),
        tok_tag!(";")));

pub struct Module<'a>(Vec<TopLvl<'a>>, Vec<TopLvlDirective<'a>>);
fn parse_toplvls<'a, 'sym>(
    i: Span<'a>,
    ctx: &RefCell<ParseContext<'a, 'sym>>,
) -> IResult<Span<'a>, (Vec<TopLvl<'a>>, Vec<TopLvlDirective<'a>>)> {
    enum AB<'a> {
        TLD(TopLvlDirective<'a>),
        TL(TopLvl<'a>),
    }

    let mut tls = Vec::with_capacity(50);
    let mut dirs = Vec::with_capacity(10);

    let (i, all) = many0!(i, complete!(alt!(
        parse!(directive TopLvlDirective, ctx) => { |tld| AB::TLD(tld) } |
        parse!(TopLvl, ctx) => { |tl| AB::TL(tl) }
    )))?;

    for e in all {
        match e {
            AB::TLD(tld) => dirs.push(tld),
            AB::TL(tl) => tls.push(tl),
        }
    }

    Ok((i, (tls, dirs)))
}
Parser!(for Module(ctx) = do_parse!(
    toplvls: call!(parse_toplvls, ctx) >>
    tok!(eof!()) >>
    (Module(toplvls.0, toplvls.1))
));

// ======== Ast-gen and Scope Validation ========


pub struct Scope<'a, 'p> {
    parent: Option<&'p Scope<'a, 'p>>,
    scope: IndexMap<&'a str, Rc<Path<'a>>>,
}

impl<'a, 'p> Scope<'a, 'p> {
    fn new() -> Self {
        Self {
            parent: None,
            scope: IndexMap::with_capacity(5),
        }
    }

    fn subscope<'b>(&'b self) -> Scope<'a, 'b> {
        Scope {
            parent: Some(self),
            scope: IndexMap::with_capacity(5),
        }
    }
    fn get(&self, id: &Span<'a>) -> Option<&Rc<Path<'a>>> {
        self.scope
            .get(id.fragment())
            .or_else(|| self.parent.and_then(|p| p.get(id)))
    }
    fn try_get<'s>(
        &self,
        id: &Span<'a>,
        desc: &str,
        ctx: &ParseContext<'a, 's>,
    ) -> Result<&Rc<Path<'a>>> {
        self.get(id).with_context(|| {
            id.format_err_at_pos(
                &format!("{} `{}` not found in scope", desc, id),
                true,
                ctx,
            )
            .unwrap()
        })
    }
    fn try_get_ident<'s>(
        &self,
        id: Span<'a>,
        desc: &str,
        ctx: &RefCell<ParseContext<'a, 's>>,
    ) -> Result<Ident<'a>> {
        Ok(Ident::new(
            Rc::clone(self.try_get(&id, desc, &ctx.borrow())?),
            id.into_ast_span(ctx)
        ))
    }

    fn bind<E>(&mut self, id: &LocatedSpan<&'a str, E>, path: Rc<Path<'a>>) {
        self.bind_raw(id.fragment(), path);
    }
    fn bind_raw(&mut self, id: &'a str, path: Rc<Path<'a>>) {
        let overriding = self.scope.insert(id, path).is_some();
        assert!(!overriding);
    }
}

trait Discover<'a> {
    fn discover<'scp, 'sym>(
        &self,
        _ctx: &RefCell<ParseContext<'a, 'sym>>,
        _scp: &RefCell<Scope<'a, 'scp>>,
    ) -> Result<()> { Ok(()) }
}

macro_rules! Discover {
    (@type $ty:path,   ) => ($ty);
    (@type $ty:path, Rc) => (Rc<$ty>);
    (for [$($o:ident$(: $ty:ident)?),*]) => (
        $(
            impl<'a> Discover<'a>
            for Discover!(@type $o<'a>, $($ty)?) {}
        )*
    );
    (for $o:ident($this:pat, $ctx:ident, $scp:ident)$(: $ty:ident)?
     = $body:expr) => (
        impl<'a> Discover<'a>
        for Discover!(@type $o<'a>, $($ty)?) {
            fn discover<'scp, 'sym>(
                &self,
                $ctx: &RefCell<ParseContext<'a, 'sym>>,
                $scp: &RefCell<Scope<'a, 'scp>>,
                ) -> Result<()> {
                let $this = self;
                $body
            }
        }
    );
}

Discover!(for [
    VarRef, IntLit, StrLit, StructLit, BooLit, FunCal, If, Block, Expr, VarLet, Stmt, Type
]);

Discover!(for FunDef(FunDef{name, ..}, ctx, scp) = {
    if scp.borrow().get(name).is_some() {
        return Ok(());
    }

    let name = name.clone().into_ast_span(ctx);
    let path = ctx.borrow_mut().mk_path(name);
    scp.borrow_mut().bind(&name, path);
    Ok(())
});

Discover!(for StructDef(StructDef{name, ..}, ctx, scp) = {
    let name = name.clone().into_ast_span(ctx);
    let path = ctx.borrow_mut().mk_path(name);
    scp.borrow_mut().bind(&name, path);
    Ok(())
});

Discover!(for TopLvl(toplvl, ctx, scp) = {
    match toplvl {
        TopLvl::FunDef(fd) => fd.discover(ctx, scp),
        TopLvl::StructDef(sd) => sd.discover(ctx, scp),
    }?;
    Ok(())
});

Discover!(for TopLvlDirective(tld, ctx, scp) = match tld {
    TopLvlDirective::InfixDef(id) => id.discover(ctx, scp)
});

Discover!(for InfixDef(InfixDef{name, info, ..}, ctx, scp) = {
    let path = {
        let mut scp = scp.borrow_mut();
        if let Some(path) = scp.get(name) {
            Rc::clone(path)
        } else {
            let name = name.clone().into_ast_span(ctx);
            let path = ctx.borrow_mut().mk_path(name);
            scp.bind(&name, Rc::clone(&path));
            path
        }
    };
    ctx.borrow_mut().insert_op_info(path, *info);
    Ok(())
});

Discover!(for Module(Module(toplvls, directives), ctx, scp) = {
    directives.iter()
        .map(|tld| tld.discover(ctx, scp))
        .collect::<Result<()>>()?;

    toplvls.iter()
        .map(|tl| tl.discover(ctx, scp))
        .collect::<Result<()>>()
});

fn bind_builtin_type_ident<'a, 'scp, 'sym>(
    ident: &'static str,
    ty: infer::TypeIdent<'a>,
    ctx: &mut ParseContext<'a, 'sym>,
    scp: &mut Scope<'a, 'scp>,
) {
    let path = ctx.mk_path_raw(ident);
    scp.bind_raw(ident, Rc::clone(&path));
    ctx.insert_type(path, infer::Type::Concrete(ty, vec![]));
}

fn bind_builtins<'a, 'scp, 'sym>(
    ctx: &RefCell<ParseContext<'a, 'sym>>,
    scp: &RefCell<Scope<'a, 'scp>>,
) {
    let ctx = &mut ctx.borrow_mut();
    let scp = &mut scp.borrow_mut();

    bind_builtin_type_ident("Int", infer::TypeIdent::Integer, ctx, scp);
    bind_builtin_type_ident("Str", infer::TypeIdent::String, ctx, scp);
    bind_builtin_type_ident("Bool", infer::TypeIdent::Boolean, ctx, scp);
    bind_builtin_type_ident("()", infer::TypeIdent::Unit, ctx, scp);
}

trait FromRawAst<'a, Raw>: Sized {
    fn from_raw_ast<'scp, 'sym>(
        raw: Raw,
        ctx: &RefCell<ParseContext<'a, 'sym>>,
        scp: &RefCell<Scope<'a, 'scp>>,
    ) -> Result<Self>;
}

macro_rules! FromRawAst {
    (@type $ty:path,   ) => ($ty);
    (@type $ty:path, Rc) => (Rc<$ty>);
    (for $o:ident($raw:pat, $ctx:ident, $scp:ident)$(: $ty:ident)?
     = $body:expr) => (
        impl<'a> FromRawAst<'a, $o<'a>>
        for FromRawAst!(@type ast::$o<'a>, $($ty)?) {
            fn from_raw_ast<'scp, 'sym>(
                $raw: $o<'a>,
                $ctx: &RefCell<ParseContext<'a, 'sym>>,
                $scp: &RefCell<Scope<'a, 'scp>>,
                ) -> Result<Self> {
                $body
            }
        }
    );
}

FromRawAst!(for VarRef(VarRef(i), ctx, scp) = {
    let scp = scp.borrow();
    let path = scp.try_get(&i, "Variable", &ctx.borrow())?;
    let span = i.into_ast_span(ctx);
    let ident = Ident::new(Rc::clone(path), span);

    Ok(ast::VarRef::new(span, ident, &mut ctx.borrow_mut()))
});

FromRawAst!(for IntLit(IntLit(span, val), ctx, _scp) =
    Ok(ast::IntLit::new(span.into_ast_span(ctx), val, &mut ctx.borrow_mut()))
);


FromRawAst!(for StrLit(StrLit(span, val), ctx, _scp) =
    Ok(ast::StrLit::new(span.into_ast_span(ctx), val, &mut ctx.borrow_mut()))
);

FromRawAst!(for BooLit(BooLit(span, val), ctx, _scp) =
    Ok(ast::BooLit::new(span.into_ast_span(ctx), val, &mut ctx.borrow_mut()))
);

FromRawAst!(for StructLit(StructLit{span, name, fields}, ctx, scp) = {
    let ident = scp.borrow().try_get_ident(name, "Struct", ctx)?;

    let fields = match fields {
        StructLitFields::Named(vec) => {
            let mut map = IndexMap::with_capacity(vec.len());
            for (name, expr) in vec.into_iter() {
                let name = name.into_ast_span(ctx);
                map.insert(*name.fragment(),
                            (name, from_raw_ast!(Expr, expr, ctx, scp)?));
            }
            ast::StructLitFields::Named(map)
        },
        StructLitFields::UnNamed(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| from_raw_ast!(Expr, e, ctx, scp))
                .collect::<Result<Vec<_>>>()?;
            ast::StructLitFields::UnNamed(exprs)
        }
    };

    Ok(ast::StructLit::new(span.into_ast_span(ctx), ident, fields, &mut ctx.borrow_mut()))
});

FromRawAst!(for If(If{span, clauses, otherwise}, ctx, scp) = {
    let span = span.into_ast_span(ctx);

    let clauses = clauses.into_iter()
        .map(|(c, e)| Ok((from_raw_ast!(Expr, c, ctx, scp)?,
                          from_raw_ast!(Expr, e, ctx, scp)?)))
        .collect::<Result<_>>()?;

    let otherwise = otherwise
        .map(|e| Ok(Box::new(from_raw_ast!(Expr, *e, ctx, scp)?)) as Result<Box<_>>)
        .transpose()?;

    Ok(ast::If::new(span, clauses, otherwise, &mut ctx.borrow_mut()))
});

FromRawAst!(for FunCal(FunCal{span, name, args}, ctx, scp) = {
    let span = span.into_ast_span(ctx);
    let ident = scp.borrow().try_get_ident(name, "Function", ctx)?;
    let args = args.into_iter()
        .map(|a| from_raw_ast!(Expr, a, ctx, scp))
        .collect::<Result<_>>()?;

    Ok(ast::FunCal::new(span, ident, args, &mut ctx.borrow_mut()))
});

FromRawAst!(for Block(Block{span, body, ret}, ctx, scp) = {
    let span = span.into_ast_span(ctx);

    let scp = scp.borrow();
    let body_scp = &RefCell::new(scp.subscope());
    let body = body.into_iter()
        .map(|s| from_raw_ast!(Stmt, s, ctx, body_scp))
        .collect::<Result<_>>()?;
    let ret = ret
        .map(|r| Ok(Box::new(from_raw_ast!(Expr, *r, ctx, body_scp)?))
            as Result<Box<_>>)
        .transpose()?;

    Ok(ast::Block::new(span, body, ret, &mut ctx.borrow_mut()))
});

FromRawAst!(for Expr(expr, ctx, scp) = Ok(match expr {
    Expr::Block(b)     => ast::Expr::Block(from_raw_ast!(Block, b, ctx, scp)?),
    Expr::If(i)        => ast::Expr::If(from_raw_ast!(If, i, ctx, scp)?),
    Expr::FunCal(f)    => ast::Expr::FunCal(from_raw_ast!(FunCal, f, ctx, scp)?),
    Expr::StructLit(s) => ast::Expr::StructLit(from_raw_ast!(StructLit, s, ctx, scp)?),
    Expr::StrLit(s)    => ast::Expr::StrLit(from_raw_ast!(StrLit, s, ctx, scp)?),
    Expr::BooLit(s)    => ast::Expr::BooLit(from_raw_ast!(BooLit, s, ctx, scp)?),
    Expr::IntLit(i)    => ast::Expr::IntLit(from_raw_ast!(IntLit, i, ctx, scp)?),
    Expr::VarRef(v)    => ast::Expr::VarRef(from_raw_ast!(VarRef, v, ctx, scp)?),
    Expr::OpChain(first, rest) => {
        let first = from_raw_ast!(Expr, *first, ctx, scp)?;
        let rest = rest.into_iter().map(|(op, e)| {
            let ident = scp.borrow().try_get_ident(op, "Operator", ctx)?;
            let opinfo = ctx.borrow().get_op_info(&ident.path)?;
            Ok((
                (ident, opinfo),
                from_raw_ast!(Expr, e, ctx, scp)?
            ))
        }).collect::<Result<Vec<_>>>()?.into();
        OpChain::new(first, rest).fold(ctx)
    },
}));

FromRawAst!(for VarLet(VarLet{span, var, val}, ctx, scp) = {
    let span = span.into_ast_span(ctx);
    let var = var.into_ast_span(ctx);
    let val = from_raw_ast!(Expr, val, ctx, scp)?;

    let path = ctx.borrow_mut().mk_path(var);
    let ident = Ident::new(Rc::clone(&path), var);

    scp.borrow_mut().bind(&var, Rc::clone(&path));

    Ok(ast::VarLet::new(span, ident, val, &mut ctx.borrow_mut()))
});

FromRawAst!(for Stmt(stmt, ctx, scp) = Ok(match stmt {
    Stmt::Expr(e)    => ast::Stmt::Expr(from_raw_ast!(Expr, e, ctx, scp)?),
    Stmt::VarLet(vl) => ast::Stmt::VarLet(from_raw_ast!(VarLet, vl, ctx, scp)?),
}));

FromRawAst!(for FunDef(FunDef{span, name, argnames, body}, ctx, scp): Rc = {
    let (argnames, body) = {
        let scp = scp.borrow();
        let mut body_scp = scp.subscope();
        let argnames = argnames
            .into_iter()
            .map(|a| {
                let a = a.into_ast_span(ctx);
                let mut ctx = ctx.borrow_mut();
                let path = ctx.mk_path(a);

                body_scp.bind(&a, Rc::clone(&path));

                Ident::new(path, a)
            })
        .collect();
        let body_scp = &RefCell::new(body_scp);

        // TODO: put this in scp instead of ctx
        ctx.borrow_mut().push_path(name.clone());
        let body = from_raw_ast!(Expr, body, ctx, body_scp)?;
        ctx.borrow_mut().pop_path();

        (argnames, body)
    };

    let span = span.into_ast_span(ctx);

    let path = Rc::clone(scp.borrow().try_get(&name, "Function", &ctx.borrow())?);
    let name = name.into_ast_span(ctx);
    let ident = Ident::new(Rc::clone(&path), name);

    let mut ctx = ctx.borrow_mut();

    let fundef =
        Rc::new(ast::FunDef::new(span, ident, argnames, body, &mut ctx));

    ctx.insert_fundef(path, Rc::clone(&fundef));

    Ok(fundef)
});

FromRawAst!(for Type(Type{span, name, args}, ctx, scp) = {
    let span = span.into_ast_span(ctx);
    let ident = scp.borrow().try_get_ident(name, "Type", ctx)?;

    let args = args
        .into_iter()
        .map(|a| Ok(from_raw_ast!(Type, a, ctx, scp)?))
        .collect::<Result<Vec<_>>>()?;

    let mut ctx = ctx.borrow_mut();

    Ok(ast::Type::new(span, ident, args, &mut ctx))
});

FromRawAst!(for StructDef(StructDef{span, name, field_names, field_types}, ctx, scp) = {
    let span = span.into_ast_span(ctx);
    let path = Rc::clone(scp.borrow().try_get(&name, "Struct", &ctx.borrow())?);
    let name = name.into_ast_span(ctx);
    let ident = Ident::new(Rc::clone(&path), name);

    let field_names: Option<Vec<Ident<'a>>> = field_names
        .map(|fns| fns.into_iter().map(|name|{
            let name = name.into_ast_span(ctx);
            // FIXME: path here should be a subpath of path with last
            // component being field name.
            Ident::new(Rc::clone(&path), name)
        }).collect());

    let field_types = field_types
        .into_iter()
        .map(|ty| Ok(from_raw_ast!(Type, ty, ctx, scp)?))
        .collect::<Result<Vec<_>>>()?;

    let mut ctx = ctx.borrow_mut();

    let record = infer::Type::Record(
        infer::TypeIdent::User(Rc::clone(&path)),
        if let Some(field_names) = field_names.as_ref() {
            field_names.iter()
                .map(|n|infer::RowIndex::Label(n.span.fragment()))
                .zip(field_types.iter().map(|ty| ty.to_type(&mut ctx)))
                .map(|(n, t)|Ok((n, t?)))
                .collect::<Result<IndexMap<_, _>>>()?
        } else {
            (0..)
                .map(|i|infer::RowIndex::Index(i))
                .zip(field_types.iter().map(|ty| ty.to_type(&mut ctx)))
                .map(|(n, t)|Ok((n, t?)))
                .collect::<Result<IndexMap<_, _>>>()?
        }
    );
    ctx.insert_type(path, infer::Type::Scheme(vec![], Box::new(record)));

    Ok(ast::StructDef::new(span, ident, field_names, field_types, &mut ctx))
});

FromRawAst!(for TopLvl(toplvl, ctx, scp) = Ok(match toplvl {
    TopLvl::FunDef(fd) =>
        ast::TopLvl::FunDef(from_raw_ast!(Rc<FunDef>, fd, ctx, scp)?),
    TopLvl::StructDef(sd) =>
        ast::TopLvl::StructDef(from_raw_ast!(StructDef, sd, ctx, scp)?),
}));

FromRawAst!(for Module(Module(toplvls, _directives), ctx, scp) = {
    let toplvls = toplvls.into_iter()
        .map(|tl| from_raw_ast!(TopLvl, tl, ctx, scp))
        .collect::<Result<_>>()?;

    Ok(ast::Module { toplvls })
});

fn align_msg(alignment: usize, msg: &str) -> String {
    let mut lines = msg.lines();
    let mut r = lines.next().unwrap().to_string();
    for line in lines {
        r.push_str("\n");
        for _ in 0..alignment { r.push(' '); }
        r.push_str(line);
    }
    r
}

pub fn format_at_pos<'a, T>(
    span: &LocatedSpan<&'a str, T>,
    prefix: &str,
    alignment: usize,
    msg: &str,
    file: &'a File,
    underline: bool,
) -> Result<String> {
    let linum = span.location_line() as usize;
    let colnum = span.get_utf8_column();
    let line = file.prog.lines().nth(linum - 1).unwrap();

    let linecount = span.fragment().lines().count();

    let mut buf = String::with_capacity(500);
    {
        // Print message
        write!(&mut buf, "{}:{}:{}: ", file.path, linum, colnum)?;
        let aligned_msg = align_msg(buf.chars().count() + alignment, msg);
        write!(&mut buf, "{}{}\n", prefix, aligned_msg)?;

        // Print code preview
        if linecount == 1 {
            write!(&mut buf, "| {}\n", line)?;
            let underline = if underline {
                format!("{:^<1$}", "^", span.fragment().len())
            } else {
                "^".to_string()
            };
            write!(
                &mut buf,
                "| {: <1$}{2}\n",
                "",
                colnum - 1,
                Paint::green(underline).bold()
            )?;
        } else {
            let arrow =  Paint::green(">").bold();

            if linecount <= 3 {
                let lines_rest = file.prog.lines()
                    .skip(linum)
                    .take(linecount - 1);

                write!(&mut buf, "{} {}\n", arrow, line)?;
                for line in lines_rest {
                    write!(&mut buf, "{} {}\n", arrow, line)?;
                }
            } else {
                let last_line
                    = file.prog.lines().nth(linum + linecount - 2).unwrap();

                write!(&mut buf, "{} {}\n", arrow, line)?;
                write!(&mut buf, "{}",
                       Paint::green(format!("+ {} +\n", linecount - 2)
                       ).bold())?;
                write!(&mut buf, "{} {}\n", arrow, last_line)?;
            }
        }
        Ok(()) as Result<()>
    }
    .context("Failed to format msg at pos")?;

    Ok(buf)
}

pub fn run_parser<'a, T: Parsable<'a>>(
    file: &'a File
) -> Result<(T, Symbols<'a>, infer::TvarGenerator)> {

    let tvar_gen = infer::TvarGenerator::new();
    let mut symbols = Symbols::new();
    let tracker = ErrorTrackerRef(Rc::new(RefCell::new(ErrorTracker::new())));
    let ctx = RefCell::new(ParseContext::new(file, &mut symbols, tvar_gen));
    let scp = RefCell::new(Scope::new());

    bind_builtins(&ctx, &scp);

    match T::parse(
        Span::new_extra(&file.prog, tracker.clone()), &ctx
    ).map(|(_i, tree)| {
        tree.discover(&ctx, &scp)
            .context("Failed to discover globals")?;
        T::from_raw_ast(tree, &ctx, &scp)
            .context("Failed to build AST")
    }) {

        Err(e) => {
            let errmsg = match e {
                Err::Error(_) | Err::Failure(_) => {
                    let tracker = tracker.0.borrow();
                    let span = &tracker.errors.first().unwrap().0;
                    let mut toks = tracker
                        .errors
                        .iter()
                        .map(|(_, t)| &**t)
                        .collect::<HashSet<&str>>()
                        .into_iter()
                        .collect::<Vec<&str>>();
                    toks.sort_unstable();
                    let toks = toks.join(", ");

                    Error::msg(format_at_pos(
                        span,
                        &Paint::red("error: ").bold().to_string(),
                        7,
                        &format!("expected one of: {}", toks),
                        file,
                        false,
                    )?)
                }
                Err::Incomplete(_) => {
                    anyhow!("{}::: parser error: incomplete input", file.path)
                }
            };
            Err(errmsg)
        }
        Ok(r) => Ok({
            let tvs = ctx.into_inner().tvar_gen;
            (r?, symbols, tvs)
        }),
    }
}
