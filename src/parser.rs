use nom::{
    call, char, complete, delimited, do_parse, escaped_transform, many0,
    flat_map, map, named, none_of, opt, separated_list, tag, take,
    take_while_m_n, take_while1, terminated, Err, IResult, parse_to,
};
use nom_locate::LocatedSpan;
use indexmap::IndexMap;
use derive_more::{ DebugCustom, Display };
use anyhow::{anyhow, Context, Error, Result};
use yansi::Paint;

use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Write;
use std::rc::Rc;

use crate::ast;
use crate::ast::{ Ident, AstNodeID };
use ast::Symbols;

#[derive(DebugCustom)]
#[debug(fmt = "File({:?})", path)]
pub struct File {
    pub prog: String,
    pub path: String,
}

pub type Span<'a> = LocatedSpan<&'a str, ErrorTrackerRef<'a>>;

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
            &format!("{} {}", Paint::red("error:").bold(), msg),
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
            &format!("{} {}", Paint::yellow("note:").bold(), msg),
            ctx.file,
            underline,
        )
    }
}

#[derive(Display, Debug, Clone, Hash, Eq, PartialEq)]
#[display(fmt = "{}.{}", "path.join(\":\")", id)]
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


#[derive(Debug)]
pub struct ParseContext<'a, 'sym> {
    next_path_id: usize,
    next_node_id: usize,
    current_path: Path<'a>,
    pub file: &'a File,
    pub symbols: &'sym mut Symbols<'a>,
}

impl<'a, 'sym> ParseContext<'a, 'sym> {
    pub fn new(file: &'a File, symbols: &'sym mut Symbols<'a>) -> Self {
        Self {
            current_path: Path::empty_with_id(0),
            next_node_id: 0,
            next_path_id: 1,
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
        let mut path = self.current_path.clone();
        path.push(part.fragment());
        path.make_unique(self);
        Rc::new(path)
    }
    pub fn insert_fundef(&mut self, path: Rc<Path<'a>>, node: Rc<ast::FunDef<'a>>) {
        self.symbols.fundefs.insert(path, node);
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
    ($i:expr, Rc<$ty:ident>, $ctx:expr) => {
        <Rc<ast::$ty> as Parsable>::parse($i, $ctx)
    };
    ($i:expr, $ty:ident, $ctx:expr) => {
        <ast::$ty as Parsable>::parse($i, $ctx)
    };
}

macro_rules! from_raw_ast {
    (Rc<$ty:ident>, $raw:expr, $ctx:expr, $scp:expr) => {
        <Rc<ast::$ty> as Parsable>::from_raw_ast($raw, $ctx, $scp)
    };
    ($ty:ident, $raw:expr, $ctx:expr, $scp:expr) => {
        <ast::$ty as Parsable>::from_raw_ast($raw, $ctx, $scp)
    };
}

macro_rules! discover_globals {
    (Rc<$ty:ident>, $raw:expr, $ctx:expr, $scp:expr) => {
        <Rc<ast::$ty> as Parsable>::discover_globals($raw, $ctx, $scp)
    };
    ($ty:ident, $raw:expr, $ctx:expr, $scp:expr) => {
        <ast::$ty as Parsable>::discover_globals($raw, $ctx, $scp)
    };
}

macro_rules! range_span {
    ($a:expr, $b:expr) => {{
        let a_ofs = $a.location_offset();
        let b_ofs = $b.location_offset();
        take!($a, b_ofs - a_ofs)
    }};
}

macro_rules! get_span {
    ($i:expr, $parser:ident!($($args:tt)*)) => ({
        let (s, r) = $parser!($i.clone(), $($args)*)?;
        let (_, range) = range_span!($i, s)?;
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
        delimited!($i, tok_tag!("("), $parser!($($args)*), tok_tag!(")"))
    };
}

macro_rules! braces {
    ($i:expr, $parser:ident!($($args:tt)*)) => {
        delimited!($i, tok_tag!("{"), $parser!($($args)*), tok_tag!("}"))
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
    (@parser $parser:ident!($($args:tt)*) => $map:expr) =>
        (|i| map!(i, $parser!($($args)*), $map));
    (@parser $parser:ident!($($args:tt)*)) =>
        (|i| $parser!(i, $($args)*));

    ($i:expr, $parser:ident!($($args:tt)*) $(=> { $map:expr })?) => (
        alt!(@parser $parser!($($args)*) $(=> $map)?)($i)
    );
    ($i:expr, $($parser:ident!($($args:tt)*) $(=> { $map:expr })?)|+) => (
        nom::branch::alt(($(alt!(@parser $parser!($($args)*) $(=> $map)?)),+))($i)
    );
}

pub trait Parsable<'a> : Sized {
    type Raw;
    fn parse<'sym>(i: Span<'a>, ctx: &RefCell<ParseContext<'a, 'sym>>)
        -> IResult<Span<'a>, Self::Raw>;

    fn from_raw_ast<'scp, 'sym>(
        raw: Self::Raw,
        ctx: &RefCell<ParseContext<'a, 'sym>>,
        scp: &RefCell<Scope<'a, 'scp>>,
    ) -> Result<Self>;

    fn discover_globals<'scp, 'sym>(
        raw: &Self::Raw,
        ctx: &RefCell<ParseContext<'a, 'sym>>,
        scp: &RefCell<Scope<'a, 'scp>>,
    ) -> Result<()>;
}
macro_rules! Parser {
    (@self $ty:path,   ) => ($ty);
    (@self $ty:path, Rc) => (Rc<$ty>);
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

                fn from_raw_ast<'scp, 'sym>(
                    raw: Self::Raw,
                    ctx: &RefCell<ParseContext<'a, 'sym>>,
                    scp: &RefCell<Scope<'a, 'scp>>,
                ) -> Result<Self> {
                    <Self as FromRawAst<'a, Self::Raw>>
                        ::from_raw_ast(raw, ctx, scp)
                }

                fn discover_globals<'scp, 'sym>(
                    raw: &Self::Raw,
                    ctx: &RefCell<ParseContext<'a, 'sym>>,
                    scp: &RefCell<Scope<'a, 'scp>>,
                ) -> Result<()> {
                    <Self as DiscoverGlobals<'a, Self::Raw>>
                        ::discover_globals(raw, ctx, scp)
                }
            }
        );
}

named!(ident(Span) -> Span,
    tok!(describe!("ident",
        take_while1!(|c: char| c == '_' || c.is_alphanumeric()))));

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
|((body, ret), span)| Block {span, body, ret}
));

pub enum Expr<'a>{
    Block(Block<'a>), 
    FunCal(FunCal<'a>),
    StrLit(StrLit<'a>),
    IntLit(IntLit<'a>),
    VarRef(VarRef<'a>),
}
Parser!(for Expr(ctx) = alt!(
        parse!(Block,  ctx) => { |b| Expr::Block(b) }
      | parse!(FunCal, ctx) => { |f| Expr::FunCal(f) }
      | parse!(StrLit, ctx) => { |s| Expr::StrLit(s) }
      | parse!(IntLit, ctx) => { |i| Expr::IntLit(i) }
      | parse!(VarRef, ctx) => { |v| Expr::VarRef(v) }));

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

pub enum TopLvl<'a>{
    FunDef(FunDef<'a>),
}
Parser!(for TopLvl(ctx) =
    terminated!(
        alt!(
            parse!(Rc<FunDef>, ctx) => { |fd| TopLvl::FunDef(fd) }
        ), 
        tok_tag!(";")));

pub struct Module<'a>(Vec<TopLvl<'a>>);
Parser!(for Module(ctx) = do_parse!(
    toplvls: many0!(complete!(parse!(TopLvl, ctx))) >>
    tok!(eof!()) >>
    (Module(toplvls))
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
        ctx: &ParseContext<'a, 's>,
    ) -> Result<&Rc<Path<'a>>> {
        self.get(id).with_context(|| {
            id.format_err_at_pos(
                &format!("`{}` not found in scope", id),
                true,
                ctx,
            )
            .unwrap()
        })
    }

    fn bind<E>(&mut self, id: &LocatedSpan<&'a str, E>, path: Rc<Path<'a>>) {
        self.scope.insert(id.fragment(), path);
    }
}

trait DiscoverGlobals<'a, Raw> {
    fn discover_globals<'scp, 'sym>(
        _raw: &Raw,
        _ctx: &RefCell<ParseContext<'a, 'sym>>,
        _scp: &RefCell<Scope<'a, 'scp>>,
    ) -> Result<()> { Ok(()) }
}

macro_rules! DiscoverGlobals {
    (@type $ty:path,   ) => ($ty);
    (@type $ty:path, Rc) => (Rc<$ty>);
    (for [$($o:ident$(: $ty:ident)?),*]) => (
        $(
            impl<'a> DiscoverGlobals<'a, $o<'a>>
            for DiscoverGlobals!(@type ast::$o<'a>, $($ty)?) {}
        )*
    );
    (for $o:ident($raw:pat, $ctx:ident, $scp:ident)$(: $ty:ident)?
     = $body:expr) => (
        impl<'a> DiscoverGlobals<'a, $o<'a>>
        for DiscoverGlobals!(@type ast::$o<'a>, $($ty)?) {
            fn discover_globals<'scp, 'sym>(
                $raw: &$o<'a>,
                $ctx: &RefCell<ParseContext<'a, 'sym>>,
                $scp: &RefCell<Scope<'a, 'scp>>,
                ) -> Result<()> {
                $body
            }
        }
    );
}

DiscoverGlobals!(for [
    VarRef, IntLit, StrLit, FunCal, Block, Expr, VarLet, Stmt
]);

DiscoverGlobals!(for FunDef(FunDef{name, ..}, ctx, scp): Rc = {
    let name = name.clone().into_ast_span(ctx);
    let path = ctx.borrow_mut().mk_path(name);
    scp.borrow_mut().bind(&name, Rc::clone(&path));
    Ok(())
});

DiscoverGlobals!(for TopLvl(toplvl, ctx, scp) = {
    match toplvl {
        TopLvl::FunDef(fd) => discover_globals!(Rc<FunDef>, fd, ctx, scp),
    }?;
    Ok(())
});

DiscoverGlobals!(for Module(Module(toplvls), ctx, scp) =
    toplvls.iter()
        .map(|tl| discover_globals!(TopLvl, tl, ctx, scp))
        .collect::<Result<()>>()
);

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
    let path = scp.try_get(&i, &ctx.borrow())?;
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

FromRawAst!(for FunCal(FunCal{span, name, args}, ctx, scp) = {
    let span = span.into_ast_span(ctx);
    let ident = {
        let scp = scp.borrow();
        let path = scp.try_get(&name, &ctx.borrow())?;
        Ident::new(Rc::clone(path), name.into_ast_span(ctx))
    };
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
    Expr::Block(b)  => ast::Expr::Block(from_raw_ast!(Block, b, ctx, scp)?),
    Expr::FunCal(f) => ast::Expr::FunCal(from_raw_ast!(FunCal, f, ctx, scp)?),
    Expr::StrLit(s) => ast::Expr::StrLit(from_raw_ast!(StrLit, s, ctx, scp)?),
    Expr::IntLit(i) => ast::Expr::IntLit(from_raw_ast!(IntLit, i, ctx, scp)?),
    Expr::VarRef(v) => ast::Expr::VarRef(from_raw_ast!(VarRef, v, ctx, scp)?),
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
    let path = Rc::clone(scp.borrow().try_get(&name, &ctx.borrow())?);
    let name = name.into_ast_span(ctx);
    let ident = Ident::new(Rc::clone(&path), name);

    let mut ctx = ctx.borrow_mut();

    let fundef =
        Rc::new(ast::FunDef::new(span, ident, argnames, body, &mut ctx));

    scp.borrow_mut().bind(&name, Rc::clone(&path));
        ctx.insert_fundef(path, Rc::clone(&fundef));

    Ok(fundef)
});

FromRawAst!(for TopLvl(toplvl, ctx, scp) = Ok(match toplvl {
    TopLvl::FunDef(fd) => 
        ast::TopLvl::FunDef(from_raw_ast!(Rc<FunDef>, fd, ctx, scp)?),
}));

FromRawAst!(for Module(Module(toplvls), ctx, scp) = {
    let toplvls = toplvls.into_iter()
        .map(|tl| from_raw_ast!(TopLvl, tl, ctx, scp))
        .collect::<Result<_>>()?;

    Ok(ast::Module { toplvls })
});


pub fn format_at_pos<'a, T>(
    span: &LocatedSpan<&'a str, T>,
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
        write!(&mut buf, "{}:{}:{}: {}\n", file.path, linum, colnum, msg)?;

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

pub fn run_parser<'a, T: Parsable<'a>>(file: &'a File) -> Result<(T, Symbols<'a>)> {
    let mut symbols = Symbols::new();
    let tracker = ErrorTrackerRef(Rc::new(RefCell::new(ErrorTracker::new())));
    let ctx = RefCell::new(ParseContext::new(file, &mut symbols));
    let scp = RefCell::new(Scope::new());

    match T::parse(
        Span::new_extra(&file.prog, tracker.clone()), &ctx
    ).map(|(_i, tree)| {
        T::discover_globals(&tree, &ctx, &scp)
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
                        &format!(
                            "{} expected one of: {}",
                            Paint::red("error:").bold(),
                            toks
                        ),
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
        Ok(r) => Ok((r?, symbols)),
    }
}
