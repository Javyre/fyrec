use crate::parser::{ ParseContext, File, Path };
use enum_dispatch::enum_dispatch;

use indexmap::IndexMap;
use nom_locate::LocatedSpan;
use std::{fmt::Debug, rc::Rc};

pub type Span<'a> = LocatedSpan<&'a str, &'a File>;

pub struct Symbols<'a> {
    pub fundefs: IndexMap<Rc<Path<'a>>, Rc<FunDef<'a>>>,
}

#[derive(Debug, Clone)]
pub struct Ident<'a> {
    pub span: Span<'a>,
    pub path: Rc<Path<'a>>,
}

#[derive(Debug)]
pub struct VarLet<'a> {
    span: Span<'a>,
    pub var: Ident<'a>,
    pub val: Expr<'a>,
    id: AstNodeID,
}

#[enum_dispatch]
#[derive(Debug)]
pub enum Stmt<'a> {
    Expr(Expr<'a>),
    VarLet(VarLet<'a>),
}

#[derive(Debug)]
pub struct VarRef<'a> {
    span: Span<'a>,
    pub name: Ident<'a>,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct IntLit<'a> {
    pub span: Span<'a>,
    pub val: i32,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct StrLit<'a> {
    pub span: Span<'a>,
    pub val: String,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct BooLit<'a> {
    pub span: Span<'a>,
    pub val: bool,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct If<'a> {
    span: Span<'a>,
    pub clauses: Vec<(Expr<'a>, Expr<'a>)>,
    pub otherwise: Option<Box<Expr<'a>>>,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct FunCal<'a> {
    span: Span<'a>,
    pub name: Ident<'a>,
    pub args: Vec<Expr<'a>>,
    id: AstNodeID,
}
#[derive(Debug)]
pub struct Block<'a> {
    pub span: Span<'a>,
    pub body: Vec<Stmt<'a>>,
    pub ret: Option<Box<Expr<'a>>>,
    id: AstNodeID,
}

#[enum_dispatch]
#[derive(Debug)]
pub enum Expr<'a> {
    VarRef(VarRef<'a>),
    IntLit(IntLit<'a>),
    StrLit(StrLit<'a>),
    BooLit(BooLit<'a>),
    If(If<'a>),
    FunCal(FunCal<'a>),
    Block(Block<'a>),
}

#[derive(Debug)]
pub struct FunDef<'a> {
    span: Span<'a>,
    pub name: Ident<'a>,
    pub argnames: Vec<Ident<'a>>,
    pub body: Expr<'a>,
    id: AstNodeID,
}

#[derive(Debug)]
pub struct Type<'a> {
    span: Span<'a>,
    pub name: Ident<'a>,
    pub args: Vec<Type<'a>>,
    id: AstNodeID,
}

#[derive(Debug)]
pub struct StructDef<'a> {
    span: Span<'a>,
    pub name: Ident<'a>,
    pub field_names: Option<Vec<Ident<'a>>>,
    pub field_types: Vec<Type<'a>>,
    id: AstNodeID,
}

#[enum_dispatch]
#[derive(Debug)]
pub enum TopLvl<'a> {
    FunDef(Rc<FunDef<'a>>),
    StructDef(StructDef<'a>),
}

#[derive(Debug)]
pub struct Module<'a> {
    pub toplvls: Vec<TopLvl<'a>>,
}

#[enum_dispatch]
pub enum AstNode<'a> {
    Expr(Expr<'a>),
    Stmt(Stmt<'a>),
    TopLvl(TopLvl<'a>),
}

// TODO: stop needing to use counter IDs. Counters like AstNodeID are unreliable
//       and could potentially be replaced with Rc<T>
pub type AstNodeID = usize;

#[enum_dispatch(Stmt)]
#[enum_dispatch(Expr)]
#[enum_dispatch(TopLvl)]
#[enum_dispatch(AstNode)]
pub trait IAstNode<'a> {
    fn get_id(&self) -> AstNodeID;
    fn span(&self) -> Span<'a>;
}

#[enum_dispatch(TopLvl)]
pub trait ITopLvl {}

#[enum_dispatch(Expr)]
pub trait IExpr {}

impl<'a> Debug for Symbols<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in self.fundefs.iter() {
            writeln!(f, "{:?}: {},", k, v.get_id())?;
        }
        Ok(())
    }
}

impl<'a> std::hash::Hash for Ident<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.span.fragment().hash(state);
    }
}

impl<'a> std::cmp::Eq for Ident<'a> {}
impl<'a> std::cmp::PartialEq for Ident<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.span.fragment() == other.span.fragment()
    }
}

impl<'a> Symbols<'a> {
    pub fn new() -> Self {
        Self {
            fundefs: IndexMap::new(),
        }
    }
}

macro_rules! IAstNode {
    (for Rc<$ty:ident> as $this:ident {get_id: $id:expr, span: $span:expr}) => {
        impl<'a> IAstNode<'a> for Rc<$ty<'a>> {
            fn get_id(&self) -> AstNodeID {
                let $this = self;
                $id
            }
            fn span(&self) -> Span<'a> {
                let $this = self;
                $span
            }
        }
    };
    (for $ty:ident as $this:ident {get_id: $id:expr, span: $span:expr}) => {
        impl<'a> IAstNode<'a> for $ty<'a> {
            fn get_id(&self) -> AstNodeID {
                let $this = self;
                $id
            }
            fn span(&self) -> Span<'a> {
                let $this = self;
                $span
            }
        }
    };
}

IAstNode! { for VarLet as this { get_id: this.id, span: this.span } }
// IAstNode! { for Ident  as this { get_id: this.id, span: this.span } }
IAstNode! { for VarRef as this { get_id: this.id, span: this.span } }
IAstNode! { for IntLit as this { get_id: this.id, span: this.span } }
IAstNode! { for StrLit as this { get_id: this.id, span: this.span } }
IAstNode! { for BooLit as this { get_id: this.id, span: this.span } }
IAstNode! { for If as this { get_id: this.id, span: this.span } }
IAstNode! { for FunCal as this { get_id: this.id, span: this.span } }
IAstNode! { for Block  as this { get_id: this.id, span: this.span } }
IAstNode! { for Rc<FunDef> as this { get_id: this.id, span: this.span } }
// IAstNode! { for FunDef as this { get_id: this.id, span: this.span } }
IAstNode! { for Type as this { get_id: this.id, span: this.span } }
IAstNode! { for StructDef as this { get_id: this.id, span: this.span } }

impl<'a> std::fmt::Display for Ident<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.span)
    }
}

impl<'a> Ident<'a> {
    pub fn new(path: Rc<Path<'a>>, name: Span<'a>) -> Self {
        Self {
            path,
            span: name,
        }
    }
}

impl<'a> VarLet<'a> {
    pub fn new(
        span: Span<'a>,
        var: Ident<'a>,
        val: Expr<'a>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            var,
            val,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> VarRef<'a> {
    pub fn new(span: Span<'a>, name: Ident<'a>, ctx: &mut ParseContext) -> Self {
        Self {
            span,
            name,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> IntLit<'a> {
    pub fn new(span: Span<'a>, val: i32, ctx: &mut ParseContext) -> Self {
        Self {
            span,
            val,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> StrLit<'a> {
    pub fn new(span: Span<'a>, val: String, ctx: &mut ParseContext) -> Self {
        Self {
            span,
            val,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> BooLit<'a> {
    pub fn new(span: Span<'a>, val: bool, ctx: &mut ParseContext) -> Self {
        Self {
            span,
            val,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> If<'a> {
    pub fn new(
        span: Span<'a>,
        clauses: Vec<(Expr<'a>, Expr<'a>)>,
        otherwise: Option<Box<Expr<'a>>>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            clauses,
            otherwise,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> FunCal<'a> {
    pub fn new(
        span: Span<'a>,
        name: Ident<'a>,
        args: Vec<Expr<'a>>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            name,
            args,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> Block<'a> {
    pub fn new(
        span: Span<'a>,
        body: Vec<Stmt<'a>>,
        ret: Option<Box<Expr<'a>>>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            body,
            ret,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> FunDef<'a> {
    pub fn new(
        span: Span<'a>,
        name: Ident<'a>,
        argnames: Vec<Ident<'a>>,
        body: Expr<'a>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            name,
            argnames,
            body,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> Type<'a> {
    pub fn new(
        span: Span<'a>,
        name: Ident<'a>,
        args: Vec<Type<'a>>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            name,
            args,
            id: ctx.gen_id(),
        }
    }
}

impl<'a> StructDef<'a> {
    pub fn new(
        span: Span<'a>,
        name: Ident<'a>,
        field_names: Option<Vec<Ident<'a>>>,
        field_types: Vec<Type<'a>>,
        ctx: &mut ParseContext,
    ) -> Self {
        Self {
            span,
            name,
            field_names,
            field_types,
            id: ctx.gen_id(),
        }
    }
}
