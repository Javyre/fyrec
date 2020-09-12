use crate::ast::*;
use crate::graph::*;
use crate::parser::{format_at_pos, Path};
use enum_dispatch::enum_dispatch;
use yansi::Paint;

use std::rc::Rc;
use std::fmt;

use indexmap::{IndexMap, IndexSet, indexmap, indexset};
use anyhow::{Context, Result, Error, bail};
use derive_more::{ Display, DebugCustom };

impl<'a> Expr<'a> {
    fn get_fun_calls(&self) -> IndexSet<&Rc<Path<'a>>> {
        match self {
            Expr::FunCal(fc) => indexset![&fc.name.path],
            Expr::Block(bl) => {
                let mut r: IndexSet<&Rc<Path>>
                    = bl.body.iter().flat_map(|s| match s {
                    Stmt::Expr(e) => e.get_fun_calls(),
                    Stmt::VarLet(vl) => vl.val.get_fun_calls(),
                }).collect();
                if let Some(ret) = &bl.ret {
                    r.extend(ret.get_fun_calls().into_iter());
                }
                r
            },
            _ => indexset![],
        }
    }
}

impl<'a> IGraphNode<Rc<Path<'a>>> for Rc<FunDef<'a>> {
    fn get_id(&self) -> Rc<Path<'a>> {
        Rc::clone(&self.name.path)
    }
    fn get_deps(&self) -> IndexSet<&Rc<Path<'a>>> {
        self.body.get_fun_calls()
    }
}

impl<'a> IGraphCtx<Rc<Path<'a>>, Rc<FunDef<'a>>, Error> for Symbols<'a> {
    fn get_node(&self, id: &Rc<Path<'a>>) -> Result<&Rc<FunDef<'a>>> {
        self.fundefs.get(id)
            .with_context(|| format!("`{}' is not a function", id))
    }
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
#[display(fmt = "T{}", "self.0")]
pub struct TypeVar(usize);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeIdent<'a> {
    User(Ident<'a>),
    Function,
    Integer,
    String,
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type<'a> {
    Concrete(TypeIdent<'a>, Vec<Type<'a>>),
    Scheme(Vec<TypeVar>, Box<Type<'a>>),
    Variable(TypeVar),
}

#[derive(Debug, Clone)]
pub enum ConstraintCtx<'a> {
    FunCal {
        fun: Rc<Path<'a>>,
    },
    FunCalArg {
        fun: Rc<Path<'a>>,
        n: usize,
    },
}

impl<'a> ConstraintCtx<'a> {
    fn context(&self) -> String {
        match self {
            ConstraintCtx::FunCal{ fun } => {
                format!("in call to {}", fun)
            },
            ConstraintCtx::FunCalArg{ fun, n } => {
                format!("in param {} in call to {}", n+1, fun)
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constraint<'a> {
    Eq {
        a: Type<'a>,
        b: Type<'a>,
        span: Span<'a>,
        ctx: Option<Rc<ConstraintCtx<'a>>>,
    },

    // For re-fetching type info for nodes once inference is done
    NodeType {
        node: AstNodeID,
        ty: Type<'a>,
        span: Span<'a>,
    },
}

impl<'a> Type<'a> {
    fn free_vars_impl(&self, set: &mut IndexSet<TypeVar>) {
        match self {
            Self::Concrete(_id, args) => {
                for arg in args {
                    arg.free_vars_impl(set);
                }
            },
            // NOTE: assuming schemes are created always with fresh quantifier
            // variables; meaning that quantifier vars cannot possibly be
            // previously existing outside of the scheme type body.
            Self::Scheme(quant, ty) => {
                ty.free_vars_impl(set);
                for q in quant {
                    set.remove(q);
                }
            },
            Self::Variable(tv) => { set.insert(*tv); },
        }
    }

    fn free_vars(&self) -> IndexSet<TypeVar> {
        let mut r = IndexSet::with_capacity(10);
        self.free_vars_impl(&mut r);
        r
    }

    fn substitute(&mut self, subst: &IndexMap<TypeVar, Type<'a>>) {
        match self {
            Self::Concrete(_, args) => {
                args.iter_mut().for_each(|a| a.substitute(subst));
            },

            // NOTE: naively ignore quantifier and substitute body as if
            // monotype.
            Self::Scheme(_, ty) => {
                ty.substitute(subst);
            },

            Self::Variable(tv) => if let Some(ty) = subst.get(tv) { 
                *self = ty.clone();
            },
        };
    }

    fn generalize(&self, ctx: &mut InferContext) -> Self {
        let free_vars = self.free_vars();
        // let mut quant = Vec::with_capacity(free_vars.len());

        // let subst = free_vars.into_iter().map(|ftv| (ftv, {
        //     let tv = ctx.fresh_tvar();
        //     quant.push(tv);
        //     Self::Variable(tv)
        // })).collect();

        // Self::Scheme(quant, Box::new(self.substitute(&subst)))

        Self::Scheme(free_vars.into_iter().collect(),
                     Box::new(self.clone()))
    }

    fn instantiate(&self, ctx: &mut InferContext, span: &Span<'a>)
        -> Result<Self> {
        if let Self::Scheme(quant, ty) = self {
            let subst = quant.iter().map(|q|
                (*q, Self::Variable(ctx.fresh_tvar()))).collect();

            let mut ty: Type<'a> = *ty.clone();
            ty.substitute(&subst);
            Ok(ty)
        } else {
            let msg = span.format_err_at_pos(
                &format!("Attempt to instantiate non-scheme type: {}", self),
                true,
            ).unwrap();
            bail!("{}", msg);
        }
    }
}

impl<'a> fmt::Display for Type<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Concrete(id, args) => {
                match id {
                    TypeIdent::User(id) => write!(f, "{}", id.span.fragment())?,
                    TypeIdent::Function => write!(f, "FUN")?,
                    TypeIdent::Integer => write!(f, "INT")?,
                    TypeIdent::String => write!(f, "STR")?,
                    TypeIdent::Unit => write!(f, "NIL")?,
                }

                if (args.len() == 0) {
                    return Ok(());
                }

                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    write!(f, "{}", a)?;
                    if i < args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Type::Scheme(params, body) => {
                write!(f, "[forall ")?;
                for (i, p) in params.iter().enumerate() {
                    write!(f, "{}", p)?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "].{}", body)
            },
            Type::Variable(tv) => write!(f, "{}", tv),
        }
    }
}

impl<'a> fmt::Display for Constraint<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Eq { a, b, .. } =>
                write!(f, "eq: {} = {}", a, b),
            Constraint::NodeType { node, ty, .. } =>
                write!(f, "ast: {} => {}", node, ty),
        }
    }
}

impl<'a> Constraint<'a> {
    fn new_eq(
        tya: Type<'a>,
        tyb: Type<'a>,
        span: Span<'a>,
        ctx: Option<Rc<ConstraintCtx<'a>>>,
    ) -> Self {
        Self::Eq {
            a: tya,
            b: tyb,
            ctx,
            span,
        }
    }

    fn new_nodety(
        nodeid: AstNodeID, ty: Type<'a>, span: Span<'a>
    ) -> Self {
        Self::NodeType { node: nodeid, ty, span }
    }

    pub fn span(&self) -> &Span<'a> {
        match self {
            Self::Eq { span, .. } | Self::NodeType { span, .. } => span,
        }
    }

    fn substitute(&mut self, subst: &IndexMap<TypeVar, Type<'a>>) {
        match self {
            Self::Eq { a, b, .. } => {
                a.substitute(subst);
                b.substitute(subst);
            },

            Self::NodeType { ty, .. } =>
                ty.substitute(subst),
        };
    }
}

struct InferContext {
    next_type_var_id: usize,
}

impl InferContext {
    fn new() -> Self {
        Self {
            next_type_var_id: 0,
        }
    }

    fn fresh_tvar(&mut self) -> TypeVar {
        let r = self.next_type_var_id;
        self.next_type_var_id += 1;
        TypeVar(r)
    }
}

impl<'a> Into<Type<'a>> for TypeVar {
    fn into(self) -> Type<'a> {
        Type::Variable(self)
    }
}


// NOTE: Thanks to `Path<'a>`s, there's no real need for scoping in the
// inference code. The purpose of Scope here is mainly to optimize memory usage
// as it is better than having one huge IndexMap which would end up containing
// all the symbols in the program.
struct Scope<'a> {
    frame_sizes: Vec<usize>,
    bindings: IndexMap<Rc<Path<'a>>, Type<'a>>,
}

impl<'a> Scope<'a> {
    fn new() -> Self {
        Self {
            frame_sizes: {
                let mut fss = Vec::with_capacity(10);
                fss.push(0);
                fss
            },
            bindings: IndexMap::with_capacity(50),
        }
    }

    fn push_frame(&mut self) {
        self.frame_sizes.push(0);
    }

    fn pop_frame(&mut self) {
        assert!(self.frame_sizes.len() > 1);

        for _ in 0..self.frame_sizes.pop().unwrap() {
            self.bindings.pop();
        }
    }

    fn get<'b>(&'b self, id: &Ident<'a>) -> Option<&Type<'a>> {
        self.bindings.get(&id.path)
    }

    fn try_get<'b>(&'b self, id: &Ident<'a>) -> Result<&Type<'a>> {
        self.get(id).with_context(|| {
            id.span
                .format_err_at_pos(
                    &format!("`{}` not found in scope", id.path), true)
                .unwrap()
        })
    }

    fn bind(&mut self, path: Rc<Path<'a>>, ty: Type<'a>) {
        if let Some(fs) = self.frame_sizes.last_mut() {
            *fs += 1;
        } else {
            unreachable!();
        }
        if let Some(_) = self.bindings.insert(path, ty) {
            panic!("{}\n{}",
                   "attempt to bind already existing path.",
                   "(this should not happend as paths should be unique)");
        }
    }

    fn substitute(&mut self, subst: &IndexMap<TypeVar, Type<'a>>) {
        for (_, ty) in self.bindings.iter_mut() {
            ty.substitute(subst);
        }
    }
}

macro_rules! with_subscope {
    ($scp:ident => $subscp:ident { $($body:tt)* }) => {
        let $subscp = $scp;
        $subscp.push_frame();

        $($body)*

        $subscp.pop_frame();
        let $scp = $subscp;
    }
}

macro_rules! Type {
    (@impl $id:expr, $args:expr) => (Type::Concrete($id, $args));
    ($builtin:ident ( ...$args:expr )) => (
        Type!(@impl TypeIdent::$builtin, $args)
    );
    ($builtin:ident ( $($args:expr),* )) => (
        Type!(@impl TypeIdent::$builtin, vec![$($args.into()),*])
    );
    ([$typeid:expr] ( ...$args:expr )) => (
        Type!(@impl $typeid, $args)
    );
    ([$typeid:expr] ( $($args:expr),* )) => (
        Type!(@impl $typeid, vec![$($args.into()),*])
    );
}

macro_rules! Constraint {
    (eq: $a:expr, $b:expr, $s:expr) => {
        Constraint::new_eq($a.into(), $b.into(), $s, None)
    };
    (eq: $a:expr, $b:expr, $s:expr, $c:expr) => {
        Constraint::new_eq($a.into(), $b.into(), $s, $c)
    };
    (ast: $a:expr, $b:expr, $s:expr) => {
        Constraint::new_nodety($a, $b.into(), $s)
    };
}


#[enum_dispatch(Expr)]
trait GenConstraints<'a> {
    fn gen_constraints(
        &self,
        targ: TypeVar,
        cons: &mut Vec<Constraint<'a>>,
        ctx: &mut InferContext,
        scp: &mut Scope<'a>,
    ) -> Result<()>;
}

macro_rules! GenConstraints {
    (@type $ty:path,   ) => ($ty);
    (@type $ty:path, Rc) => (Rc<$ty>);
    (for $o:ident(
            $this:pat,
            $targ:ident,
            $cons:ident,
            $ctx:ident,
            $scp:ident
            )$(: $ty:ident)?  = $body:expr) => (
        impl<'a> GenConstraints<'a>
        for GenConstraints!(@type $o<'a>, $($ty)?) {
            fn gen_constraints(
                &self,
                $targ: TypeVar,
                $cons: &mut Vec<Constraint<'a>>,
                $ctx: &mut InferContext,
                $scp: &mut Scope<'a>,
            ) -> Result<()> {
                let $this = self;
                $body
            }
        }
    );

//     {Rc<$ty:ident<$lt:lifetime>>(&$self:ident, $targ:ident, $cons:ident, $ctx:ident, $scp:ident)
//      => $ret:expr} => {
//         impl<$lt> GenConstraints<$lt> for Rc<$ty<$lt>> {
//             fn gen_constraints<'s>(
//                 &self,
//                 $targ: TypeVar,
//                 $cons: &mut Vec<Constraint<$lt>>,
//                 $ctx: &mut InferContext,
//                 $scp: &Scope<$lt, 's>,
//             ) -> Result<()> {
//                 // self is not a valid identifier to pass a macro
//                 let $self = self;
//                 $ret
//             }
//         }
//     };
//     {$ty:ident<$lt:lifetime>(&$self:ident, $targ:ident, $cons:ident, $ctx:ident, $scp:ident)
//      => $ret:expr} => {
//         impl<$lt> GenConstraints<$lt> for $ty<$lt> {
//             fn gen_constraints<'s>(
//                 &self,
//                 $targ: TypeVar,
//                 $cons: &mut Vec<Constraint<$lt>>,
//                 $ctx: &mut InferContext,
//                 $scp: &Scope<$lt, 's>,
//             ) -> Result<()> {
//                 // self is not a valid identifier to pass a macro
//                 let $self = self;
//                 $ret
//             }
//         }
//     }
}

GenConstraints!(for Ident(_this, _targ, _cons, _ctx, _scp) = unimplemented!());
GenConstraints!(for Stmt(_this, _targ, _cons, _ctx, _scp) = unimplemented!());

GenConstraints!(for VarRef(this, targ, cons, _ctx, scp) = {
    cons.push(Constraint!(ast: this.get_id(), targ, this.span()));
    cons.push(
        Constraint!(
            eq: targ, scp.try_get(&this.name)?.clone(), this.span()));
    Ok(())
});

GenConstraints!(for IntLit(this, targ, cons, _ctx, _scp) = {
    cons.push(Constraint!(ast: this.get_id(), targ, this.span()));
    cons.push(Constraint!(eq: targ, Type!(Integer()), this.span()));
    Ok(())
});

GenConstraints!(for StrLit(this, targ, cons, _ctx, _scp) = {
    cons.push(Constraint!(ast: this.get_id(), targ, this.span()));
    cons.push(Constraint!(eq: targ, Type!(String()), this.span()));
    Ok(())
});

GenConstraints!(for Block(this, targ, cons, ctx, scp) = {

    with_subscope!(scp => subscp {

        for stmt in &this.body {
            match stmt {
                Stmt::Expr(e) => {
                    e.gen_constraints(ctx.fresh_tvar(), cons, ctx, subscp)?;
                },
                Stmt::VarLet(vl) => {
                    let tvar = ctx.fresh_tvar();
                    vl.val.gen_constraints(tvar, cons, ctx, subscp)?;
                    subscp.bind(Rc::clone(&vl.var.path), tvar.into());
                },
            }
        }

        if let Some(ref e) = this.ret {
            e.gen_constraints(targ, cons, ctx, subscp)?;
        } else {
            cons.push(Constraint!(eq: targ, Type!(Unit()), this.span()));
        }
        cons.push(Constraint!(ast: this.get_id(), targ, this.span()));

    });

    Ok(())
});

GenConstraints!(for FunCal(this, targ, cons, ctx, scp) = {
    let mut fty_args = Vec::<Type<'a>>::with_capacity(this.args.len() + 1);
    for arg in &this.args {
        let tvar = ctx.fresh_tvar();
        fty_args.push(tvar.into());
        arg.gen_constraints(tvar, cons, ctx, scp)?;
    }
    fty_args.push(targ.into());

    let fty_b = Type!(Function(...fty_args));

    let fty_a = scp.try_get(&this.name)?;

    let fty_a = if let Type::Scheme(..) = fty_a {
        fty_a.instantiate(ctx, &this.span())?
    } else {
        fty_a.clone()
    };

    cons.push(Constraint!(ast: this.get_id(), targ, this.span()));
    cons.push(Constraint!(eq: fty_a, fty_b,
                          this.span(),
                          Some(Rc::new(ConstraintCtx::FunCal{
                              fun: Rc::clone(&this.name.path)
                          }))));

    Ok(())
});

impl<'a> FunDef<'a> {
    fn gen_constraints(
        self: &Rc<Self>,
        cons: &mut Vec<Constraint<'a>>,
        ctx: &mut InferContext,
        scp: &mut Scope<'a>,
    ) -> Result<Type<'a>> {

        with_subscope!(scp => subscp {

            let retty = ctx.fresh_tvar();

            let mut fty_args
                = Vec::<Type<'a>>::with_capacity(self.argnames.len() + 1);
            for name in &self.argnames {
                let tvar = ctx.fresh_tvar();
                fty_args.push(tvar.into());
                subscp.bind(Rc::clone(&name.path), tvar.into());
            }
            self.body.gen_constraints(retty, cons, ctx, subscp)?;
            fty_args.push(retty.into());
            let fty = Type!(Function(...fty_args));

        });

        Ok(fty)
    }
}

// group of recursive functions depending on eachother
struct FunDefGroup<'a, 'f>(Vec<&'f Rc<FunDef<'a>>>);
impl<'a, 'f> FunDefGroup<'a, 'f> {
    fn gen_constraints(
        &self,
        cons: &mut Vec<Constraint<'a>>,
        ctx: &mut InferContext,
        scp: &mut Scope<'a>,
    ) -> Result<()> {
        // TODO: detect situations that fall under limitations of type
        //       inference and output warnings telling user to
        //       explicitly type the function(s)

        with_subscope!(scp => subscp {

            for fundef in self.0.iter() {
                // monomorphic fun type within recursive function bodies
                subscp.bind(Rc::clone(&fundef.name.path),
                            ctx.fresh_tvar().into());
            }

            let mut ftys = Vec::with_capacity(self.0.len());
            for fundef in self.0.iter() {
                let fty = fundef.gen_constraints(cons, ctx, subscp)?;
                ftys.push(fty);
            }

            let subst = unify(cons.clone())?;
            substitute_constraints(cons, &subst);
            subscp.substitute(&subst);

            for (fundef, fty) in self.0.iter().zip(ftys.iter_mut()) {
                fty.substitute(&subst);
                let gen_fty = fty.generalize(ctx);

                let monoty = subscp.try_get(&fundef.name)?;
                let instance = gen_fty.instantiate(ctx, &fundef.span())?;
                cons.push(Constraint!(eq: monoty.clone(),
                                      instance, fundef.span()));
            }

            let subst = unify(cons.clone())?;
            substitute_constraints(cons, &subst);
            subscp.substitute(&subst);

            for (fundef, fty) in self.0.iter().zip(ftys.iter_mut()) {
                fty.substitute(&subst);
                *fty = fty.generalize(ctx);

                cons.push(Constraint!(ast: IAstNode::get_id(*fundef),
                                      fty.clone(), fundef.span()));
            }

        });

        for (fundef, fty) in self.0.iter().zip(ftys.into_iter()) {
            scp.bind(Rc::clone(&fundef.name.path), fty);
        }

        Ok(())
    }
}

impl<'a> Module<'a> {
    pub fn gen_constraints(&self, symbols: &Symbols<'a>)
        -> Result<Vec<Constraint<'a>>> {

        let mut ctx = InferContext::new();
        let mut scp = Scope::new();
        let mut r: Vec<Constraint<'a>> =
            Vec::with_capacity(self.toplvls.len() * 50);

        let fundefs = 
            topological_sort(symbols, &symbols.fundefs.values().collect())
            .context("Failed to order function dependencies")?;

        for group in fundefs.into_iter() {
            println!("rec-group:");
            for fd in group.iter() {
                println!("\t{} :\t{}", fd.name.path, fd.span().fragment());
            }
            FunDefGroup(group).gen_constraints(&mut r, &mut ctx, &mut scp)?;
        }

        // TODO: inference on other ast toplvls (typedefs/structdefs)

        let subst = unify(r.clone())?;
        substitute_constraints(&mut r, &subst);

        Ok(r)
    }
}

fn substitute_constraints<'a>(
    cons: &mut Vec<Constraint<'a>>,
    subst: &IndexMap<TypeVar, Type<'a>>,
) {
    cons.iter_mut().for_each(|c| c.substitute(&subst));
    cons.retain(|con| match con {
        Constraint::Eq{a, b, ..} => a != b,
        Constraint::NodeType{..} => true,
    });
}

/// Compose two substitutions such that (a ◦ b)S = a(bS) and b := (a ◦ b).
fn compose_substs<'a>(
    a: IndexMap<TypeVar, Type<'a>>,
    b: &mut IndexMap<TypeVar, Type<'a>>,
) {
    for (_, ty) in b.iter_mut() {
        ty.substitute(&a);
    }
    for (v, ty) in a.into_iter() {
        if !b.contains_key(&v) {
            b.insert(v, ty);
        }
    }
}

fn unify<'a>(
    mut cons: Vec<Constraint<'a>>
) -> Result<IndexMap<TypeVar, Type<'a>>> {
    let mut r = IndexMap::with_capacity(cons.len());

    let mut i = 0;
    while i < cons.len() {
        match cons[i].clone() {
            Constraint::Eq{a, b, span, ctx} => {
                match (a, b) {
                    (Type::Variable(x), Type::Variable(y)) if x == y => {
                        trace!("igoring {} = {}",
                               Type::Variable(x),
                               Type::Variable(y));
                    },

                    (Type::Variable(x), ty) | (ty, Type::Variable(x)) => {
                        if !ty.free_vars().contains(&x) {
                            let len = cons.len();
                            let mut sub = indexmap!{x => ty};
                            trace!("running substitution: {:?}", sub);

                            // NOTE: Not calling substitute_constraints() here
                            // since it also changes the length of the vec
                            cons[i..len]
                                .iter_mut()
                                .for_each(|c| c.substitute(&sub));

                            compose_substs(sub, &mut r);
                        } else {
                            let msg = span.format_err_at_pos(
                                "failed occurs check!",
                                true,
                            ).unwrap();
                            bail!("{}", msg);
                        }
                    },

                    (Type::Concrete(ta, aargs), Type::Concrete(tb, bargs))
                        if ta == tb && aargs.len() == bargs.len() => {
                            let mut n = 0;
                            for (a, b) in aargs.into_iter().zip(bargs.into_iter()) {
                                if let Some(ConstraintCtx::FunCal{fun})
                                    = ctx.as_ref().map(|c| c.as_ref()) {
                                    cons.push(
                                        Constraint!(
                                            eq: a, b, span,
                                            Some(Rc::new(
                                                ConstraintCtx::FunCalArg{
                                                    fun: Rc::clone(fun),
                                                    n,
                                                }
                                            ))));
                                } else {
                                    cons.push(
                                        Constraint!(
                                            eq: a, b, span,
                                            ctx.as_ref().map(|ctx| Rc::clone(ctx))));
                                }
                                n += 1;
                            }
                        },

                    (a, b) if a == b => {
                        trace!("igoring {} = {}", a, b);
                    }

                    (a, b) => {
                        let msg = span.format_err_at_pos(
                            &format!("Type mismatch {} and {} {}", a, b,
                                     ctx.map(|ctx| ctx.context()).unwrap_or("".to_string())
                            ),
                            true,
                        ).unwrap();
                        bail!("{}", msg);
                    },
                }
            },

            Constraint::NodeType{..} => (),
        }

        i += 1;
    }

    Ok(r)
}

pub trait FormatAtPos {
    fn format_err_at_pos(&self, msg: &str, underline: bool) -> Result<String>;
    fn format_note_at_pos(&self, msg: &str, underline: bool) -> Result<String>;
}

impl<'a> FormatAtPos for Span<'a> {
    fn format_err_at_pos(&self, msg: &str, underline: bool) -> Result<String> {
        format_at_pos(
            self,
            &format!("{} {}", Paint::red("error:").bold(), msg),
            self.extra,
            underline,
        )
    }

    fn format_note_at_pos(&self, msg: &str, underline: bool) -> Result<String> {
        format_at_pos(
            self,
            &format!("{} {}", Paint::yellow("note:").bold(), msg),
            self.extra,
            underline,
        )
    }
}

// Foo.A for Module.A = {
//     foo(b, c) = b * c;

//     gen_constraints(this, targ, ctx, scp) = {
//         r      = mut Vec:new();
//         subscp = mut subscope(scp);
//         retty  = fresh_tvar(ctx);

//         fly_args = Vec:with_capacity(len(argnames(this)) + 1);
//         loop!(name in argnames(this)) {
//             tvar = fresh_tvar(ctx);
//             push(fty_args, coerce(tvar));
//             bind(subscp, clone(name), tvar);
//         };
//         push(fty_args, coerce(retty));
//         fty = Type:new!(Function(...fty_args));

//         push(r, Constraint:new!(ast: get_id(this), targ, span(this)));
//         push(r, Constraint:new!(eq: targ, fty, span(this)));

//         extend(r, body(this) |> gen_constraints(retty, ctx, &subscp)?)
//         ok(r)
//     };
// };

#[cfg(test)]
mod test {
    use crate::parser::File;
    use crate::ast::Span;
    use super::*;

    use rstest::*;
    use lazy_static::*;

    lazy_static! {
        static ref FILE: File = File {
            prog: "test() = 0;".to_string(),
            path: "-".to_string(),
        };
        static ref SPAN: Span<'static> = Span::new_extra(&FILE.prog, &FILE);
    }

    macro_rules! Constraints {
        [$(($($tt:tt)+)),*$(,)?] => (vec![$(Constraint!($($tt)+, *SPAN)),*]);
    }


    #[rstest(sub, ty, expected,
             case(indexmap!{}, Type!(Integer()), Type!(Integer())),

             case(indexmap! {
                 TypeVar(0) => Type!(Integer()),
             }, Type::Variable(TypeVar(0)), Type!(Integer())),

             case(indexmap! {
                 TypeVar(0) => Type!(Integer()),
             }, Type!(Function(TypeVar(0))), Type!(Function(Type!(Integer())))),
             ::trace
    )]
    fn type_substitute(
        sub: IndexMap<TypeVar, Type<'static>>,
        mut ty: Type<'static>,
        expected: Type<'static>,
    ) {
        ty.substitute(&sub);
        assert_eq!(ty, expected);
    }

    #[rstest(constraints, expected,
             case(Constraints![
                 (eq: Type!(Integer()), Type!(Integer()))
             ], indexmap! {}),

             case(Constraints![
                 (eq: Type::Variable(TypeVar(0)), Type!(Integer()))
             ], indexmap! { TypeVar(0) => Type!(Integer())}),

             case(Constraints![
                 (eq: Type::Variable(TypeVar(0)), Type!(Integer())),
                 (eq: Type::Variable(TypeVar(1)), Type::Variable(TypeVar(0))),
             ], indexmap! {
                 TypeVar(0) => Type!(Integer()),
                 TypeVar(1) => Type!(Integer()),
             }),

             case(Constraints![
                 (eq: Type::Variable(TypeVar(0)), Type!(Integer())),
                 (eq: Type::Variable(TypeVar(0)), Type::Variable(TypeVar(1))),
             ], indexmap! {
                 TypeVar(0) => Type!(Integer()),
                 TypeVar(1) => Type!(Integer()),
             }),

             #[should_panic]
             case::occurs_check_fail(Constraints![
                 (eq: Type::Variable(TypeVar(0)), Type!(Function(TypeVar(1)))),
                 (eq: Type::Variable(TypeVar(1)), Type::Variable(TypeVar(0))),
             ], indexmap! {}),

             case(Constraints![
                 (eq: Type::Variable(TypeVar(0)), Type!(Function(TypeVar(1)))),
                 (eq: Type::Variable(TypeVar(2)), Type::Variable(TypeVar(1))),
             ], indexmap! {
                 TypeVar(0) => Type!(Function(TypeVar(1))),
                 TypeVar(2) => Type::Variable(TypeVar(1)),
             }),

             case(Constraints![
                 (eq: Type::Variable(TypeVar(1)), Type::Variable(TypeVar(2))),
                 (eq: Type::Variable(TypeVar(0)),
                  Type!(Function(Type!(Function(TypeVar(1)))))),
             ], indexmap! {
                 TypeVar(1) => Type::Variable(TypeVar(2)),
                 TypeVar(0) => Type!(Function(Type!(Function(TypeVar(2))))),
             }),

             ::trace
    )]
    fn unify_unifies(
        constraints: Vec<Constraint>,
        expected: IndexMap<TypeVar, Type>) {
        let unified = unify(constraints).unwrap();

        for k in expected.keys() {
            assert_eq!((k, &unified[k]), (k, &expected[k]));
        }
    }
}
