use crate::syntax;
use std::{collections::HashSet, io::Write, ptr::NonNull};

pub struct Constraint {
    root: NonNull<GenNode>,
}

impl Constraint {
    pub fn new(term: syntax::Term) -> Constraint {
        ConstraintBuilder::new().build(term)
    }

    pub fn write_dot(&self, w: impl Write) -> Result<(), std::io::Error> {
        DotWriter::new(w).write(self.root)
    }
}

enum Edge {
    Unif(NonNull<TyNode>),
    Inst(NonNull<GenNode>),
}

struct ConstraintBuilder {
    vars: Vec<Edge>,
}

impl ConstraintBuilder {
    fn new() -> ConstraintBuilder {
        ConstraintBuilder { vars: Vec::new() }
    }

    fn build(&mut self, term: syntax::Term) -> Constraint {
        match term {
            syntax::Term::Var(id) => self.variable(id),
            syntax::Term::Apply(fun, arg) => self.apply(*fun, *arg),
            syntax::Term::Lambda(_, body) => self.lambda(*body),
            syntax::Term::Let(_, value, body) => self.let_expr(*value, *body),
            syntax::Term::Coerce(ty) => self.coerce(ty),
        }
    }

    fn variable(&mut self, id: usize) -> Constraint {
        let root = match self.vars[self.vars.len() - 1 - id] {
            Edge::Unif(ty) => GenNode::new(ty),
            Edge::Inst(gen) => {
                let var = TyNode::new_bottom();
                let root = GenNode::new(var);
                TyNode::bind(
                    var,
                    Binder {
                        flag: BindingFlag::Flexible,
                        node: NodePtr::Gen(root),
                    },
                );
                TyNode::constrain(var, gen);
                root
            }
        };
        Constraint { root }
    }

    fn apply(&mut self, fun: syntax::Term, arg: syntax::Term) -> Constraint {
        let arg_ty = TyNode::new_bottom();
        let ret_ty = TyNode::new_bottom();
        let fun_ty = TyNode::new_arrow(arg_ty, ret_ty);
        let fun = self.build(fun);
        let arg = self.build(arg);
        TyNode::constrain(fun_ty, fun.root);
        TyNode::constrain(arg_ty, arg.root);
        let root = GenNode::new(ret_ty);
        let binder = Binder {
            flag: BindingFlag::Flexible,
            node: NodePtr::Gen(root),
        };
        GenNode::bind(fun.root, root);
        GenNode::bind(arg.root, root);
        TyNode::bind(fun_ty, binder);
        TyNode::bind(arg_ty, binder);
        TyNode::bind(ret_ty, binder);
        Constraint { root }
    }

    fn lambda(&mut self, body: syntax::Term) -> Constraint {
        let arg_ty = TyNode::new_bottom();
        let ret_ty = TyNode::new_bottom();
        let fun_ty = TyNode::new_arrow(arg_ty, ret_ty);
        self.vars.push(Edge::Unif(arg_ty));
        let body = self.build(body);
        self.vars.pop();
        TyNode::constrain(ret_ty, body.root);
        let root = GenNode::new(fun_ty);
        let binder = Binder {
            flag: BindingFlag::Flexible,
            node: NodePtr::Gen(root),
        };
        GenNode::bind(body.root, root);
        TyNode::bind(fun_ty, binder);
        TyNode::bind(arg_ty, binder);
        TyNode::bind(ret_ty, binder);
        Constraint { root }
    }

    fn let_expr(&mut self, value: syntax::Term, body: syntax::Term) -> Constraint {
        let var = TyNode::new_bottom();
        let root = GenNode::new(var);
        TyNode::bind(
            var,
            Binder {
                flag: BindingFlag::Flexible,
                node: NodePtr::Gen(root),
            },
        );
        let val = self.build(value);
        self.vars.push(Edge::Inst(val.root));
        let body = self.build(body);
        self.vars.pop();
        GenNode::bind(val.root, root);
        GenNode::bind(body.root, root);
        TyNode::constrain(var, body.root);
        Constraint { root }
    }

    fn coerce(&mut self, ty: syntax::Type) -> Constraint {
        let arg = Type::new(ty.clone());
        let ret = Type::new(ty);
        let fun = TyNode::new_arrow(arg.root, ret.root);
        let root = GenNode::new(fun);
        TyNode::bind(
            arg.root,
            Binder {
                flag: BindingFlag::Rigid,
                node: NodePtr::Gen(root),
            },
        );
        TyNode::bind(
            ret.root,
            Binder {
                flag: BindingFlag::Flexible,
                node: NodePtr::Gen(root),
            },
        );
        TyNode::bind(
            fun,
            Binder {
                flag: BindingFlag::Flexible,
                node: NodePtr::Gen(root),
            },
        );
        Constraint { root }
    }
}

struct DotWriter<W> {
    w: W,
    visited_gen: HashSet<NonNull<GenNode>>,
    visited_ty: HashSet<NonNull<TyNode>>,
}

impl<W: Write> DotWriter<W> {
    fn new(w: W) -> DotWriter<W> {
        DotWriter {
            w,
            visited_gen: HashSet::new(),
            visited_ty: HashSet::new(),
        }
    }

    fn visit_gen(&mut self, gen: NonNull<GenNode>) -> Result<(), std::io::Error> {
        if !self.visited_gen.insert(gen) {
            return Ok(());
        }
        let r = unsafe { gen.as_ref() };
        writeln!(self.w, "    gen_{0:?} [label=\"{0:?}\", shape=rect]", gen)?;
        for ptr in r.bound.iter() {
            match *ptr {
                NodePtr::Gen(node) => self.visit_gen(node)?,
                NodePtr::Ty(node) => self.visit_ty(node)?,
            }
        }

        writeln!(self.w, "    gen_{:?} -> ty_{:?} [dir=none]", gen, r.ty)?;
        if let Some(binder) = r.binder {
            writeln!(
                self.w,
                "    gen_{:?} -> gen_{:?} [style=dotted dir=back]",
                binder, gen
            )?;
        }
        r.constrains.iter().try_for_each(|ptr| {
            writeln!(
                self.w,
                "    gen_{:?} -> ty_{:?} [color=\"red:red\" style=dashed arrowhead=veevee]",
                gen, ptr
            )
        })?;
        Ok(())
    }

    fn visit_ty(&mut self, ty: NonNull<TyNode>) -> Result<(), std::io::Error> {
        if !self.visited_ty.insert(ty) {
            return Ok(());
        }
        let r = unsafe { ty.as_ref() };
        match r.structure {
            Structure::Arrow(arg, ret) => {
                writeln!(self.w, "    ty_{0:?} [label=\"\u{2192}\\n{0:?}\"]", ty)?;
                writeln!(self.w, "    ty_{:?}:sw -> ty_{:?} [dir=none]", ty, arg)?;
                writeln!(self.w, "    ty_{:?}:se -> ty_{:?} [dir=none]", ty, ret)?;
            }
            Structure::Bottom => writeln!(self.w, "    ty_{0:?} [label=\"\u{22a5}\\n{0:?}\"]", ty)?,
        }
        for ptr in r.bound.iter() {
            self.visit_ty(*ptr)?;
        }

        if let Some(binder) = r.binder {
            let style = match binder.flag {
                BindingFlag::Flexible => "dotted",
                BindingFlag::Rigid => "dashed",
            };
            match binder.node {
                NodePtr::Gen(binder) => writeln!(
                    self.w,
                    "    gen_{:?} -> ty_{:?} [style={} dir=back]",
                    binder, ty, style
                )?,
                NodePtr::Ty(binder) => writeln!(
                    self.w,
                    "    ty_{:?} -> ty_{:?} [style={} dir=back]",
                    binder, ty, style
                )?,
            }
        }
        Ok(())
    }

    fn write(&mut self, constraint: NonNull<GenNode>) -> Result<(), std::io::Error> {
        writeln!(self.w, "digraph {{")?;
        self.visit_gen(constraint)?;
        writeln!(self.w, "}}")
    }
}

pub(crate) struct GenNode {
    ty: NonNull<TyNode>,
    binder: Option<NonNull<GenNode>>,
    bound: HashSet<NodePtr>,
    constrains: HashSet<NonNull<TyNode>>,
}

impl GenNode {
    pub(crate) fn new(ty: NonNull<TyNode>) -> NonNull<GenNode> {
        let node = Box::new(GenNode {
            ty,
            binder: None,
            bound: HashSet::new(),
            constrains: HashSet::new(),
        });
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(node)) };
        unsafe { &mut *ty.as_ptr() }
            .parents
            .insert(NodePtr::Gen(ptr));
        ptr
    }

    pub(crate) fn bind(this: NonNull<Self>, binder: NonNull<GenNode>) {
        unsafe { &mut *this.as_ptr() }.binder = Some(binder);
        unsafe { &mut *binder.as_ptr() }
            .bound
            .insert(NodePtr::Gen(this));
    }
}

pub struct Type {
    root: NonNull<TyNode>,
}

impl Type {
    pub fn new(ty: syntax::Type) -> Type {
        fn with_vars(ty: syntax::Type, vars: &mut Vec<NonNull<TyNode>>) -> NonNull<TyNode> {
            match ty {
                syntax::Type::Var(id) => vars[vars.len() - 1 - id],
                syntax::Type::Arrow(arg, ret) => {
                    let arg = with_vars(*arg, vars);
                    let ret = with_vars(*ret, vars);
                    TyNode::new_arrow(arg, ret)
                }
                syntax::Type::Forall(_, ty, body) => {
                    let bound = match ty {
                        Some(ty) => with_vars(*ty, vars),
                        None => TyNode::new_bottom(),
                    };
                    vars.push(bound);
                    let root = with_vars(*body, vars);
                    vars.pop();
                    TyNode::bind(
                        bound,
                        Binder {
                            flag: BindingFlag::Flexible,
                            node: NodePtr::Ty(root),
                        },
                    );
                    root
                }
            }
        }
        Type {
            root: with_vars(ty, &mut Vec::new()),
        }
    }
}

pub(crate) struct TyNode {
    parents: HashSet<NodePtr>,
    structure: Structure,
    binder: Option<Binder>,
    bound: HashSet<NonNull<TyNode>>,
    constraint: Option<NonNull<GenNode>>,
}

impl TyNode {
    pub(crate) fn new_bottom() -> NonNull<TyNode> {
        let node = Box::new(TyNode {
            parents: HashSet::new(),
            structure: Structure::Bottom,
            binder: None,
            bound: HashSet::new(),
            constraint: None,
        });
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(node)) };
        ptr
    }

    pub(crate) fn new_arrow(arg: NonNull<TyNode>, ret: NonNull<TyNode>) -> NonNull<TyNode> {
        let node = Box::new(TyNode {
            parents: HashSet::new(),
            structure: Structure::Arrow(arg, ret),
            binder: None,
            bound: HashSet::new(),
            constraint: None,
        });
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(node)) };
        unsafe { &mut *arg.as_ptr() }
            .parents
            .insert(NodePtr::Ty(ptr));
        unsafe { &mut *ret.as_ptr() }
            .parents
            .insert(NodePtr::Ty(ptr));
        ptr
    }

    pub(crate) fn bind(this: NonNull<Self>, binder: Binder) {
        unsafe { &mut *this.as_ptr() }.binder = Some(binder);
        match binder.node {
            NodePtr::Gen(gen) => unsafe { &mut *gen.as_ptr() }
                .bound
                .insert(NodePtr::Ty(this)),
            NodePtr::Ty(ty) => unsafe { &mut *ty.as_ptr() }.bound.insert(this),
        };
    }

    pub(crate) fn constrain(this: NonNull<TyNode>, constraint: NonNull<GenNode>) {
        unsafe { &mut *this.as_ptr() }.constraint = Some(constraint);
        unsafe { &mut *constraint.as_ptr() }.constrains.insert(this);
    }
}

enum Structure {
    Arrow(NonNull<TyNode>, NonNull<TyNode>),
    Bottom,
}

#[derive(Clone, Copy)]
pub(crate) struct Binder {
    flag: BindingFlag,
    node: NodePtr,
}

#[derive(Clone, Copy)]
enum BindingFlag {
    Flexible,
    Rigid,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum NodePtr {
    Gen(NonNull<GenNode>),
    Ty(NonNull<TyNode>),
}
