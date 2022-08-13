use std::{ptr::NonNull, collections::HashSet, io::Write};

pub enum Term {
    Var(usize),
    App(Box<Term>, Box<Term>),
    Lam(Box<Term>), // binder
}

pub struct Constraint {
    root: NonNull<GenNode>,
}

impl Constraint {
    pub fn new(term: Term) -> Constraint {
        fn with_vars(term: Term, vars: &mut Vec<NonNull<TyNode>>) -> Constraint {
            match term {
                Term::Var(id) => {
                    let ty = vars[vars.len() - 1 - id]; 
                    let root = GenNode::new(ty);
                    Constraint { root }
                }
                Term::App(fun, arg) => {
                    let arg_ty = TyNode::new_bottom();
                    let ret_ty = TyNode::new_bottom();
                    let fun_ty = TyNode::new_arrow(arg_ty, ret_ty);

                    let fun = with_vars(*fun, vars);
                    let arg = with_vars(*arg, vars);
                    TyNode::constrain(fun_ty, fun.root);
                    TyNode::constrain(arg_ty, arg.root);

                    let root = GenNode::new(ret_ty);
                    let binder = Binder { flag: BindingFlag::Flexible, node: NodePtr::Gen(root) };
                    GenNode::bind(fun.root, root);
                    GenNode::bind(arg.root, root);
                    TyNode::bind(fun_ty, binder);
                    TyNode::bind(arg_ty, binder);
                    TyNode::bind(ret_ty, binder);

                    Constraint { root }
                }
                Term::Lam(body) => {
                    let arg_ty = TyNode::new_bottom();
                    let ret_ty = TyNode::new_bottom();
                    let fun_ty = TyNode::new_arrow(arg_ty, ret_ty);

                    vars.push(arg_ty);
                    let body = with_vars(*body, vars);
                    vars.pop();
                    TyNode::constrain(ret_ty, body.root);

                    let root = GenNode::new(fun_ty);
                    let binder = Binder { flag: BindingFlag::Flexible, node: NodePtr::Gen(root) };
                    GenNode::bind(body.root, root);
                    TyNode::bind(fun_ty, binder);
                    TyNode::bind(arg_ty, binder);
                    TyNode::bind(ret_ty, binder);

                    Constraint { root }
                }
            }
        }
        with_vars(term, &mut Vec::new())
    }


    pub fn write_dot(&self, mut w: impl Write) -> Result<(), std::io::Error> {
        fn visit_gen(
            gen: NonNull<GenNode>, 
            w: &mut impl Write,
            visited_gen: &mut HashSet<NonNull<GenNode>>,
            visited_ty: &mut HashSet<NonNull<TyNode>>,
        ) -> Result<(), std::io::Error> {
            if !visited_gen.insert(gen) { return Ok(()) }
            let r = unsafe { gen.as_ref() };

            writeln!(w, "    gen_{0:?} [label=\"{0:?}\", shape=rect]", gen)?;
            r.bound.iter().try_for_each(|ptr| match *ptr {
                NodePtr::Gen(node) => visit_gen(node, w, visited_gen, visited_ty),
                NodePtr::Ty(node) => visit_ty(node, w, visited_ty),
            })?;

            writeln!(w, "    gen_{:?} -> ty_{:?} [dir=none]", gen, r.ty)?;
            if let Some(binder) = r.binder {
                writeln!(w, "    gen_{:?} -> gen_{:?} [style=dotted dir=back]", binder, gen)?;
            }

            r.constrains.iter().try_for_each(|ptr|
                writeln!(w, "    gen_{:?} -> ty_{:?} [color=\"red:red\" style=dashed arrowhead=veevee]", gen, ptr)
            )?;

            Ok(())
        }

        fn visit_ty(
            ty: NonNull<TyNode>,
            w: &mut impl Write,
            visited_ty: &mut HashSet<NonNull<TyNode>>,
        ) -> Result<(), std::io::Error> {
            if !visited_ty.insert(ty) { return Ok(()) }
            let r = unsafe { ty.as_ref() };

            match r.structure {
                Structure::Arrow(arg, ret) => {
                    visit_ty(arg, w, visited_ty)?;
                    visit_ty(ret, w, visited_ty)?;
                    writeln!(w, "    ty_{0:?} [label=\"\u{2192}\\n{0:?}\"]", ty)?;
                    writeln!(w, "    ty_{:?}:sw -> ty_{:?} [dir=none]", ty, arg)?;
                    writeln!(w, "    ty_{:?}:se -> ty_{:?} [dir=none]", ty, ret)?;
                }
                Structure::Bottom => writeln!(w, "    ty_{0:?} [label=\"\u{22a5}\\n{0:?}\"]", ty)?
            }

            if let Some(binder) = r.binder {
                let style = match binder.flag {
                    BindingFlag::Flexible => "dotted",
                    BindingFlag::Rigid => "dashed",
                };
                match binder.node {
                    NodePtr::Gen(binder) => {
                        writeln!(w, "    gen_{:?} -> ty_{:?} [style={} dir=back]", binder, ty, style)?
                    }
                    NodePtr::Ty(binder) => {
                        writeln!(w, "    ty_{:?} -> ty_{:?} [style={} dir=back]", binder, ty, style)?
                    }
                }
            }

            Ok(())
        }


        writeln!(w, "digraph {{")?;
        visit_gen(self.root, &mut w, &mut HashSet::new(), &mut HashSet::new())?;
        writeln!(w, "}}")
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
        unsafe { &mut *ty.as_ptr() }.parents.insert(NodePtr::Gen(ptr));
        ptr
    }

    pub(crate) fn bind(this: NonNull<Self>, binder: NonNull<GenNode>) {
        unsafe { &mut *this.as_ptr() }.binder = Some(binder);
        unsafe { &mut *binder.as_ptr() }.bound.insert(NodePtr::Gen(this));
    }
}

pub struct Type {
    root: NonNull<TyNode>,
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
        unsafe { &mut *arg.as_ptr() }.parents.insert(NodePtr::Ty(ptr));
        unsafe { &mut *ret.as_ptr() }.parents.insert(NodePtr::Ty(ptr));
        ptr
    }

    pub(crate) fn bind(this: NonNull<Self>, binder: Binder) {
        unsafe { &mut *this.as_ptr() }.binder = Some(binder);
        match binder.node {
            NodePtr::Gen(gen) => unsafe { &mut *gen.as_ptr() }.bound.insert(NodePtr::Ty(this)),
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
