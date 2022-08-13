use constraint::{Constraint, Term};

pub mod constraint;

fn main() {
    let term = Box::new(Term::Lam(
        // \x.
        Box::new(Term::Lam(
            // \y. 
            Box::new(Term::Lam(
                // \z.
                Box::new(Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Var(2)),
                        Box::new(Term::Var(0)),
                    )),
                    Box::new(Term::App(
                        Box::new(Term::Var(1)),
                        Box::new(Term::Var(0)),
                    )),
                ))
            ))
        ))
    ));
    let constraint = Constraint::new(*term);

    constraint.write_dot(std::io::stdout()).unwrap();

}
