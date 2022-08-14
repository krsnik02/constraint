use constraint::Constraint;
use syntax::{Term, parse_term};

pub mod constraint;
pub mod syntax;

fn main() {
    let choice = parse_term("(λ(x) λ(y) x : ∀(a) ∀(b ≤ a → a) a → b)").unwrap();
    let id = parse_term("let s = λ(x) λ(y) λ(z) x z (y z) in let k = λ(x) λ(y) x in s k k").unwrap();
    let term = Term::Apply(Box::new(choice), Box::new(id));
    println!("{:?}", term);
    let constraint = Constraint::new(term);

    constraint.write_dot(std::io::stdout()).unwrap();

}
