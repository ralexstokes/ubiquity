use std::io;

use ubiquity::evaluator;
use ubiquity::printer;

fn main() -> io::Result<()> {
    let input = r#"
  (reduce (fn-with-meta
    {:docs "add two numbers"
     :args #{:a :b}}
    [a b]
      (+ a b)) (range 10 2)) ;; find a sum
  "#;

    let results = evaluator::eval(input);
    printer::print_to(results.as_slice(), io::stdout())?;

    println!("");

    let input = "(+ 2 2)";
    let results = evaluator::eval(input);

    printer::print_to(results.as_slice(), io::stdout());

    println!("");

    let input = "+";
    let results = evaluator::eval(input);

    printer::print_to(results.as_slice(), io::stdout())
}
