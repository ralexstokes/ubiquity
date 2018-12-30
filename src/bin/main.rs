use std::io;

use ubiquity::printer;
use ubiquity::reader;

fn main() -> io::Result<()> {
    let input = r#"
  (reduce (fn-with-meta
    {:docs "add two numbers"
     :args #{:a :b}}
    [a b]
      (+ a b)) (range 10 2)) ;; find a sum
  "#;

    let ast = reader::read(input).unwrap();

    printer::print_to(&ast, io::stdout())
}
