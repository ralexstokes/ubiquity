use std::io;

use super::evaluator::Result;
use super::reader::Expr;

pub fn print_expr_to(mut out: impl io::Write, expr: &Expr) -> io::Result<()> {
    write!(&mut out, "{}", expr)
}

pub fn println_to(mut out: impl io::Write, exprs: &[Result<Expr>]) -> io::Result<()> {
    for expr in exprs {
        match expr {
            Ok(expr) => {
                print_expr_to(&mut out, &expr)?;
                writeln!(&mut out, "")?;
            }
            Err(e) => {
                writeln!(&mut out, "error: {}", e)?;
            }
        }
    }
    Ok(())
}
