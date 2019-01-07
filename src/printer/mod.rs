use std::io;

use super::evaluator::Result;
use super::reader::Expr;

pub fn print_expr_to(mut out: impl io::Write, expr: &Expr) -> io::Result<()> {
    write!(&mut out, "{}", expr)
}

pub fn print_to(mut out: impl io::Write, exprs: &[Result<Expr>]) -> io::Result<()> {
    let mut result = Ok(());
    for expr in exprs {
        match expr {
            Ok(expr) => {
                result = print_expr_to(&mut out, &expr);
            }
            Err(e) => {
                result = write!(&mut out, "{:?}", e);
            }
        }
    }
    result
}
