use std::io;

use super::evaluator::Result;
use super::reader::Expr;

pub fn print_expr_to(expr: &Expr, mut out: impl io::Write) -> io::Result<()> {
    write!(&mut out, "{}", expr)
}

pub fn print_to(exprs: &[Result<Expr>], mut out: impl io::Write) -> io::Result<()> {
    let mut result = Ok(());
    for expr in exprs {
        match expr {
            Ok(expr) => {
                result = print_expr_to(&expr, &mut out);
            }
            Err(e) => {
                result = write!(&mut out, "{:?}", e);
            }
        }
    }
    result
}
