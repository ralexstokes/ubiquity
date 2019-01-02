use std::io;

use itertools::Itertools;

use super::reader::Expr;

pub fn print_to(ast: &[Expr], mut out: impl io::Write) -> io::Result<()> {
    write!(&mut out, "{}", ast.iter().format(" "))
}
