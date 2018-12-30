use std::io;

use itertools::Itertools;

use super::reader::Ast;

pub fn print_to(ast: &[Ast], mut out: impl io::Write) -> io::Result<()> {
    write!(&mut out, "{}", ast.iter().format(" "))
}
