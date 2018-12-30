use std::io::{self, Write};

use itertools::Itertools;

use super::reader::Ast;

pub fn print_to(ast: &[Ast], mut out: impl Write) -> io::Result<()> {
    write!(&mut out, "{}", ast.iter().format(" "))
}
