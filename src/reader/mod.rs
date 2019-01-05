mod lexer;
mod parser;

use self::lexer::Lexer;
use self::parser::Parser;

pub use self::parser::{Error, Expr, FnDecl, HostFn, Result};

pub use self::lexer::lex;

pub fn read(input: &str) -> Vec<Result<Expr>> {
    let lexer = Lexer::new(input);

    let mut parser = Parser::new();
    parser.run(lexer)
}

#[cfg(test)]
mod tests {
    use super::parser::Expr;
    use super::*;

    #[test]
    fn can_read_expr() {
        let input = "(+ 2 3)";
        let expr = read(input).pop().unwrap();
        assert_eq!(
            expr,
            Ok(Expr::List(vec![
                Expr::Symbol("+".into()),
                Expr::Number(2),
                Expr::Number(3)
            ]))
        )
    }
}
