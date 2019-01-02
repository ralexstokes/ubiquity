mod lexer;
mod parser;

use self::lexer::Lexer;
use self::parser::Parser;

pub use self::parser::{Error, Expr, FnDecl, Result};

pub use self::lexer::lex;

pub fn read(input: &str) -> Result<Vec<Expr>> {
    let mut lexer = Lexer::new(input);

    let mut parser = Parser::new();
    parser.parse_tokens(&mut lexer)
}

#[cfg(test)]
mod tests {
    use super::parser::Expr;
    use super::*;

    #[test]
    fn can_read_expr() {
        let input = "(+ 2 3)";
        let expr = read(input).unwrap();
        assert_eq!(
            expr,
            vec![Expr::List(vec![
                Expr::Symbol("+".into()),
                Expr::Number(2),
                Expr::Number(3),
            ])]
        )
    }
}
