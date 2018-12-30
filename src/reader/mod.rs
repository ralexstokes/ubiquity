mod lexer;
mod parser;

use self::lexer::Lexer;
use self::parser::{Parser, Result};

pub use self::parser::Ast;

pub use self::lexer::lex;

pub fn read(input: &str) -> Result<Vec<Ast>> {
    let mut lexer = Lexer::new(input);

    let mut parser = Parser::new();
    parser.parse_tokens(&mut lexer)
}

#[cfg(test)]
mod tests {
    use super::parser::Ast;
    use super::*;

    #[test]
    fn can_read_expr() {
        let input = "(+ 2 3)";
        let expr = read(input).unwrap();
        assert_eq!(
            expr,
            vec![Ast::List(vec![
                Ast::Symbol("+".into()),
                Ast::Number(2),
                Ast::Number(3),
            ])]
        )
    }
}
