use std::iter;
use std::result;
use std::str;

/// Result binds the std::result::Result::Err type to this module's error type.
pub type Result<T> = result::Result<T, LexerError>;

/// lex is a convenience function to take some `input`and produce the resulting `Vec<Token>`.
pub fn lex(input: &str) -> Result<Vec<Token>> {
    let lexer = Lexer::new(input);
    lexer.into_iter().collect::<result::Result<Vec<_>, _>>()
}

// Lexer contains the logic to lex individual tokens from the input source.
#[derive(Debug)]
pub struct Lexer<'input> {
    input: str::Chars<'input>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            input: input.chars(),
        }
    }

    /// advance_if advances the state of the lexer if the resulting tokens satisfy the `predicate`.
    fn advance_if<P>(&mut self, predicate: P)
    where
        P: Fn(char) -> bool,
    {
        while self.peek().map_or(false, &predicate) {
            self.consume();
        }
    }

    /// consume advances the state of the lexer to the next char, yielding an Option of the current char from the input source
    fn consume(&mut self) -> Option<char> {
        self.input.next()
    }

    /// peek returns an Option of the next char in the input source without consuming it
    fn peek(&self) -> Option<char> {
        self.input.clone().next()
    }

    fn take_while<P>(&mut self, predicate: P) -> &str
    where
        P: Fn(char) -> bool,
    {
        let input = self.input.as_str();
        self.advance_if(predicate);
        &input[..input.len() - self.input.as_str().len()]
    }
}

// NOTE: refer https://users.rust-lang.org/t/takewhile-iterator-over-chars-to-string-slice/11014
// main idea is that `std::str::Chars::clone()` is not that expensive to clone
impl<'input> iter::Iterator for Lexer<'input> {
    type Item = Result<Token<'input>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance_if(|ch| ch.is_whitespace());

        let next_token = match self.peek() {
            None => return None,
            Some('(') => {
                self.input.next();
                Ok(Token::OpenParen)
            }
            Some(')') => {
                self.input.next();
                Ok(Token::CloseParen)
            }
            Some(ch) if ch.is_numeric() => {
                let value = self.take_while(|ch| ch.is_numeric());
                Ok(Token::Number(value))
            }
            // NOTE: if the other match arms do their job in terms of managing complete UTF-8 strings, then we should not get here; we keep this arm in case we do.
            _ => Err(LexerError::UnrecognizedToken(333)),
        };
        Some(next_token)
    }
}

#[derive(Debug, PartialEq)]
/// LexerError represents an error the lexer encountered while lexing.
pub enum LexerError {
    /// UnrecognizedToken represents some character in the input source that the lexer does not understand; wraps the index into the input source that points to the unrecognizeable character.
    // TODO make a span?
    UnrecognizedToken(usize),
}

#[derive(Debug, PartialEq)]
/// Token represents an atomic component of this language's syntax.
pub enum Token<'input> {
    OpenParen,
    CloseParen,
    Number(&'input str),
    Symbol(&'input str),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_lex_parens() {
        let input = "()";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(tokens, vec![Token::OpenParen, Token::CloseParen]);

        let input = "   ()";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(tokens, vec![Token::OpenParen, Token::CloseParen]);

        let input = "   ()  ";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(tokens, vec![Token::OpenParen, Token::CloseParen]);

        let input = "   ()  )";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(
            tokens,
            vec![Token::OpenParen, Token::CloseParen, Token::CloseParen]
        );

        let input = "((()))";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::OpenParen,
                Token::OpenParen,
                Token::OpenParen,
                Token::CloseParen,
                Token::CloseParen,
                Token::CloseParen
            ]
        );

        let input = "((()))))";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::OpenParen,
                Token::OpenParen,
                Token::OpenParen,
                Token::CloseParen,
                Token::CloseParen,
                Token::CloseParen,
                Token::CloseParen,
                Token::CloseParen
            ]
        );
    }

    #[test]
    fn can_lex_numbers() {
        let input = "2";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(tokens, vec![Token::Number(&input)]);

        let input = "233      ";
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(tokens, vec![Token::Number(&input.trim())]);

        let input = "(    233 ))       ";
        let i = input.find("233").unwrap();
        let j = i + 3;
        let number = &input[i..j];
        let lexer = Lexer::new(input);
        let tokens = lexer.into_iter().collect::<Result<Vec<_>>>().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::OpenParen,
                Token::Number(number),
                Token::CloseParen,
                Token::CloseParen,
            ]
        );
    }
}
