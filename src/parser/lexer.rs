use std::iter;
use std::result;
use std::str;

/// Result binds the std::result::Result::Err type to this module's error type.
pub type Result<'a, T> = result::Result<T, LexerError<'a>>;

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

const COMMENT_CHAR: char = ';';
const STRING_CHAR: char = '"';
const NEWLINE_CHAR: char = '\n';

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

    /// take_while advances the input while `predicate` is true and then returns a str slice of the traversed span.
    fn take_while<P>(&mut self, predicate: P) -> &'input str
    where
        P: Fn(char) -> bool,
    {
        let input = self.input.as_str();
        self.advance_if(predicate);
        &input[..input.len() - self.input.as_str().len()]
    }

    fn drain(&self) -> &'input str {
        self.input.as_str()
    }

    fn consume_delimiter<T>(
        &mut self,
        token: T,
        delimiter: Delimiter,
    ) -> Result<'input, Token<'input>>
    where
        T: Fn(Delimiter) -> Token<'input>,
    {
        self.consume();
        Ok(token(delimiter))
    }

    fn consume_numeric(&mut self) -> Result<'input, Token<'input>> {
        let value = self.take_while(|ch| ch.is_numeric());
        Ok(Token::Number(value))
    }

    fn consume_string(&mut self) -> Result<'input, Token<'input>> {
        self.consume();
        let value = self.take_while(|ch| ch != STRING_CHAR);
        self.consume();
        Ok(Token::String(value))
    }

    fn consume_comment(&mut self) -> Result<'input, Token<'input>> {
        self.consume();
        let value = self.take_while(|ch| ch != NEWLINE_CHAR);
        Ok(Token::Comment(value))
    }

    fn is_symbolic(ch: char) -> bool {
        if ch.is_whitespace() {
            false
        } else if ch.is_control() {
            false
        } else {
            true
        }
    }

    fn consume_symbol(&mut self) -> Result<'input, Token<'input>> {
        let value = self.take_while(Lexer::is_symbolic);
        Ok(Token::Symbol(value))
    }
}

// NOTE: refer https://users.rust-lang.org/t/takewhile-iterator-over-chars-to-string-slice/11014
// main idea is that `std::str::Chars::clone()` is not that expensive to clone
impl<'a> iter::Iterator for Lexer<'a> {
    type Item = Result<'a, Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance_if(|ch| ch.is_whitespace());

        let next_token = match self.peek() {
            None => return None,
            Some('(') => self.consume_delimiter(Token::Open, Delimiter::Paren),
            Some(')') => self.consume_delimiter(Token::Close, Delimiter::Paren),
            Some('[') => self.consume_delimiter(Token::Open, Delimiter::Bracket),
            Some(']') => self.consume_delimiter(Token::Close, Delimiter::Bracket),
            Some('{') => self.consume_delimiter(Token::Open, Delimiter::Brace),
            Some('}') => self.consume_delimiter(Token::Close, Delimiter::Brace),
            Some(ch) if ch.is_numeric() => self.consume_numeric(),
            Some(STRING_CHAR) => self.consume_string(),
            Some(COMMENT_CHAR) => self.consume_comment(),
            Some(ch) if Lexer::is_symbolic(ch) => self.consume_symbol(),
            _ => Err(LexerError::UnrecognizedToken(self.drain())),
        };
        Some(next_token)
    }
}

#[derive(Debug, PartialEq)]
/// LexerError represents an error the lexer encountered while lexing.
pub enum LexerError<'input> {
    /// UnrecognizedToken represents part of the input stream that could not be correctly lexed
    UnrecognizedToken(&'input str),
}

#[derive(Debug, PartialEq)]
/// Token represents an atomic component of this language's syntax.
pub enum Token<'input> {
    Open(Delimiter),
    Close(Delimiter),
    Number(&'input str),
    String(&'input str),
    Comment(&'input str),
    Symbol(&'input str),
}

#[derive(Debug, PartialEq)]
pub enum Delimiter {
    Paren,
    Bracket,
    Brace,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_lex_test(input: &str, expected_tokens: Vec<Token>) {
        let tokens = lex(input).unwrap();
        assert_eq!(tokens, expected_tokens);
    }

    #[test]
    fn can_lex_parens() {
        let input = "()";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "   ()";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "   ()  ";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "   ()  )";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "((()))";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "((()))))";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_delimiters() {
        let input = "([{{])";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Bracket),
            Token::Open(Delimiter::Brace),
            Token::Open(Delimiter::Brace),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "  2  ([{{]) 222";
        let expected_tokens = vec![
            Token::Number("2"),
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Bracket),
            Token::Open(Delimiter::Brace),
            Token::Open(Delimiter::Brace),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Paren),
            Token::Number("222"),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_numbers() {
        let input = "2";
        let expected_tokens = vec![Token::Number(&input)];
        run_lex_test(input, expected_tokens);

        let input = "233      ";
        let expected_tokens = vec![Token::Number(&input.trim())];
        run_lex_test(input, expected_tokens);

        let input = "(    233 ))       ";
        let i = input.find("233").unwrap();
        let j = i + 3;
        let number = &input[i..j];
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Number(number),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_strings() {
        let input = r#""hi there""#;
        let expected_tokens = vec![Token::String("hi there")];
        run_lex_test(input, expected_tokens);

        let input = r#"()"hi there"]]"#;
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::String("hi there"),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Bracket),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_comments() {
        let input = "233     ; abcdef";
        let expected_tokens = vec![Token::Number("233"), Token::Comment(" abcdef")];
        run_lex_test(input, expected_tokens);

        let input = "233     ; ; ;;abcdef";
        let expected_tokens = vec![Token::Number("233"), Token::Comment(" ; ;;abcdef")];
        run_lex_test(input, expected_tokens);

        let input = "233     ; abcdef\n123 456() ; hi";
        let expected_tokens = vec![
            Token::Number("233"),
            Token::Comment(" abcdef"),
            Token::Number("123"),
            Token::Number("456"),
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::Comment(" hi"),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_symbols() {
        let input = "abcdef";
        let expected_tokens = vec![Token::Symbol("abcdef")];
        run_lex_test(input, expected_tokens);

        let input = "a123";
        let expected_tokens = vec![Token::Symbol("a123")];
        run_lex_test(input, expected_tokens);

        let input = "+ abc 123";
        let expected_tokens = vec![
            Token::Symbol("+"),
            Token::Symbol("abc"),
            Token::Number("123"),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_expressions() {
        let input = "(+ 2 2)";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Symbol("+"),
            Token::Number("2"),
            Token::Number("2"),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens)
    }
}
