use std::collections::HashSet;
use std::iter;
use std::result;
use std::str;

use lazy_static::lazy_static;

const OPEN_PAREN: char = '(';
const CLOSE_PAREN: char = ')';
const OPEN_BRACKET: char = '[';
const CLOSE_BRACKET: char = ']';
const OPEN_BRACE: char = '{';
const CLOSE_BRACE: char = '}';
const COMMENT_CHAR: char = ';';
const STRING_CHAR: char = '"';
const NEWLINE_CHAR: char = '\n';
const DISPATCH_CHAR: char = '#';
const QUOTE_CHAR: char = '\'';

lazy_static! {
    /// SPECIAL_CHARS are characters indicative of a non-symbolic atom
    static ref SPECIAL_CHARS: HashSet<char> = {
        let mut set = HashSet::new();

        set.insert(OPEN_PAREN);
        set.insert(CLOSE_PAREN);
        set.insert(OPEN_BRACKET);
        set.insert(CLOSE_BRACKET);
        set.insert(OPEN_BRACE);
        set.insert(CLOSE_BRACE);
        set.insert(COMMENT_CHAR);
        set.insert(STRING_CHAR);
        set.insert(NEWLINE_CHAR);

        set
    };
}

/// Result binds the std::result::Result::Err type to this module's error type.
pub type Result<T> = result::Result<T, Error>;

/// lex is a convenience function to take some `input`and produce the resulting `Vec<Token>`.
pub fn lex(input: &str) -> Result<Vec<Token>> {
    Lexer::new(input).tokens()
}

#[derive(Debug, PartialEq)]
/// Error represents an error the lexer encountered while lexing.
pub enum Error {
    /// UnrecognizedToken points to the byte in the input stream where an unrecognized token was found
    UnrecognizedToken(usize, char),
    /// UnbalancedString points to the byte in the input stream where an unbalanced string began
    UnbalancedString(usize),
    // Internal represents a bug in the internal consistency of this module's logic.
    // An example is where we know a subsequent lex will succeed for some syntactic category due to checking with `peek` but still need an Option for other failable lexes.
    Internal,
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
    Dispatch,
    Quote,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Delimiter {
    Paren,   // ()
    Bracket, // []
    Brace,   // {}
}

impl Delimiter {
    pub fn open_char(self) -> char {
        use self::Delimiter::*;

        match self {
            Paren => OPEN_PAREN,
            Bracket => OPEN_BRACKET,
            Brace => OPEN_BRACE,
        }
    }

    pub fn close_char(self) -> char {
        use self::Delimiter::*;

        match self {
            Paren => CLOSE_PAREN,
            Bracket => CLOSE_BRACKET,
            Brace => CLOSE_BRACE,
        }
    }
}

/// Lexer contains the logic to lex individual tokens from the input source.
#[derive(Debug)]
pub struct Lexer<'input> {
    input: &'input str,
    iter: iter::Peekable<str::CharIndices<'input>>,
}

impl<'input> Lexer<'input> {
    /// new constructs a Lexer instance from the input but does not do any lexing.
    pub fn new(input: &'input str) -> Self {
        Self {
            input,
            iter: input.char_indices().peekable(),
        }
    }

    /// tokens is a convenience method that returns the tokens lexed from the input stream.
    fn tokens(self) -> Result<Vec<Token<'input>>> {
        self.collect::<result::Result<Vec<_>, _>>()
    }

    /// advance_if advances the state of the lexer if the resulting tokens satisfy the `predicate`. Returns Some(span) in the `input` that was advanced over; returns None if such a span cannot be generated (e.g. because we ran out of more input chars).
    fn advance_if<P>(&mut self, predicate: P) -> Option<(usize, usize)>
    where
        P: Fn(char) -> bool,
    {
        let start = match self.peek() {
            Some(&(_, ch)) if predicate(ch) => self.consume().map(|(index, _)| index).unwrap(),
            _ => return None,
        };
        let mut end = start;

        while self.peek().map_or(false, |&(_, ch)| predicate(ch)) {
            end = self.consume().map(|(index, _)| index).unwrap()
        }

        Some((start, end))
    }

    /// consume advances the state of the lexer to the next char, yielding an Option of the current char from the input source
    fn consume(&mut self) -> Option<(usize, char)> {
        self.iter.next()
    }

    /// peek returns the next element in the iterator without consuming it
    fn peek(&mut self) -> Option<&(usize, char)> {
        self.iter.peek()
    }

    /// take_while advances the input while `predicate` is true and then returns a str slice of the traversed span.
    fn take_while<P>(&mut self, predicate: P) -> Option<&'input str>
    where
        P: Fn(char) -> bool,
    {
        self.advance_if(predicate)
            .map(|(start, finish)| &self.input[start..=finish])
    }

    fn consume_delimiter<T>(&mut self, token: T, delimiter: Delimiter) -> Result<Token<'input>>
    where
        T: Fn(Delimiter) -> Token<'input>,
    {
        self.consume();
        Ok(token(delimiter))
    }

    fn is_numeric(ch: char) -> bool {
        ch.is_numeric()
    }

    fn consume_numeric(&mut self) -> Result<Token<'input>> {
        self.take_while(Lexer::is_numeric)
            .map(Token::Number)
            .ok_or(Error::Internal)
    }

    // use a naive test to lex a string literal
    // ... just to the next `STRING_CHAR`
    fn is_string_literal(ch: char) -> bool {
        ch != STRING_CHAR
    }

    fn consume_string(&mut self) -> Result<Token<'input>> {
        let (start, _) = self.consume().unwrap();
        match self.take_while(Lexer::is_string_literal) {
            Some(value) => match self.peek() {
                Some(&(_, ch)) if ch == STRING_CHAR => {
                    self.consume();
                    Ok(Token::String(value))
                }
                _ => Err(Error::UnbalancedString(start)),
            },
            None => match self.peek() {
                Some(&(end, ch)) if ch == STRING_CHAR => {
                    self.consume();
                    let start = start + STRING_CHAR.len_utf8();
                    Ok(Token::String(&self.input[start..end]))
                }
                _ => Err(Error::UnbalancedString(start)),
            },
        }
    }

    fn consume_comment(&mut self) -> Result<Token<'input>> {
        self.consume();
        self.take_while(|ch| ch != NEWLINE_CHAR)
            .map(Token::Comment)
            .ok_or(Error::Internal)
    }

    fn is_symbolic(ch: char) -> bool {
        (ch.is_alphanumeric() || ch.is_ascii_punctuation())
            && !SPECIAL_CHARS.contains(&ch)
            && !Lexer::is_whitespace(ch)
    }

    fn consume_symbol(&mut self) -> Result<Token<'input>> {
        self.take_while(Lexer::is_symbolic)
            .map(Token::Symbol)
            .ok_or(Error::Internal)
    }

    fn is_whitespace(ch: char) -> bool {
        ch.is_whitespace() || ch == ','
    }

    fn consume_dispatch(&mut self) -> Result<Token<'input>> {
        self.consume()
            .map(|_| Token::Dispatch)
            .ok_or(Error::Internal)
    }

    fn consume_quote(&mut self) -> Result<Token<'input>> {
        self.consume().map(|_| Token::Quote).ok_or(Error::Internal)
    }
}

impl<'a> iter::Iterator for Lexer<'a> {
    type Item = Result<Token<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance_if(Lexer::is_whitespace);

        let next_token = match self.peek() {
            None => return None,
            // The order is important here
            Some(&(_, DISPATCH_CHAR)) => self.consume_dispatch(),
            Some(&(_, QUOTE_CHAR)) => self.consume_quote(),
            Some(&(_, OPEN_PAREN)) => self.consume_delimiter(Token::Open, Delimiter::Paren),
            Some(&(_, CLOSE_PAREN)) => self.consume_delimiter(Token::Close, Delimiter::Paren),
            Some(&(_, OPEN_BRACKET)) => self.consume_delimiter(Token::Open, Delimiter::Bracket),
            Some(&(_, CLOSE_BRACKET)) => self.consume_delimiter(Token::Close, Delimiter::Bracket),
            Some(&(_, OPEN_BRACE)) => self.consume_delimiter(Token::Open, Delimiter::Brace),
            Some(&(_, CLOSE_BRACE)) => self.consume_delimiter(Token::Close, Delimiter::Brace),
            Some(&(_, ch)) if Lexer::is_numeric(ch) => self.consume_numeric(),
            Some(&(_, STRING_CHAR)) => self.consume_string(),
            Some(&(_, COMMENT_CHAR)) => self.consume_comment(),
            Some(&(_, ch)) if Lexer::is_symbolic(ch) => self.consume_symbol(),
            Some(&(index, ch)) => Err(Error::UnrecognizedToken(index, ch)),
        };
        Some(next_token)
    }
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

        let input = "233abc";
        let expected_tokens = vec![Token::Number("233"), Token::Symbol("abc")];
        run_lex_test(input, expected_tokens);

        let input = "233;; abc";
        let expected_tokens = vec![Token::Number("233"), Token::Comment("; abc")];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_strings() {
        let input = r#""hi there""#;
        let expected_tokens = vec![Token::String("hi there")];
        run_lex_test(input, expected_tokens);

        let input = r#""""#;
        let expected_tokens = vec![Token::String("")];
        run_lex_test(input, expected_tokens);

        let input = r#""hi there" "hello world" "#;
        let expected_tokens = vec![Token::String("hi there"), Token::String("hello world")];
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

        let input = r#"()"hi, there"]]"#;
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::String("hi, there"),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Bracket),
        ];
        run_lex_test(input, expected_tokens);

        let input = r#"()"hi, there"123]]"#;
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
            Token::String("hi, there"),
            Token::Number("123"),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Bracket),
        ];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_find_unbalanced_string() {
        let input = r#"""#;
        let result = lex(input);
        assert_eq!(result, Err(Error::UnbalancedString(0)));

        let input = r#""hi there"#;
        let result = lex(input);
        assert_eq!(result, Err(Error::UnbalancedString(0)));

        let input = r#" " hello world"#;
        let result = lex(input);
        assert_eq!(result, Err(Error::UnbalancedString(1)));

        let input = r#" hello there" hello world"#;
        let result = lex(input);
        assert_eq!(result, Err(Error::UnbalancedString(12)));

        let input = r#" hello there " hello world"#;
        let result = lex(input);
        assert_eq!(result, Err(Error::UnbalancedString(13)));
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

        let input = "hi, there";
        let expected_tokens = vec![Token::Symbol("hi"), Token::Symbol("there")];
        run_lex_test(input, expected_tokens);

        let input = "+ abc 123";
        let expected_tokens = vec![
            Token::Symbol("+"),
            Token::Symbol("abc"),
            Token::Number("123"),
        ];
        run_lex_test(input, expected_tokens);

        let input = "these are some symbols);; and a comment";
        let expected_tokens = vec![
            Token::Symbol("these"),
            Token::Symbol("are"),
            Token::Symbol("some"),
            Token::Symbol("symbols"),
            Token::Close(Delimiter::Paren),
            Token::Comment("; and a comment"),
        ];
        run_lex_test(input, expected_tokens);

        let input = "these are some symbols;; and a comment";
        let expected_tokens = vec![
            Token::Symbol("these"),
            Token::Symbol("are"),
            Token::Symbol("some"),
            Token::Symbol("symbols"),
            Token::Comment("; and a comment"),
        ];
        run_lex_test(input, expected_tokens);

        let input = ":a";
        let expected_tokens = vec![Token::Symbol(":a")];
        run_lex_test(input, expected_tokens);

        let input = "#:a";
        let expected_tokens = vec![Token::Dispatch, Token::Symbol(":a")];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_dispatch() {
        let input = "#";
        let expected_tokens = vec![Token::Dispatch];
        run_lex_test(input, expected_tokens);

        let input = "((#{}))";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Open(Delimiter::Paren),
            Token::Dispatch,
            Token::Open(Delimiter::Brace),
            Token::Close(Delimiter::Brace),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
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
        run_lex_test(input, expected_tokens);

        let input = "(+ 2 2); (/ 1 0)\n (+ 2 3))";
        let expected_tokens = vec![
            Token::Open(Delimiter::Paren),
            Token::Symbol("+"),
            Token::Number("2"),
            Token::Number("2"),
            Token::Close(Delimiter::Paren),
            Token::Comment(" (/ 1 0)"),
            Token::Open(Delimiter::Paren),
            Token::Symbol("+"),
            Token::Number("2"),
            Token::Number("3"),
            Token::Close(Delimiter::Paren),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "";
        let expected_tokens = vec![];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    fn can_lex_quotes() {
        let input = "'(1 2)";
        let expected_tokens = vec![
            Token::Quote,
            Token::Open(Delimiter::Paren),
            Token::Number("1"),
            Token::Number("2"),
            Token::Close(Delimiter::Paren),
        ];
        run_lex_test(input, expected_tokens);

        let input = "hi'";
        let expected_tokens = vec![Token::Symbol("hi'".into())];
        run_lex_test(input, expected_tokens);
    }

    #[test]
    // tests that the lexer can find:
    // U+009C, STRING TERMINATOR,
    // a control character given in the Rust docs for `char.is_control`
    fn can_find_control_character() {
        let mut input = String::from("made with ");
        let remainder = " and some text";
        let ch = std::char::from_u32(0x9c).unwrap();
        input.push(ch);
        input.push_str(remainder);
        let index = input.find(ch).unwrap();

        let result = lex(&input);
        let mut unrecognized = String::new();
        unrecognized.push(ch);
        unrecognized.push_str(remainder);

        assert_eq!(result, Err(Error::UnrecognizedToken(index, ch)));
    }
}
