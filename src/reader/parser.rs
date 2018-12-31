use std::collections::HashMap;
use std::convert;
use std::fmt;
use std::num;
use std::result;

use itertools::Itertools;

use super::lexer::{Delimiter, Error as LexerError, Result as LexerResult, Token};

pub type Result<T> = result::Result<T, Error>;

const INITIAL_NESTING_DEPTH: usize = 10;

static KEYWORD_CHAR: char = ':';

static NIL_LITERAL: &str = "nil";
static TRUE_LITERAL: &str = "true";
static FALSE_LITERAL: &str = "false";

#[derive(Debug, PartialEq, Hash, Eq)]
pub enum Ast {
    Nil,
    Bool(bool),
    Number(i64),
    String(String),
    Comment(String),
    Symbol(String),
    Keyword(String),
    List(Vec<Ast>),
    Vector(Vec<Ast>),
    Map(Vec<Ast>),
    Set(Vec<Ast>),
}

impl Ast {
    fn fmt_seq<'a>(
        f: &mut fmt::Formatter,
        nodes: impl IntoIterator<Item = &'a Ast>,
        delimiter: Delimiter,
    ) -> fmt::Result {
        write!(f, "{}", delimiter.open_char())?;
        write!(f, "{}", nodes.into_iter().format(" "))?;
        write!(f, "{}", delimiter.close_char())
    }
}

impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Ast::*;

        match self {
            Nil => write!(f, "nil"),
            Bool(b) => write!(f, "{}", b),
            Number(n) => write!(f, "{}", n),
            String(s) => write!(f, r#""{}""#, s),
            Comment(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            Keyword(k) => write!(f, ":{}", k),
            List(nodes) => Ast::fmt_seq(f, nodes, Delimiter::Paren),
            Vector(nodes) => Ast::fmt_seq(f, nodes, Delimiter::Bracket),
            Map(nodes) => Ast::fmt_seq(f, nodes, Delimiter::Brace),
            Set(nodes) => {
                write!(f, "#")?;
                Ast::fmt_seq(f, nodes, Delimiter::Brace)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    /// UnbalancedDelimiter indicates a delimiter that does not match the other delimiter in the pair of Open and Close. Returns an index into the token stream where the imbalance occurs.
    UnbalancedDelimiter(Delimiter, usize),
    UnbalancedString(usize),
    UnrecognizedToken(usize, char),
    MissingPairInMap(Vec<Ast>),
    // ParseIntError(&'a str),
}

impl convert::From<LexerError> for Error {
    fn from(lexer_error: LexerError) -> Self {
        match lexer_error {
            LexerError::UnrecognizedToken(index, ch) => Error::UnrecognizedToken(index, ch),
            LexerError::UnbalancedString(index) => Error::UnbalancedString(index),
            LexerError::Internal => unreachable!(),
        }
    }
}

impl convert::From<num::ParseIntError> for Error {
    fn from(_error: num::ParseIntError) -> Self {
        unimplemented!()
    }
}

#[derive(Debug)]
struct DelimiterCounter {
    count: isize,
    indices: Vec<usize>,
}

impl DelimiterCounter {
    fn new(initial_capacity: usize) -> Self {
        Self {
            count: 0,
            indices: Vec::with_capacity(initial_capacity),
        }
    }
}

pub struct Parser {
    delimiter_nesting: HashMap<Delimiter, DelimiterCounter>,
    token_index: Option<usize>,
}

impl<'a> Parser {
    pub fn new() -> Self {
        let mut delimiter_nesting = HashMap::new();
        delimiter_nesting.insert(
            Delimiter::Paren,
            DelimiterCounter::new(INITIAL_NESTING_DEPTH),
        );
        delimiter_nesting.insert(
            Delimiter::Bracket,
            DelimiterCounter::new(INITIAL_NESTING_DEPTH),
        );
        delimiter_nesting.insert(
            Delimiter::Brace,
            DelimiterCounter::new(INITIAL_NESTING_DEPTH),
        );

        Self {
            delimiter_nesting,
            token_index: None,
        }
    }

    /// parse_tokens takes an `Iterator` over `LexerResult<Token>` and attempts to parse a full AST from them.
    // NOTE: we require a `&mut T` so that we can recurse over the token stream. The borrowing could be simplified with
    // `&mut tokens` but then the compiler hits a recursion limit while attempting to monomorphize the function.
    pub fn parse_tokens<T>(&mut self, tokens: &mut T) -> Result<Vec<Ast>>
    where
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let ast = self.parse_form(tokens)?;

        if let Some((delimiter, index)) = self.outstanding_delimiters() {
            Err(Error::UnbalancedDelimiter(delimiter, index))
        } else {
            Ok(ast)
        }
    }

    pub fn parse_form<T>(&mut self, tokens: &mut T) -> Result<Vec<Ast>>
    where
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let mut nodes = vec![];

        while let Some(result) = tokens.next() {
            self.increment_token_index();

            let token = result?;
            let node = match token {
                Token::Open(Delimiter::Paren) => {
                    self.parse_seq(Delimiter::Paren, Ast::List, tokens.by_ref())?
                }
                Token::Close(Delimiter::Paren) => {
                    self.dec_depth(Delimiter::Paren);
                    break;
                }
                Token::Open(Delimiter::Bracket) => {
                    self.parse_seq(Delimiter::Bracket, Ast::Vector, tokens.by_ref())?
                }
                Token::Close(Delimiter::Bracket) => {
                    self.dec_depth(Delimiter::Bracket);
                    break;
                }
                Token::Open(Delimiter::Brace) => {
                    self.parse_seq(Delimiter::Brace, Ast::Map, tokens.by_ref())?
                }
                Token::Close(Delimiter::Brace) => {
                    self.dec_depth(Delimiter::Brace);
                    break;
                }
                Token::Number(input) => self.parse_number(input)?,
                Token::String(input) => self.parse_string(input)?,
                Token::Comment(input) => self.parse_comment(input)?,
                Token::Symbol(input) => self.parse_symbol(input)?,
                Token::Dispatch => {
                    let node = self.parse_dispatch(tokens.by_ref())?;
                    nodes.push(node);
                    break;
                }
            };

            nodes.push(node)
        }

        Ok(nodes)
    }

    fn increment_token_index(&mut self) {
        if let Some(index) = self.token_index.as_mut() {
            *index += 1;
        } else {
            self.token_index = Some(0);
        }
    }

    // outstanding_delimiters prevents leaking AST nodes
    fn outstanding_delimiters(&mut self) -> Option<(Delimiter, usize)> {
        if let Some((&delimiter, counter)) =
            self.delimiter_nesting.iter_mut().find(|(_, v)| v.count < 0)
        {
            if let Some(index) = counter.indices.pop() {
                Some((delimiter, index))
            } else {
                Some((delimiter, self.token_index.unwrap()))
            }
        } else {
            None
        }
    }

    fn inc_depth(&mut self, delimiter: Delimiter) -> isize {
        let index = self.token_index.unwrap();
        let counter = self.delimiter_nesting.get_mut(&delimiter).unwrap();
        counter.count += 1;
        counter.indices.push(index);
        counter.count
    }

    fn dec_depth(&mut self, delimiter: Delimiter) {
        let counter = self.delimiter_nesting.get_mut(&delimiter).unwrap();
        counter.count -= 1;
    }

    fn get_depth_for(&self, delimiter: Delimiter) -> isize {
        // add one to account for decrement that *should* have occurred
        self.delimiter_nesting[&delimiter].count + 1
    }

    fn get_unbalanced_index_for(&self, delimiter: Delimiter) -> usize {
        *self.delimiter_nesting[&delimiter].indices.last().unwrap()
    }

    fn adjust_depth_indices(&mut self, delimiter: Delimiter) {
        let counter = self.delimiter_nesting.get_mut(&delimiter).unwrap();
        counter.indices.pop();
    }

    fn parse_seq<T, C>(
        &mut self,
        delimiter: Delimiter,
        constructor: C,
        tokens: &mut T,
    ) -> Result<Ast>
    where
        C: Fn(Vec<Ast>) -> Ast,
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let entry_depth = self.inc_depth(delimiter);
        let nodes = self.parse_form(tokens)?;
        let exit_depth = self.get_depth_for(delimiter);

        if entry_depth < exit_depth {
            return Err(Error::UnbalancedDelimiter(
                delimiter,
                self.get_unbalanced_index_for(delimiter),
            ));
        }

        self.adjust_depth_indices(delimiter);
        Ok(constructor(nodes))
    }

    fn parse_number(&mut self, value: &str) -> Result<Ast> {
        let number = value.parse()?;
        Ok(Ast::Number(number))
    }

    fn parse_string(&mut self, value: &str) -> Result<Ast> {
        Ok(Ast::String(value.into()))
    }

    fn parse_comment(&mut self, value: &str) -> Result<Ast> {
        Ok(Ast::Comment(value.into()))
    }

    fn parse_symbol(&mut self, value: &str) -> Result<Ast> {
        match value {
            _sym if _sym == NIL_LITERAL => Ok(Ast::Nil),
            _sym if _sym == TRUE_LITERAL => Ok(Ast::Bool(true)),
            _sym if _sym == FALSE_LITERAL => Ok(Ast::Bool(false)),
            symbol if symbol.starts_with(KEYWORD_CHAR) => {
                Ok(Ast::Keyword(symbol[KEYWORD_CHAR.len_utf8()..].into()))
            }
            symbol => Ok(Ast::Symbol(symbol.into())),
        }
    }

    fn parse_dispatch<T>(&mut self, tokens: &mut T) -> Result<Ast>
    where
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let mut nodes = self.parse_form(tokens)?;
        if nodes.len() != 1 {
            panic!("reader dispatch is not fully implemented")
        }
        let nodes = nodes.pop().unwrap();
        match nodes {
            Ast::Map(nodes) => Ok(Ast::Set(nodes)),
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::lexer::Lexer;
    use super::*;

    fn run_parse(input: &str) -> Result<Vec<Ast>> {
        let mut lexer = Lexer::new(input);

        let mut parser = Parser::new();
        parser.parse_tokens(&mut lexer)
    }

    macro_rules! parse_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected): (&str, Vec<Ast>) = $value;
                    let result = run_parse(input).unwrap();
                    assert_eq!(expected, result);
                }
            )*
        }
    }

    parse_tests! {
        can_parse_empty_input: ("", vec![]),
        can_parse_nil: ("nil", vec![Ast::Nil]),
        can_parse_true: ("true", vec![Ast::Bool(true)]),
        can_parse_false: ("false", vec![Ast::Bool(false)]),
        can_parse_numbers: ("3", vec![Ast::Number(3)]),
        can_parse_numbers_multi: ("3 4 5", vec![
            Ast::Number(3),
            Ast::Number(4),
            Ast::Number(5)
        ]),
        can_parse_empty_string: (r#""""#, vec![Ast::String("".into())]),
        can_parse_strings: (r#""hi, there""#, vec![Ast::String("hi, there".into())]),
        can_parse_symbols: ("+ a b", vec![
            Ast::Symbol("+".into()),
            Ast::Symbol("a".into()),
            Ast::Symbol("b".into())
        ]),
        can_parse_symbols_whitespace: ("hi, there    ", vec![
            Ast::Symbol("hi".into()),
            Ast::Symbol("there".into()),
        ]),
        can_parse_symbols_with_punctuation: ("+ a22 b34- $", vec![
            Ast::Symbol("+".into()),
            Ast::Symbol("a22".into()),
            Ast::Symbol("b34-".into()),
            Ast::Symbol("$".into())
        ]),
        can_parse_special_symbols: ("abc nil true false not-nil true33", vec![
            Ast::Symbol("abc".into()),
            Ast::Nil,
            Ast::Bool(true),
            Ast::Bool(false),
            Ast::Symbol("not-nil".into()),
            Ast::Symbol("true33".into()),
        ]),
        can_parse_keywords: (":a :b :cc :def234 :sdfou--", vec![
            Ast::Keyword("a".into()),
            Ast::Keyword("b".into()),
            Ast::Keyword("cc".into()),
            Ast::Keyword("def234".into()),
            Ast::Keyword("sdfou--".into()),
        ]),
        can_parse_tricky_keywords: (":*() :: :ns/var :nil :true :false", vec![
            Ast::Keyword("*".into()),
            Ast::List(vec![]),
            Ast::Keyword(":".into()),
            Ast::Keyword("ns/var".into()),
            Ast::Keyword("nil".into()),
            Ast::Keyword("true".into()),
            Ast::Keyword("false".into()),
        ]),
        can_parse_empty_list: ("()", vec![Ast::List(vec![])]),
        can_parse_multiple_empty_lists: ("() ()", vec![
            Ast::List(vec![]),
            Ast::List(vec![])
        ]),
        can_parse_list: ("( + 1 2)", vec![
            Ast::List(vec![
            Ast::Symbol("+".into()),
            Ast::Number(1),
            Ast::Number(2)
        ])]),
        can_parse_nested_empty_lists: ("(()) ()", vec![
            Ast::List(vec![
                Ast::List(vec![])
            ]),
            Ast::List(vec![])
        ]),
        can_parse_vector: ("[:a 1 3]", vec![
            Ast::Vector(vec![
                Ast::Keyword("a".into()),
                Ast::Number(1),
                Ast::Number(3)])
        ]),
        can_parse_empty_vector: ("[]", vec![Ast::Vector(vec![])]),
        can_parse_map: ("{:a 1}", vec![
            Ast::Map(vec![
                Ast::Keyword("a".into()),
                Ast::Number(1)])
        ]),
        can_parse_empty_map: ("{}", vec![Ast::Map(vec![])]),
        can_parse_empty_set: ("#{}", vec![Ast::Set(vec![])]),
        can_parse_set: ("#{1 2}", vec![
            Ast::Set(vec![
                Ast::Number(1),
                Ast::Number(2)
            ])
        ]),
        can_parse_expr_example: ("(first {:args #{:a :b}})", vec![
            Ast::List(vec![
                Ast::Symbol("first".into()),
                Ast::Map(vec![
                    Ast::Keyword("args".into()),
                    Ast::Set(vec![
                        Ast::Keyword("a".into()),
                        Ast::Keyword("b".into()),
                    ])
                ])
            ])
        ]),
        can_parse_with_set: (r#"(reduce (fn-with-meta #{:a :b}))"#, vec![
            Ast::List(vec![
                Ast::Symbol("reduce".into()),
                Ast::List(vec![
                    Ast::Symbol("fn-with-meta".into()),
                    Ast::Set(vec![
                        Ast::Keyword("a".into()),
                        Ast::Keyword("b".into()),
                    ])
                ]),
            ])
        ]),
        can_parse_nested_lists_and_map: ("(({})) ;; hi", vec![
            Ast::List(vec![
                Ast::List(vec![Ast::Map(vec![])])]),
            Ast::Comment("; hi".into()),
        ]),
        can_parse_nested_lists_and_set: ("((#{})) ;; hi", vec![
            Ast::List(vec![
                Ast::List(vec![Ast::Set(vec![])])]),
            Ast::Comment("; hi".into()),
        ]),
        can_parse_expr: (r#"
                              (reduce (fn-with-meta
                                        {:docs "add two numbers"
                                         :args #{:a :b}}
                                        [a b]
                                          (+ a b)) (range 10 2)) ;; find a sum
                         "#, vec![
                             Ast::List(vec![
                                 Ast::Symbol("reduce".into()),
                                 Ast::List(vec![
                                     Ast::Symbol("fn-with-meta".into()),
                                     Ast::Map(vec![
                                         Ast::Keyword("docs".into()),
                                         Ast::String("add two numbers".into()),
                                         Ast::Keyword("args".into()),
                                         Ast::Set(vec![
                                             Ast::Keyword("a".into()),
                                             Ast::Keyword("b".into()),
                                         ])
                                     ]),
                                     Ast::Vector(vec![
                                         Ast::Symbol("a".into()),
                                         Ast::Symbol("b".into())
                                     ]),
                                     Ast::List(vec![
                                         Ast::Symbol("+".into()),
                                         Ast::Symbol("a".into()),
                                         Ast::Symbol("b".into())
                                     ])
                                 ]),
                                 Ast::List(vec![
                                     Ast::Symbol("range".into()),
                                     Ast::Number(10),
                                     Ast::Number(2),
                                 ])
                             ]),
                             Ast::Comment("; find a sum".into())
                         ]),
    }

    #[test]
    fn can_parse_unbalanced_string() {
        let input = r#"  "hi, there"#;
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedString(2)));
    }

    #[test]
    fn can_parse_unbalanced_lists() {
        let input = "(";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 0)));

        let input = ")";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 0)));

        let input = "hi there)";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 2)));

        let input = "hi there) foo bar";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 2)));

        let input = "hi(";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 1)));

        let input = "hi())";
        let result = run_parse(input);
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 3)));

        let input = "hi(((((((((()))))))))))";
        let result = run_parse(input);
        assert_eq!(
            result,
            Err(Error::UnbalancedDelimiter(Delimiter::Paren, 21))
        );
    }

    #[test]
    fn can_parse_unbalanced_vectors() {
        let input = "[ 1 2 []";
        let result = run_parse(input);
        assert_eq!(
            result,
            Err(Error::UnbalancedDelimiter(Delimiter::Bracket, 0))
        );

        let input = "][ 1 2 []";
        let result = run_parse(input);
        assert_eq!(
            result,
            Err(Error::UnbalancedDelimiter(Delimiter::Bracket, 0))
        );
    }

    #[test]
    fn can_parse_unbalanced_maps() {
        let input = "{:a 1";
        let result = run_parse(input);
        assert_eq!(Err(Error::UnbalancedDelimiter(Delimiter::Brace, 0)), result);

        let input = "}:a 1}";
        let result = run_parse(input);
        assert_eq!(Err(Error::UnbalancedDelimiter(Delimiter::Brace, 0)), result);
    }
}
