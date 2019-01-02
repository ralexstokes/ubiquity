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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr {
    Nil,
    Bool(bool),
    Number(i64),
    String(String),
    Comment(String),
    Symbol(String),
    Keyword(String),
    List(Vec<Expr>),
    Vector(Vec<Expr>),
    Map(Vec<Expr>),
    Set(Vec<Expr>),
    Fn(FnDecl),
    PrimitiveFn(HostFn),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FnDecl {
    pub params: Vec<Expr>,
    pub body: Vec<Expr>,
}

pub type HostFn = fn(Vec<Expr>) -> Result<Expr>;

impl Expr {
    fn fmt_seq<'a>(
        f: &mut fmt::Formatter,
        nodes: impl IntoIterator<Item = &'a Expr>,
        delimiter: Delimiter,
    ) -> fmt::Result {
        write!(f, "{}", delimiter.open_char())?;
        write!(f, "{}", nodes.into_iter().format(" "))?;
        write!(f, "{}", delimiter.close_char())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Expr::*;

        match self {
            Nil => write!(f, "nil"),
            Bool(b) => write!(f, "{}", b),
            Number(n) => write!(f, "{}", n),
            String(s) => write!(f, r#""{}""#, s),
            Comment(c) => write!(f, "{}", c),
            Symbol(s) => write!(f, "{}", s),
            Keyword(k) => write!(f, ":{}", k),
            List(nodes) => Expr::fmt_seq(f, nodes, Delimiter::Paren),
            Vector(nodes) => Expr::fmt_seq(f, nodes, Delimiter::Bracket),
            Map(nodes) => Expr::fmt_seq(f, nodes, Delimiter::Brace),
            Set(nodes) => {
                write!(f, "#")?;
                Expr::fmt_seq(f, nodes, Delimiter::Brace)
            }
            Fn(FnDecl { params, body }) => {
                write!(f, "(fn* [")?;
                write!(f, "{}] ", params.iter().format(" "))?;
                write!(f, "{}", body.iter().format(" "))?;
                write!(f, ")")
            }
            PrimitiveFn(host_fn) => write!(f, "{:?}", host_fn),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    /// UnbalancedDelimiter indicates a delimiter that does not match the other delimiter in the pair of Open and Close. Returns an index into the token stream where the imbalance occurs.
    UnbalancedDelimiter(Delimiter, usize),
    UnbalancedString(usize),
    UnrecognizedToken(usize, char),
    MissingPairInMap(Vec<Expr>),
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
    pub fn parse_tokens<T>(&mut self, tokens: &mut T) -> Result<Vec<Expr>>
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

    pub fn parse_form<T>(&mut self, tokens: &mut T) -> Result<Vec<Expr>>
    where
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let mut nodes = vec![];

        while let Some(result) = tokens.next() {
            self.increment_token_index();

            let token = result?;
            let node = match token {
                Token::Open(Delimiter::Paren) => {
                    self.parse_seq(Delimiter::Paren, Expr::List, tokens.by_ref())?
                }
                Token::Close(Delimiter::Paren) => {
                    self.dec_depth(Delimiter::Paren);
                    break;
                }
                Token::Open(Delimiter::Bracket) => {
                    self.parse_seq(Delimiter::Bracket, Expr::Vector, tokens.by_ref())?
                }
                Token::Close(Delimiter::Bracket) => {
                    self.dec_depth(Delimiter::Bracket);
                    break;
                }
                Token::Open(Delimiter::Brace) => {
                    self.parse_seq(Delimiter::Brace, Expr::Map, tokens.by_ref())?
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
        if let Some((&delimiter, _)) = self.delimiter_nesting.iter().find(|(_, v)| v.count < 0) {
            Some((delimiter, self.token_index.unwrap()))
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
    ) -> Result<Expr>
    where
        C: Fn(Vec<Expr>) -> Expr,
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

    fn parse_number(&mut self, value: &str) -> Result<Expr> {
        let number = value.parse()?;
        Ok(Expr::Number(number))
    }

    fn parse_string(&mut self, value: &str) -> Result<Expr> {
        Ok(Expr::String(value.into()))
    }

    fn parse_comment(&mut self, value: &str) -> Result<Expr> {
        Ok(Expr::Comment(value.into()))
    }

    fn parse_symbol(&mut self, value: &str) -> Result<Expr> {
        match value {
            _sym if _sym == NIL_LITERAL => Ok(Expr::Nil),
            _sym if _sym == TRUE_LITERAL => Ok(Expr::Bool(true)),
            _sym if _sym == FALSE_LITERAL => Ok(Expr::Bool(false)),
            symbol if symbol.starts_with(KEYWORD_CHAR) => {
                Ok(Expr::Keyword(symbol[KEYWORD_CHAR.len_utf8()..].into()))
            }
            symbol => Ok(Expr::Symbol(symbol.into())),
        }
    }

    fn parse_dispatch<T>(&mut self, tokens: &mut T) -> Result<Expr>
    where
        T: Iterator<Item = LexerResult<Token<'a>>>,
    {
        let mut nodes = self.parse_form(tokens)?;
        if nodes.len() != 1 {
            panic!("reader dispatch is not fully implemented")
        }
        let nodes = nodes.pop().unwrap();
        match nodes {
            Expr::Map(nodes) => Ok(Expr::Set(nodes)),
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::lexer::Lexer;
    use super::*;

    fn run_parse(input: &str) -> Result<Vec<Expr>> {
        let mut lexer = Lexer::new(input);

        let mut parser = Parser::new();
        parser.parse_tokens(&mut lexer)
    }

    macro_rules! parse_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected): (&str, Vec<Expr>) = $value;
                    let result = run_parse(input).unwrap();
                    assert_eq!(expected, result);
                }
            )*
        }
    }

    parse_tests! {
        can_parse_empty_input: ("", vec![]),
        can_parse_nil: ("nil", vec![Expr::Nil]),
        can_parse_true: ("true", vec![Expr::Bool(true)]),
        can_parse_false: ("false", vec![Expr::Bool(false)]),
        can_parse_numbers: ("3", vec![Expr::Number(3)]),
        can_parse_numbers_multi: ("3 4 5", vec![
            Expr::Number(3),
            Expr::Number(4),
            Expr::Number(5)
        ]),
        can_parse_empty_string: (r#""""#, vec![Expr::String("".into())]),
        can_parse_strings: (r#""hi, there""#, vec![Expr::String("hi, there".into())]),
        can_parse_symbols: ("+ a b", vec![
            Expr::Symbol("+".into()),
            Expr::Symbol("a".into()),
            Expr::Symbol("b".into())
        ]),
        can_parse_symbols_whitespace: ("hi, there    ", vec![
            Expr::Symbol("hi".into()),
            Expr::Symbol("there".into()),
        ]),
        can_parse_symbols_with_punctuation: ("+ a22 b34- $", vec![
            Expr::Symbol("+".into()),
            Expr::Symbol("a22".into()),
            Expr::Symbol("b34-".into()),
            Expr::Symbol("$".into())
        ]),
        can_parse_special_symbols: ("abc nil true false not-nil true33", vec![
            Expr::Symbol("abc".into()),
            Expr::Nil,
            Expr::Bool(true),
            Expr::Bool(false),
            Expr::Symbol("not-nil".into()),
            Expr::Symbol("true33".into()),
        ]),
        can_parse_keywords: (":a :b :cc :def234 :sdfou--", vec![
            Expr::Keyword("a".into()),
            Expr::Keyword("b".into()),
            Expr::Keyword("cc".into()),
            Expr::Keyword("def234".into()),
            Expr::Keyword("sdfou--".into()),
        ]),
        can_parse_tricky_keywords: (":*() :: :ns/var :nil :true :false", vec![
            Expr::Keyword("*".into()),
            Expr::List(vec![]),
            Expr::Keyword(":".into()),
            Expr::Keyword("ns/var".into()),
            Expr::Keyword("nil".into()),
            Expr::Keyword("true".into()),
            Expr::Keyword("false".into()),
        ]),
        can_parse_empty_list: ("()", vec![Expr::List(vec![])]),
        can_parse_multiple_empty_lists: ("() ()", vec![
            Expr::List(vec![]),
            Expr::List(vec![])
        ]),
        can_parse_list: ("( + 1 2)", vec![
            Expr::List(vec![
            Expr::Symbol("+".into()),
            Expr::Number(1),
            Expr::Number(2)
        ])]),
        can_parse_nested_empty_lists: ("(()) ()", vec![
            Expr::List(vec![
                Expr::List(vec![])
            ]),
            Expr::List(vec![])
        ]),
        can_parse_vector: ("[:a 1 3]", vec![
            Expr::Vector(vec![
                Expr::Keyword("a".into()),
                Expr::Number(1),
                Expr::Number(3)])
        ]),
        can_parse_empty_vector: ("[]", vec![Expr::Vector(vec![])]),
        can_parse_map: ("{:a 1}", vec![
            Expr::Map(vec![
                Expr::Keyword("a".into()),
                Expr::Number(1)])
        ]),
        can_parse_empty_map: ("{}", vec![Expr::Map(vec![])]),
        can_parse_empty_set: ("#{}", vec![Expr::Set(vec![])]),
        can_parse_set: ("#{1 2}", vec![
            Expr::Set(vec![
                Expr::Number(1),
                Expr::Number(2)
            ])
        ]),
        can_parse_expr_example: ("(first {:args #{:a :b}})", vec![
            Expr::List(vec![
                Expr::Symbol("first".into()),
                Expr::Map(vec![
                    Expr::Keyword("args".into()),
                    Expr::Set(vec![
                        Expr::Keyword("a".into()),
                        Expr::Keyword("b".into()),
                    ])
                ])
            ])
        ]),
        can_parse_with_set: (r#"(reduce (fn-with-meta #{:a :b}))"#, vec![
            Expr::List(vec![
                Expr::Symbol("reduce".into()),
                Expr::List(vec![
                    Expr::Symbol("fn-with-meta".into()),
                    Expr::Set(vec![
                        Expr::Keyword("a".into()),
                        Expr::Keyword("b".into()),
                    ])
                ]),
            ])
        ]),
        can_parse_nested_lists_and_map: ("(({})) ;; hi", vec![
            Expr::List(vec![
                Expr::List(vec![Expr::Map(vec![])])]),
            Expr::Comment("; hi".into()),
        ]),
        can_parse_nested_lists_and_set: ("((#{})) ;; hi", vec![
            Expr::List(vec![
                Expr::List(vec![Expr::Set(vec![])])]),
            Expr::Comment("; hi".into()),
        ]),
        can_parse_expr: (r#"
                              (reduce (fn-with-meta
                                        {:docs "add two numbers"
                                         :args #{:a :b}}
                                        [a b]
                                          (+ a b)) (range 10 2)) ;; find a sum
                         "#, vec![
                             Expr::List(vec![
                                 Expr::Symbol("reduce".into()),
                                 Expr::List(vec![
                                     Expr::Symbol("fn-with-meta".into()),
                                     Expr::Map(vec![
                                         Expr::Keyword("docs".into()),
                                         Expr::String("add two numbers".into()),
                                         Expr::Keyword("args".into()),
                                         Expr::Set(vec![
                                             Expr::Keyword("a".into()),
                                             Expr::Keyword("b".into()),
                                         ])
                                     ]),
                                     Expr::Vector(vec![
                                         Expr::Symbol("a".into()),
                                         Expr::Symbol("b".into())
                                     ]),
                                     Expr::List(vec![
                                         Expr::Symbol("+".into()),
                                         Expr::Symbol("a".into()),
                                         Expr::Symbol("b".into())
                                     ])
                                 ]),
                                 Expr::List(vec![
                                     Expr::Symbol("range".into()),
                                     Expr::Number(10),
                                     Expr::Number(2),
                                 ])
                             ]),
                             Expr::Comment("; find a sum".into())
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
