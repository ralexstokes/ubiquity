use std::collections::HashMap;
use std::convert;
use std::fmt;
use std::iter;
use std::num;
use std::result;

use itertools::Itertools;

use super::lexer::{Delimiter, Error as LexerError, Lexer, Token};
use crate::evaluator::Result as EvalResult;

pub type Result<T> = result::Result<T, Error>;
type LexerIter<'a> = iter::Peekable<iter::Enumerate<Lexer<'a>>>;
pub type HostFn = fn(Vec<Expr>) -> EvalResult<Expr>;

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
    PrimitiveFn(String, HostFn),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FnDecl {
    pub params: Vec<Expr>,
    pub body: Vec<Expr>,
    pub captured_bindings: Vec<(String, Expr)>,
}

fn fmt_seq<'a>(
    f: &mut fmt::Formatter,
    nodes: impl IntoIterator<Item = &'a Expr>,
    delimiter: Delimiter,
) -> fmt::Result {
    write!(f, "{}", delimiter.open_char())?;
    write!(f, "{}", nodes.into_iter().format(" "))?;
    write!(f, "{}", delimiter.close_char())
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
            List(nodes) => fmt_seq(f, nodes, Delimiter::Paren),
            Vector(nodes) => fmt_seq(f, nodes, Delimiter::Bracket),
            Map(nodes) => fmt_seq(f, nodes, Delimiter::Brace),
            Set(nodes) => {
                write!(f, "#")?;
                fmt_seq(f, nodes, Delimiter::Brace)
            }
            Fn(FnDecl { params, body, .. }) => {
                write!(f, "(fn* [")?;
                write!(f, "{}] ", params.iter().format(" "))?;
                write!(f, "{}", body.iter().format(" "))?;
                write!(f, ")")
            }
            PrimitiveFn(name, _) => write!(f, "#<primitive: `{}`>", name),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    /// UnbalancedDelimiter indicates a delimiter that does not match the other delimiter in the pair of Open and Close. Returns an index into the token stream where the imbalance occurs.
    UnbalancedDelimiter(Delimiter, usize),
    UnbalancedString(usize),
    UnrecognizedToken(usize, char),
    MissingPairInMap(Vec<Expr>),
    // ParseIntError(&'a str),
    UnexpectedEndOfInput(usize),
    Internal,
}

impl convert::From<&LexerError> for Error {
    fn from(lexer_error: &LexerError) -> Self {
        match lexer_error {
            LexerError::UnrecognizedToken(index, ch) => Error::UnrecognizedToken(*index, *ch),
            LexerError::UnbalancedString(index) => Error::UnbalancedString(*index),
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
pub struct Parser {
    delimiter_nesting: HashMap<Delimiter, Vec<usize>>,
}

impl<'a> Parser {
    pub fn new() -> Self {
        let mut delimiter_nesting = HashMap::new();
        delimiter_nesting.insert(Delimiter::Paren, Vec::with_capacity(INITIAL_NESTING_DEPTH));
        delimiter_nesting.insert(
            Delimiter::Bracket,
            Vec::with_capacity(INITIAL_NESTING_DEPTH),
        );
        delimiter_nesting.insert(Delimiter::Brace, Vec::with_capacity(INITIAL_NESTING_DEPTH));

        Self { delimiter_nesting }
    }

    /// run takes an `Iterator` over `LexerResult<Token>` and attempts to parse `Expr`s from the token stream until it is exhausted.
    // NOTE: we require a `&mut T` so that we can recurse over the token stream. The borrowing could be simplified with
    // `&mut tokens` but then the compiler hits a recursion limit while attempting to monomorphize the function.
    pub fn run(&mut self, lexer: Lexer) -> Vec<Result<Expr>> {
        let mut forms = vec![];

        let mut iter = lexer.enumerate().peekable();

        while iter.peek().is_some() {
            let mut form = self.parse_form(&mut iter);

            if form.is_ok() {
                // only check if form is Ok(_) so we do not mask any errors
                if let Some(err) = self.find_unclosed_delimiters() {
                    form = err;
                }
            }

            forms.push(form);
        }

        forms
    }

    fn find_unclosed_delimiters(&mut self) -> Option<Result<Expr>> {
        for record in self.delimiter_nesting.values_mut() {
            if let Some(index) = record.pop() {
                return Some(Err(Error::UnexpectedEndOfInput(index)));
            }
        }
        None
    }

    pub fn parse_form(&mut self, iter: &mut LexerIter) -> Result<Expr> {
        while let Some((index, result)) = iter.peek() {
            let index = *index;

            match result {
                Ok(token) => match token {
                    Token::Open(Delimiter::Paren) => {
                        return self.parse_seq(Delimiter::Paren, Expr::List, iter)
                    }
                    Token::Open(Delimiter::Bracket) => {
                        return self.parse_seq(Delimiter::Bracket, Expr::Vector, iter)
                    }
                    Token::Open(Delimiter::Brace) => {
                        return self.parse_seq(Delimiter::Brace, Expr::Map, iter)
                    }
                    Token::Close(d) => {
                        let d = *d;
                        iter.next();
                        return Err(Error::UnbalancedDelimiter(d, index));
                    }
                    _ => return self.parse_atomic(iter),
                },
                Err(_) => break,
            }
        }

        if let Some((_, result)) = iter.next() {
            match result {
                Ok(_) => unreachable!(),
                Err(ref e) => return Err(e.into()),
            }
        }

        Err(Error::Internal)
    }

    fn parse_atomic(&mut self, iter: &mut LexerIter) -> Result<Expr> {
        let (_, result) = iter.next().unwrap();

        match result {
            Ok(token) => match token {
                Token::Number(input) => {
                    return self.parse_number(input);
                }
                Token::String(input) => {
                    return self.parse_string(input);
                }
                Token::Comment(input) => {
                    return self.parse_comment(input);
                }
                Token::Symbol(input) => {
                    return self.parse_symbol(input);
                }
                Token::Dispatch => {
                    return self.parse_dispatch(iter);
                }
                _ => unreachable!(),
            },
            Err(ref e) => Err(e.into()),
        }
    }

    fn parse_seq<C>(
        &mut self,
        delimiter: Delimiter,
        constructor: C,
        iter: &mut LexerIter,
    ) -> Result<Expr>
    where
        C: Fn(Vec<Expr>) -> Expr,
    {
        let (index, _) = iter.next().unwrap();
        self.push_depth(delimiter, index);

        let mut forms = vec![];

        while let Some((index, result)) = iter.peek() {
            let index = *index;
            match result {
                Ok(token) => match token {
                    Token::Close(d) if *d == delimiter => {
                        iter.next();
                        self.pop_depth(delimiter);
                        break;
                    }
                    Token::Close(unbalanced_delimiter) => {
                        let delimiter = unbalanced_delimiter.clone();
                        iter.next();
                        return Err(Error::UnbalancedDelimiter(delimiter, index));
                    }
                    _ => {
                        let next_form = self.parse_form(iter)?;
                        forms.push(next_form);
                    }
                },
                Err(e) => return Err(e.into()),
            }
        }

        Ok(constructor(forms))
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

    fn parse_dispatch(&mut self, iter: &mut LexerIter) -> Result<Expr> {
        self.parse_form(iter).map(|form| match form {
            Expr::Map(nodes) => Expr::Set(nodes),
            _ => unimplemented!(),
        })
    }

    fn push_depth(&mut self, delimiter: Delimiter, index: usize) {
        let stack = self.delimiter_nesting.get_mut(&delimiter).unwrap();
        stack.push(index);
    }

    fn pop_depth(&mut self, delimiter: Delimiter) {
        let stack = self.delimiter_nesting.get_mut(&delimiter).unwrap();
        stack.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::super::lexer::Lexer;
    use super::*;

    fn run_parse(input: &str) -> Vec<Result<Expr>> {
        let lexer = Lexer::new(input);

        let mut parser = Parser::new();
        parser.run(lexer)
    }

    macro_rules! parse_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected): (&str, Vec<Expr>) = $value;
                    let results = run_parse(input);
                    let mut actual = vec![];
                    for result in results {
                        actual.push(result.unwrap());
                    }
                    assert_eq!(expected, actual);
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
                Expr::List(vec![Expr::Map(vec![])])
            ]),
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
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnbalancedString(2)));
    }

    #[test]
    fn can_parse_unbalanced_lists() {
        let input = "(";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnexpectedEndOfInput(0)));

        let input = ")";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 0)));

        let input = "hi there)";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 2)));

        let input = "(+ 2 2 })";
        let result = run_parse(input);
        assert_eq!(
            result,
            vec![
                Err(Error::UnbalancedDelimiter(Delimiter::Brace, 4)),
                Err(Error::UnbalancedDelimiter(Delimiter::Paren, 5)),
            ]
        );

        let input = "hi there) foo bar";
        let result = run_parse(input);
        assert_eq!(
            result,
            vec![
                Ok(Expr::Symbol("hi".into())),
                Ok(Expr::Symbol("there".into())),
                Err(Error::UnbalancedDelimiter(Delimiter::Paren, 2)),
                Ok(Expr::Symbol("foo".into())),
                Ok(Expr::Symbol("bar".into())),
            ]
        );

        let input = "hi(";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnexpectedEndOfInput(1)));

        let input = "hi())";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnbalancedDelimiter(Delimiter::Paren, 3)));

        let input = "hi(((((((((()))))))))))";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(
            result,
            Err(Error::UnbalancedDelimiter(Delimiter::Paren, 21))
        );
    }

    #[test]
    fn can_parse_unbalanced_vectors() {
        let input = "[ 1 2 []";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(result, Err(Error::UnexpectedEndOfInput(0)));

        let input = "][ 1 2 []";
        let result = run_parse(input);
        assert_eq!(
            result,
            vec![
                Err(Error::UnbalancedDelimiter(Delimiter::Bracket, 0)),
                Err(Error::UnexpectedEndOfInput(1)),
            ]
        );
    }

    #[test]
    fn can_parse_unbalanced_maps() {
        let input = "{:a 1";
        let result = run_parse(input).pop().unwrap();
        assert_eq!(Err(Error::UnexpectedEndOfInput(0)), result);

        let input = " 1 2 3{:a 1";
        let result = run_parse(input);
        assert_eq!(
            vec![
                Ok(Expr::Number(1)),
                Ok(Expr::Number(2)),
                Ok(Expr::Number(3)),
                Err(Error::UnexpectedEndOfInput(3)),
            ],
            result
        );

        let input = "}:a 1}";
        let result = run_parse(input);
        assert_eq!(
            vec![
                Err(Error::UnbalancedDelimiter(Delimiter::Brace, 0)),
                Ok(Expr::Keyword("a".into())),
                Ok(Expr::Number(1)),
                Err(Error::UnbalancedDelimiter(Delimiter::Brace, 3))
            ],
            result
        );

        let input = "{}:a 1}";
        let result = run_parse(input);
        assert_eq!(
            vec![
                Ok(Expr::Map(vec![])),
                Ok(Expr::Keyword("a".into())),
                Ok(Expr::Number(1)),
                Err(Error::UnbalancedDelimiter(Delimiter::Brace, 4))
            ],
            result
        );
    }
}
