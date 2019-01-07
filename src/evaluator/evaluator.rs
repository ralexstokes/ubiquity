use std::convert;
use std::result;

use super::env::Env;
use crate::reader::{Error as ParserError, Expr, FnDecl};

static FN_SYMBOL: &'static str = "fn*";
static DEF_SYMBOL: &'static str = "def";

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    FnMissingArgumentVector,
    DefRequiresSymbolicName,
    InsufficientArguments,
    UnboundSymbol(Expr),
    /// WrongArity indicates a `fn*` evaluation where the number of args passed did not match the number of params requested.
    // (number_requested, number_provided)
    WrongArity(usize, usize),
    IncorrectArguments,
    Internal,
    ParserError(ParserError),
}

impl convert::From<ParserError> for Error {
    fn from(parser_error: ParserError) -> Self {
        Error::ParserError(parser_error)
    }
}

pub fn eval(exprs: Vec<Expr>, env: &mut Env) -> Vec<Result<Expr>> {
    exprs
        .into_iter()
        .map(|expr| eval_expr(expr, env))
        .collect::<Vec<Result<_>>>()
}

pub fn eval_expr(expr: Expr, env: &mut Env) -> Result<Expr> {
    use self::Expr::*;

    let node = match expr {
        Nil => Nil,
        Bool(b) => Bool(b),
        Number(n) => Number(n),
        String(s) => String(s),
        Comment(s) => Comment(s),
        Symbol(s) => eval_symbol(s, env)?,
        Keyword(s) => Keyword(s),
        List(exprs) => eval_list(exprs, env)?,
        Vector(exprs) => {
            let results = exprs
                .into_iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Vector(results)
        }
        Map(exprs) => {
            let results = exprs
                .into_iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Map(results)
        }
        Set(exprs) => {
            let results = exprs
                .into_iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Set(results)
        }
        Fn(FnDecl { params, body }) => Fn(FnDecl { params, body }),
        PrimitiveFn(name, host_fn) => PrimitiveFn(name, host_fn),
    };
    Ok(node)
}

fn eval_symbol(symbol: String, env: &mut Env) -> Result<Expr> {
    env.lookup(&symbol)
        .ok_or(Error::UnboundSymbol(Expr::Symbol(symbol)))
        .map(|referent| referent.clone())
}

fn eval_list(exprs: Vec<Expr>, env: &mut Env) -> Result<Expr> {
    if let Some((first, rest)) = exprs.split_first() {
        eval_list_dispatch(first, rest, env)
    } else {
        Ok(Expr::List(exprs))
    }
}

fn eval_list_dispatch(first: &Expr, rest: &[Expr], env: &mut Env) -> Result<Expr> {
    match first {
        Expr::Symbol(s) if s == FN_SYMBOL => eval_fn(rest),
        Expr::Symbol(s) if s == DEF_SYMBOL => eval_def(rest, env),
        _ => eval_expr(first.clone(), env).and_then(|op| {
            let args = rest
                .iter()
                .cloned()
                .map(|arg| eval_expr(arg, env))
                .collect::<Result<Vec<_>>>()?;
            apply(&op, args.as_slice(), env)
        }),
    }
}

// (fn* [<args>] <body>)
fn eval_fn(exprs: &[Expr]) -> Result<Expr> {
    exprs
        .split_first()
        .ok_or(Error::InsufficientArguments)
        .and_then(|(first, rest)| match first {
            Expr::Vector(params) => Ok(Expr::Fn(FnDecl {
                params: params.to_vec(),
                body: rest.to_vec(),
            })),
            _ => Err(Error::FnMissingArgumentVector),
        })
}

// (def <symbol> <form>)
fn eval_def(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    exprs
        .split_first()
        .ok_or(Error::InsufficientArguments)
        .and_then(|(first, rest)| match first {
            Expr::Symbol(name) => eval(rest.to_vec(), env)
                .split_last()
                .ok_or(Error::Internal)
                .and_then(|(last, _)| match last {
                    Ok(result) => {
                        env.add_binding(name, result);
                        Ok(Expr::Symbol(name.clone()))
                    }
                    Err(e) => Err(e.clone()),
                }),
            _ => Err(Error::DefRequiresSymbolicName),
        })
}

// zip_for_env zips the `params` to the `args` so that the environment can be extended with the appropriate bindings.
fn zip_for_env(params: &[Expr], args: &[Expr]) -> Result<Vec<(String, Expr)>> {
    Ok(params
        .iter()
        .filter_map(|param| match param {
            Expr::Symbol(s) => Some(s.clone()),
            _ => None,
        })
        .zip(args.iter().cloned())
        .collect::<Vec<_>>())
}

fn apply(op: &Expr, args: &[Expr], env: &mut Env) -> Result<Expr> {
    match op {
        Expr::Fn(FnDecl { params, body }) => {
            if params.len() != args.len() {
                return Err(Error::WrongArity(params.len(), args.len()));
            }

            let mut local_env = Env::with_parent(env);
            let bindings = zip_for_env(params, args)?;
            local_env.add_bindings(bindings.as_slice());

            eval(body.clone(), &mut local_env)
                .split_last()
                .ok_or(Error::Internal)
                .and_then(|(last, _)| match last {
                    Ok(result) => Ok(result.clone()),
                    Err(e) => Err(e.clone()),
                })
        }
        Expr::PrimitiveFn(_, host_fn) => host_fn(args.to_vec()).map_err(|e| e.into()),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::prelude;
    use super::Expr::*;
    use super::*;

    fn run_eval(exprs: Vec<Expr>) -> Vec<Result<Expr>> {
        let mut env = prelude::env();
        eval(exprs, &mut env)
    }

    #[test]
    fn test_env_simple() {
        let mut env = prelude::env();
        let exprs = vec![Expr::List(vec![
            Expr::Symbol("def".into()),
            Expr::Symbol("foo".into()),
            Expr::Number(333),
        ])];

        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Symbol("foo".into()), result);

        let exprs = vec![Expr::Symbol("foo".into())];
        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Number(333), result);
    }

    #[test]
    fn test_env_evaluating() {
        let mut env = prelude::env();
        let exprs = vec![Expr::List(vec![
            Expr::Symbol("def".into()),
            Expr::Symbol("inc".into()),
            Expr::List(vec![
                Expr::Symbol("fn*".into()),
                Expr::Vector(vec![Expr::Symbol("a".into())]),
                Expr::List(vec![
                    Expr::Symbol("+".into()),
                    Expr::Symbol("a".into()),
                    Expr::Number(1),
                ]),
            ]),
        ])];

        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Symbol("inc".into()), result);

        let exprs = vec![Expr::List(vec![
            Expr::Symbol("inc".into()),
            Expr::Number(1),
        ])];
        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Number(2), result);
    }

    macro_rules! eval_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected): (Vec<Expr>, Vec<Expr>) = $value;
                    let expected_results: Vec<Result<Expr>> = expected.into_iter().map(|expr| Ok(expr)).collect();

                    let results = run_eval(input);

                    assert_eq!(expected_results, results);
                }
            )*
        }
    }

    eval_tests! {
        can_eval_empty: (vec![], vec![]),
        can_eval_simple_arith: (vec![
            List(vec![
                Symbol("+".into()),
                Number(2),
                Number(2),
            ]),
        ], vec![Number(4)]),
        can_eval_fn: (vec![
            List(vec![
                List(vec![
                    Symbol("fn*".into()),
                    Vector(vec![
                        Symbol("a".into())
                    ]),
                    List(vec![
                        Symbol("+".into()),
                        Symbol("a".into()),
                        Number(1),
                    ])
                ]),
                Number(1),
            ])
        ], vec![Number(2)]),
        can_eval_literals: (vec![
            Nil,
            Bool(true),
            Bool(false),
            Number(33),
            String("hi".into()),
            Comment("; some comment".into()),
            Keyword("a".into()),
            List(vec![]),
            Vector(vec![]),
            Vector(vec![
                Keyword("a".into()),
                Number(22),
                String("hi".into()),
                String("there".into()),
                String("eval".into())
            ]),
            Map(vec![]),
            Map(vec![Keyword("a".into()), Number(22)]),
            Set(vec![]),
            Set(vec![
                String("hi".into()),
                String("there".into()),
                String("eval".into())
            ]),
        ], vec![
            Nil,
            Bool(true),
            Bool(false),
            Number(33),
            String("hi".into()),
            Comment("; some comment".into()),
            Keyword("a".into()),
            List(vec![]),
            Vector(vec![]),
            Vector(vec![
                Keyword("a".into()),
                Number(22),
                String("hi".into()),
                String("there".into()),
                String("eval".into())
            ]),
            Map(vec![]),
            Map(vec![Keyword("a".into()), Number(22)]),
            Set(vec![]),
            Set(vec![
                String("hi".into()),
                String("there".into()),
                String("eval".into())
            ]),
        ]),
    }
}
