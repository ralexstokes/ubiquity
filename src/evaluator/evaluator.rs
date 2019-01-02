use std::convert;
use std::result;

use super::env::Env;
use crate::reader::{Error as ParserError, Expr, FnDecl};

static FN_SYMBOL: &'static str = "fn*";

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {
    FnMissingArgumentVector,
    InsufficientArguments,
    ParserError(ParserError),
}

impl convert::From<ParserError> for Error {
    fn from(parser_error: ParserError) -> Self {
        Error::ParserError(parser_error)
    }
}

pub fn eval(exprs: Vec<Expr>, env: &mut Env) -> Vec<Result<Expr>> {
    exprs.into_iter().map(eval_expr).collect::<Vec<Result<_>>>()
}

fn eval_expr(expr: Expr) -> Result<Expr> {
    use self::Expr::*;

    let node = match expr {
        Nil => Nil,
        Bool(b) => Bool(b),
        Number(n) => Number(n),
        String(s) => String(s),
        Comment(s) => Comment(s),
        Symbol(s) => eval_symbol(s)?,
        Keyword(s) => Keyword(s),
        List(exprs) => eval_list(exprs)?,
        Vector(exprs) => {
            let results = exprs
                .into_iter()
                .map(eval_expr)
                .collect::<Result<Vec<_>>>()?;
            Vector(results)
        }
        Map(exprs) => {
            let results = exprs
                .into_iter()
                .map(eval_expr)
                .collect::<Result<Vec<_>>>()?;
            Map(results)
        }
        Set(exprs) => {
            let results = exprs
                .into_iter()
                .map(eval_expr)
                .collect::<Result<Vec<_>>>()?;
            Set(results)
        }
        Fn(FnDecl { params, body }) => Vector(vec![]),
        PrimitiveFn(host_fn) => PrimitiveFn(host_fn),
    };
    Ok(node)
}

fn eval_symbol(symbol: String) -> Result<Expr> {
    Ok(Expr::Symbol(symbol))
}

fn eval_list(exprs: Vec<Expr>) -> Result<Expr> {
    if let Some((first, rest)) = exprs.split_first() {
        eval_list_dispatch(first, rest)
    } else {
        Ok(Expr::List(exprs))
    }
}

fn eval_list_dispatch(first: &Expr, rest: &[Expr]) -> Result<Expr> {
    match first {
        Expr::Symbol(s) if s == FN_SYMBOL => eval_fn(rest),
        _ => apply(first, rest),
    }
}

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

fn apply(op: &Expr, args: &[Expr]) -> Result<Expr> {
    match op {
        Expr::Fn(FnDecl { params, body }) => {
            let expr = Expr::Bool(true); // build extended expr
            eval_expr(expr)
        }
        Expr::PrimitiveFn(host_fn) => host_fn(args.to_vec()).map_err(|e| e.into()),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
mod tests {
    use super::Env;
    use super::Expr::*;
    use super::*;

    fn run_eval(exprs: Vec<Expr>) -> Vec<Result<Expr>> {
        let mut env = Env::new();
        eval(exprs, &mut env)
    }

    macro_rules! eval_tests {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected): (Vec<Expr>, Vec<Expr>) = $value;
                    let result = run_eval(input);
                    let expected_results: Vec<Result<Expr>> = expected.into_iter().map(|expr| Ok(expr)).collect();
                    assert_eq!(expected_results, result);
                }
            )*
        }
    }

    eval_tests! {
        can_eval_empty: (vec![], vec![]),
        can_eval_literals: (vec![
            Nil,
            Bool(true),
            Bool(false),
            Number(33),
            String("hi".into()),
            Comment("; some comment".into()),
            Symbol("there".into()),
            Keyword("a".into()),
            List(vec![]),
            List(vec![Symbol("hi".into())]),
            Vector(vec![]),
            Vector(vec![
                Symbol("hi".into()),
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
            Symbol("there".into()),
            Keyword("a".into()),
            List(vec![]),
            List(vec![Symbol("hi".into())]),
            Vector(vec![]),
            Vector(vec![
                Symbol("hi".into()),
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
