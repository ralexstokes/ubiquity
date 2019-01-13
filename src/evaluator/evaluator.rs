use std::collections::HashSet;
use std::convert;
use std::result;

use lazy_static::lazy_static;

use super::env::Env;
use crate::reader::{Error as ParserError, Expr, FnDecl};

static DEF_SYMBOL: &'static str = "def";
static IF_SYMBOL: &'static str = "if";
static LET_SYMBOL: &'static str = "let*";
static DO_SYMBOL: &'static str = "do";
static FN_SYMBOL: &'static str = "fn*";
static LOOP_SYMBOL: &'static str = "loop*";
static RECUR_SYMBOL: &'static str = "recur";

lazy_static! {
    /// SPECIAL_SYMBOLS indicate a non-standard evaluation order
    static ref SPECIAL_SYMBOLS: HashSet<&'static str> = {
        let mut set = HashSet::new();

        set.insert(DEF_SYMBOL);
        set.insert(IF_SYMBOL);
        set.insert(LET_SYMBOL);
        set.insert(DO_SYMBOL);
        set.insert(FN_SYMBOL);
        set.insert(LOOP_SYMBOL);
        set.insert(RECUR_SYMBOL);

        set
    };
}

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
    FnMissingArgumentVector,
    FnParamsMustBeSymbolic,
    DefRequiresSymbolicName,
    IfPredicateMustBeBooleanCondition,
    LetRequiresVectorOfBindings,
    LetRequiresEvenNumberOfFormsInBindings,
    LetBindingRequiresSymbolicName,
    LocalBindingsMustBeVectorForm,
    UnboundSymbol(Expr),
    /// WrongArity indicates a `fn*` evaluation where the number of args passed did not match the number of params requested.
    // (number_requested, number_provided)
    WrongArity(usize, usize),
    ArithmeticOverflow,
    ArithmeticDivisionByZero,
    /// IncorrectArguments indicates a type error to some function or special form
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
        .iter()
        .map(|expr| eval_expr(expr, env))
        .collect::<Vec<Result<_>>>()
}

pub fn eval_expr(expr: &Expr, env: &mut Env) -> Result<Expr> {
    use self::Expr::*;

    let node = match expr {
        Nil => Nil,
        Bool(b) => Bool(*b),
        Number(n) => Number(*n),
        String(s) => String(s.clone()),
        Comment(s) => Comment(s.clone()),
        Symbol(s) => eval_symbol(s, env)?,
        Keyword(s) => Keyword(s.clone()),
        List(exprs) => eval_list(exprs, env)?,
        Vector(exprs) => {
            let results = exprs
                .iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Vector(results)
        }
        Map(exprs) => {
            let results = exprs
                .iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Map(results)
        }
        Set(exprs) => {
            let results = exprs
                .iter()
                .map(|expr| eval_expr(expr, env))
                .collect::<Result<Vec<_>>>()?;
            Set(results)
        }
        Fn(FnDecl {
            params,
            body,
            captured_bindings,
        }) => Fn(FnDecl {
            params: params.clone(),
            body: body.clone(),
            captured_bindings: captured_bindings.clone(),
        }),
        PrimitiveFn(name, host_fn) => PrimitiveFn(name.clone(), *host_fn),
        Recur(values) => Recur(values.clone()),
    };
    Ok(node)
}

fn eval_symbol(symbol: &str, env: &mut Env) -> Result<Expr> {
    env.lookup(&symbol)
        .ok_or(Error::UnboundSymbol(Expr::Symbol(String::from(symbol))))
        .map(|referent| referent.clone())
}

fn eval_list(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    if let Some((first, rest)) = exprs.split_first() {
        eval_list_dispatch(first, rest, env)
    } else {
        Ok(Expr::List(exprs.to_vec()))
    }
}

fn eval_list_dispatch(first: &Expr, rest: &[Expr], env: &mut Env) -> Result<Expr> {
    match first {
        Expr::Symbol(s) if s == DEF_SYMBOL => eval_def(rest, env),
        Expr::Symbol(s) if s == IF_SYMBOL => eval_if(rest, env),
        Expr::Symbol(s) if s == LET_SYMBOL => eval_let(rest, env),
        Expr::Symbol(s) if s == DO_SYMBOL => eval_do(rest, env),
        Expr::Symbol(s) if s == FN_SYMBOL => eval_fn(rest, env),
        Expr::Symbol(s) if s == LOOP_SYMBOL => eval_loop(rest, env),
        Expr::Symbol(s) if s == RECUR_SYMBOL => eval_recur(rest, env),
        _ => eval_expr(first, env).and_then(|op| {
            let args = rest
                .iter()
                .map(|arg| eval_expr(arg, env))
                .collect::<Result<Vec<_>>>()?;
            invoke(&op, args.as_slice(), env)
        }),
    }
}

fn is_bound(s: &String, bound_symbols: &HashSet<&String>) -> bool {
    bound_symbols.contains(s) || SPECIAL_SYMBOLS.contains(s.as_str())
}

fn find_captured_bindings(
    expr: &Expr,
    env: &Env,
    bound_symbols: &HashSet<&String>,
) -> Result<Vec<(String, Expr)>> {
    match expr {
        Expr::Symbol(s) => {
            if is_bound(s, bound_symbols) {
                Ok(vec![])
            } else {
                if let Some(value) = env.lookup(s) {
                    Ok(vec![(s.clone(), value.clone())])
                } else {
                    Err(Error::UnboundSymbol(Expr::Symbol(s.clone())))
                }
            }
        }
        Expr::List(exprs) => {
            let mut captures = vec![];
            for expr in exprs {
                let mut more_captures = find_captured_bindings(expr, env, bound_symbols)?;
                captures.append(&mut more_captures);
            }
            Ok(captures)
        }
        Expr::Vector(exprs) => {
            let mut captures = vec![];
            for expr in exprs {
                let mut more_captures = find_captured_bindings(expr, env, bound_symbols)?;
                captures.append(&mut more_captures);
            }
            Ok(captures)
        }
        Expr::Map(exprs) => {
            let mut captures = vec![];
            for expr in exprs {
                let mut more_captures = find_captured_bindings(expr, env, bound_symbols)?;
                captures.append(&mut more_captures);
            }
            Ok(captures)
        }
        Expr::Set(exprs) => {
            let mut captures = vec![];
            for expr in exprs {
                let mut more_captures = find_captured_bindings(expr, env, bound_symbols)?;
                captures.append(&mut more_captures);
            }
            Ok(captures)
        }
        Expr::Fn(FnDecl { body: exprs, .. }) => {
            let mut captures = vec![];
            for expr in exprs {
                let mut more_captures = find_captured_bindings(expr, env, bound_symbols)?;
                captures.append(&mut more_captures);
            }
            Ok(captures)
        }
        _ => Ok(vec![]),
    }
}

fn find_all_captured_bindings(
    exprs: &[Expr],
    env: &Env,
    params: &[Expr], // &[Expr::Symbol]
) -> Result<Vec<(String, Expr)>> {
    let bound_symbols = params
        .iter()
        .try_fold(HashSet::new(), |mut syms, expr| match expr {
            Expr::Symbol(s) => {
                syms.insert(s);
                Ok(syms)
            }
            _ => Err(Error::FnParamsMustBeSymbolic),
        })?;

    let mut all_captures = vec![];

    for expr in exprs {
        let mut captures = find_captured_bindings(expr, env, &bound_symbols)?;
        all_captures.append(&mut captures);
    }
    Ok(all_captures)
}

// (fn* [<args>] <body>)
fn eval_fn(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    exprs
        .split_first()
        // TODO should be polyadic, not just 2
        .ok_or(Error::WrongArity(2, exprs.len()))
        .and_then(|(first, rest)| match first {
            Expr::Vector(params) => {
                let captured_bindings = find_all_captured_bindings(rest, env, params)?;

                Ok(Expr::Fn(FnDecl {
                    params: params.to_vec(),
                    body: rest.to_vec(),
                    captured_bindings,
                }))
            }
            _ => Err(Error::FnMissingArgumentVector),
        })
}

// (def <symbol> <form>)
fn eval_def(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    exprs
        .split_first()
        // TODO should be polyadic, not just 2
        .ok_or(Error::WrongArity(2, exprs.len()))
        .and_then(|(first, rest)| match first {
            // TODO sink into `eval_do`?
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

// (if p? c a)
fn eval_if(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    if exprs.len() != 3 {
        return Err(Error::WrongArity(3, exprs.len()));
    }

    let predicate = &exprs[0];

    match eval_expr(predicate, env)? {
        Expr::Bool(predicate) => {
            if predicate {
                eval_expr(&exprs[1], env)
            } else {
                eval_expr(&exprs[2], env)
            }
        }
        _ => Err(Error::IfPredicateMustBeBooleanCondition),
    }
}

// (let* [bindings*] exprs*)
fn eval_let(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    exprs
        .split_first()
        // TODO can be greater than 2
        .ok_or(Error::WrongArity(2, exprs.len()))
        .and_then(|(bindings, body)| match bindings {
            Expr::Vector(bindings) => {
                if bindings.len() % 2 != 0 {
                    return Err(Error::LetRequiresEvenNumberOfFormsInBindings);
                }

                let mut local_env = Env::with_parent(env);
                for pair in bindings.chunks_exact(2) {
                    match &pair[0] {
                        Expr::Symbol(name) => {
                            let init_value = &pair[1];
                            let value = eval_expr(init_value, &mut local_env)?;
                            local_env.add_binding(&name, &value);
                        }
                        _ => return Err(Error::LetBindingRequiresSymbolicName),
                    }
                }

                eval_do(body, &mut local_env)
            }
            _ => Err(Error::LocalBindingsMustBeVectorForm),
        })
}

// (do exprs*)
fn eval_do(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    exprs
        .iter()
        .try_fold(Expr::Nil, |_, expr| eval_expr(expr, env))
}

// [name0 val0 name1 val1 ...], [val0' val1' ...] ~> [name0 val0' name1 val1' ...]
// NOTE: assuming some invariants hold as this function should only be called after we have successfully passed a call to `eval_let` where they are checked.
fn update_bindings_values(bindings: &Expr, new_values: &[Expr]) -> Result<Expr> {
    match bindings {
        Expr::Vector(bindings) => {
            let new_bindings = bindings
                .chunks_exact(2)
                .into_iter()
                .zip(new_values.iter())
                .flat_map(|(pair, new_value)| {
                    let name = &pair[0];
                    vec![name.clone(), new_value.clone()]
                })
                .collect::<Vec<_>>();
            Ok(Expr::Vector(new_bindings))
        }
        _ => Err(Error::LocalBindingsMustBeVectorForm),
    }
}

// (loop [bindings*] body)
fn eval_loop(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    // TODO ensure any recur is in tail position
    let mut result = eval_let(exprs, env)?;

    while let Expr::Recur(new_values) = result {
        let updated_bindings = update_bindings_values(&exprs[0], &new_values)?;

        let mut new_exprs = vec![];
        new_exprs.push(updated_bindings);
        new_exprs.extend_from_slice(&exprs[1..]);

        // TODO can save some work by calling "`eval_let_inner`"
        result = eval_let(&new_exprs, env)?;
    }

    Ok(result)
}

// (recur bindings*)
fn eval_recur(exprs: &[Expr], env: &mut Env) -> Result<Expr> {
    let mut evaled_exprs = vec![];
    for expr in exprs {
        let expr = eval_expr(expr, env)?;
        evaled_exprs.push(expr);
    }
    Ok(Expr::Recur(evaled_exprs))
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

fn invoke(op: &Expr, args: &[Expr], env: &mut Env) -> Result<Expr> {
    match op {
        Expr::Fn(FnDecl {
            params,
            body,
            captured_bindings,
        }) => {
            if params.len() != args.len() {
                return Err(Error::WrongArity(params.len(), args.len()));
            }

            let mut local_env = Env::with_parent(env);
            local_env.add_bindings(captured_bindings);
            let bindings = zip_for_env(params, args)?;
            local_env.add_bindings(bindings.as_slice());

            eval_do(body, &mut local_env)
        }
        Expr::PrimitiveFn(_, host_fn) => host_fn(args.to_vec()).map_err(|e| e.into()),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::eval as eval_str;
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

    #[test]
    fn test_simple_closures() {
        let mut env = prelude::env();

        let exprs = vec![Expr::List(vec![
            Expr::Symbol("def".into()),
            Expr::Symbol("add-b".into()),
            Expr::List(vec![
                Expr::Symbol("fn*".into()),
                Expr::Vector(vec![Expr::Symbol("a".into())]),
                Expr::List(vec![
                    Expr::Symbol("+".into()),
                    Expr::Symbol("a".into()),
                    Expr::Symbol("b".into()),
                ]),
            ]),
        ])];

        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone();
        assert_eq!(Err(Error::UnboundSymbol(Expr::Symbol("b".into()))), result);

        let def_expr = vec![Expr::List(vec![
            Expr::Symbol("def".into()),
            Expr::Symbol("b".into()),
            Expr::Number(12),
        ])];
        let results = eval(def_expr, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Symbol("b".into()), result);

        let exprs = vec![Expr::List(vec![
            Expr::Symbol("def".into()),
            Expr::Symbol("add-b".into()),
            Expr::List(vec![
                Expr::Symbol("fn*".into()),
                Expr::Vector(vec![Expr::Symbol("a".into())]),
                Expr::List(vec![
                    Expr::Symbol("+".into()),
                    Expr::Symbol("a".into()),
                    Expr::Symbol("b".into()),
                ]),
            ]),
        ])];

        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Symbol("add-b".into()), result);

        let exprs = vec![Expr::List(vec![
            Expr::Symbol("add-b".into()),
            Expr::Number(12),
        ])];

        let results = eval(exprs, &mut env);
        let result = results.first().unwrap().clone().unwrap();
        assert_eq!(Expr::Number(24), result);
    }

    #[test]
    fn closures_respect_special_forms() {
        let input = "(def fact (fn* [n] (if (= n 1) n (* n (fact (dec n))))))";
        // (def fact (fn* [n] (..)))
        // (def fact (fn* fact [n]))
        let mut env = prelude::env();
        let results = eval_str(input, &mut env);
        println!("{:?}", results);
        assert!(false);
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
        can_eval_if_true: (vec![
            List(vec![
                Symbol("if".into()),
                Bool(true),
                Number(1),
                Number(2),
            ])
        ], vec![Number(1)]),
        can_eval_if_false: (vec![
            List(vec![
                Symbol("if".into()),
                Bool(false),
                Number(1),
                Number(2),
            ])
        ], vec![Number(2)]),
        can_eval_if_unevaluated: (vec![
            List(vec![
                Symbol("if".into()),
                Bool(false),
                List(vec![
                    Symbol("/".into()),
                    Number(1),
                    Number(0),
                ]),
                Number(2),
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
