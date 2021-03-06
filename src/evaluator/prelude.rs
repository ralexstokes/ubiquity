use super::env::Env;
use super::evaluator::Error;
use super::Result;
use crate::reader::{Expr, HostFn};
use itertools::Itertools;
use std::fmt::Write;

fn add(args: Vec<Expr>) -> Result<Expr> {
    if let Some((first, rest)) = args.split_first() {
        match first {
            Expr::Number(first) => {
                let mut result = *first;
                for elem in rest {
                    match elem {
                        Expr::Number(next) => match result.checked_add(*next) {
                            Some(next) => result = next,
                            None => return Err(Error::ArithmeticOverflow),
                        },
                        _ => return Err(Error::IncorrectArguments),
                    }
                }
                return Ok(Expr::Number(result));
            }
            _ => return Err(Error::IncorrectArguments),
        }
    }
    Ok(Expr::Number(0))
}

fn sub(args: Vec<Expr>) -> Result<Expr> {
    if let Some((first, rest)) = args.split_first() {
        match first {
            Expr::Number(first) => {
                let mut result = *first;
                for elem in rest {
                    match elem {
                        Expr::Number(next) => match result.checked_sub(*next) {
                            Some(next) => result = next,
                            None => return Err(Error::ArithmeticOverflow),
                        },
                        _ => return Err(Error::IncorrectArguments),
                    }
                }
                return Ok(Expr::Number(result));
            }
            _ => return Err(Error::IncorrectArguments),
        }
    }
    Ok(Expr::Number(0))
}

fn mul(args: Vec<Expr>) -> Result<Expr> {
    if let Some((first, rest)) = args.split_first() {
        match first {
            Expr::Number(first) => {
                let mut result = *first;
                for elem in rest {
                    dbg!(&elem);
                    match elem {
                        Expr::Number(next) => match result.checked_mul(*next) {
                            Some(next) => result = next,
                            None => return Err(Error::ArithmeticOverflow),
                        },
                        _ => return Err(Error::IncorrectArguments),
                    }
                }
                return Ok(Expr::Number(result));
            }
            _ => return Err(Error::IncorrectArguments),
        }
    }
    Ok(Expr::Number(0))
}

fn div(args: Vec<Expr>) -> Result<Expr> {
    if let Some((first, rest)) = args.split_first() {
        match first {
            Expr::Number(first) => {
                let mut result = *first;
                for elem in rest {
                    match elem {
                        Expr::Number(next) => match result.checked_div(*next) {
                            Some(next) => result = next,
                            None => return Err(Error::ArithmeticDivisionByZero),
                        },
                        _ => return Err(Error::IncorrectArguments),
                    }
                }
                return Ok(Expr::Number(result));
            }
            _ => return Err(Error::IncorrectArguments),
        }
    }
    Ok(Expr::Number(0))
}

fn list(args: Vec<Expr>) -> Result<Expr> {
    Ok(Expr::List(args))
}

fn prn(args: Vec<Expr>) -> Result<Expr> {
    let result = args
        .iter()
        .map(|expr| {
            let mut output = String::new();
            let _ = write!(&mut output, "{}", expr);
            output
        })
        .intersperse(" ".to_string())
        .collect::<String>();
    println!("{}", result);
    Ok(Expr::Nil)
}

fn eq(args: Vec<Expr>) -> Result<Expr> {
    args.split_first()
        // TODO fix possible many arity
        .ok_or(Error::WrongArity(1, args.len()))
        .and_then(|(first, rest)| {
            for form in rest {
                if first != form {
                    return Ok(Expr::Bool(false));
                }
            }
            Ok(Expr::Bool(true))
        })
}

fn inc(args: Vec<Expr>) -> Result<Expr> {
    if args.len() != 1 {
        return Err(Error::IncorrectArguments);
    }

    args.get(0)
        .ok_or(Error::IncorrectArguments)
        .and_then(|number| match number {
            Expr::Number(number) => Ok(Expr::Number(number + 1)),
            _ => Err(Error::IncorrectArguments),
        })
}

fn dec(args: Vec<Expr>) -> Result<Expr> {
    if args.len() != 1 {
        return Err(Error::IncorrectArguments);
    }

    args.get(0)
        .ok_or(Error::IncorrectArguments)
        .and_then(|number| match number {
            Expr::Number(number) => Ok(Expr::Number(number - 1)),
            _ => Err(Error::IncorrectArguments),
        })
}

fn count(args: Vec<Expr>) -> Result<Expr> {
    use Expr::*;

    if args.len() != 1 {
        return Err(Error::IncorrectArguments);
    }

    let result = match &args[0] {
        Nil => 0,
        String(s) => s.len(),
        List(elems) => elems.len(),
        Vector(elems) => elems.len(),
        Map(bindings) => bindings.len() / 2,
        Set(bindings) => bindings.len(),
        _ => return Err(Error::IncorrectArguments),
    };

    Ok(Number(result as i64))
}

static PRELUDE_BINDINGS: &[(&str, &str, HostFn)] = &[
    ("+", "add", add),
    ("-", "sub", sub),
    ("*", "mul", mul),
    ("/", "div", div),
    ("list", "list", list),
    ("prn", "prn", prn),
    ("=", "equal", eq),
    ("inc", "increment", inc),
    ("dec", "decrement", dec),
    ("count", "count", count),
];

pub fn env() -> Env<'static> {
    let bindings = PRELUDE_BINDINGS
        .into_iter()
        .map(|(k, name, host_fn)| {
            (
                String::from(*k),
                Expr::PrimitiveFn(String::from(*name), *host_fn),
            )
        })
        .collect::<Vec<(String, Expr)>>();
    let mut env = Env::new();
    env.add_bindings(bindings.as_slice());
    env
}
