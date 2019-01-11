use super::env::Env;
use super::evaluator::Error;
use super::Result;
use crate::reader::{Expr, HostFn};

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
    args.iter().for_each(|arg| {
        println!("{}", arg);
    });
    Ok(Expr::Nil)
}

static PRELUDE_BINDINGS: &[(&str, &str, HostFn)] = &[
    ("+", "add", add),
    ("-", "sub", sub),
    ("*", "mul", mul),
    ("/", "div", div),
    ("list", "list", list),
    ("prn", "prn", prn),
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
