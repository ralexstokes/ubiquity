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
                        Expr::Number(next) => {
                            result = result + *next;
                        }
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
                        Expr::Number(next) => {
                            result = result - *next;
                        }
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

static PRELUDE_BINDINGS: &[(&str, &str, HostFn)] = &[("+", "add", add), ("-", "sub", sub)];

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
