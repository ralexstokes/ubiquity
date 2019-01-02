use crate::reader::{Expr, Result};

use super::env::Env;

fn plus(args: Vec<Expr>) -> Result<Expr> {
    Ok(Expr::Number(
        args.into_iter()
            .map(|arg| match arg {
                Expr::Number(n) => n,
                _ => 0,
            })
            .sum(),
    ))
}

static PRELUDE_BINDINGS: &[(&str, Expr)] = &[("+", Expr::PrimitiveFn(plus))];

pub fn env() -> Env<'static> {
    let bindings = PRELUDE_BINDINGS
        .into_iter()
        .map(|(k, v)| (String::from(*k), v.clone()))
        .collect::<Vec<(String, Expr)>>();
    let mut env = Env::new();
    env.add_bindings(bindings.as_slice());
    env
}
