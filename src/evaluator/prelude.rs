use crate::reader::{Expr, HostFn, Result};

use super::env::Env;

fn add(args: Vec<Expr>) -> Result<Expr> {
    Ok(Expr::Number(
        args.into_iter()
            .map(|arg| match arg {
                Expr::Number(n) => n,
                _ => 0,
            })
            .sum(),
    ))
}

static PRELUDE_BINDINGS: &[(&str, &str, HostFn)] = &[("+", "add", add)];

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
