mod env;
mod evaluator;
pub mod prelude;

use crate::reader;

pub use self::env::Env;
pub use self::evaluator::Result;
pub use crate::reader::Expr;

pub fn eval(input: &str, env: &mut Env) -> Vec<Result<Expr>> {
    let results = reader::read(input);

    results
        .into_iter()
        .map(|result| {
            result
                .map_err(|e| e.into())
                .and_then(|expr| evaluator::eval_expr(expr, env))
        })
        .collect::<Vec<_>>()
}
