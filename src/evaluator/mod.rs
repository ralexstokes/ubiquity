use std::result;

use crate::reader::Expr;

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug, PartialEq)]
pub enum Error {}

pub fn eval(exprs: Vec<Expr>) -> Vec<Result<Expr>> {
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
        Symbol(s) => Symbol(s),
        Keyword(s) => Keyword(s),
        List(exprs) => List(exprs),
        Vector(exprs) => Vector(exprs),
        Map(exprs) => Map(exprs),
        Set(exprs) => Set(exprs),
    };
    Ok(node)
}

#[cfg(test)]
mod tests {
    use super::Expr::*;
    use super::*;

    fn run_eval(exprs: Vec<Expr>) -> Vec<Result<Expr>> {
        eval(exprs)
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
                String("there".into()), //
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
