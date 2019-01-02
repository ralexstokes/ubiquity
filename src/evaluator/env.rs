use std::collections::HashMap;
use std::fmt;

use itertools::Itertools;

use crate::reader::Expr;

type Scope = HashMap<String, Expr>;

#[derive(Debug)]
pub struct Env<'e> {
    bindings: Scope,
    parent: Option<&'e Env<'e>>,
}

impl<'e> Env<'e> {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub fn with_parent(parent: &'e Env) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(parent),
        }
    }

    pub fn add_bindings(&mut self, bindings: &[(String, Expr)]) {
        bindings.into_iter().for_each(|(k, v)| {
            self.bindings.insert(k.clone(), v.clone());
        })
    }

    pub fn lookup(&self, key: &str) -> Option<&Expr> {
        self.bindings
            .get(key)
            .or_else(|| self.parent.and_then(|parent| parent.lookup(key)))
    }
}

impl<'e> fmt::Display for Env<'e> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Env (some-parent? {:?}) {{", self.parent.is_some())?;
        write!(
            f,
            "{}",
            self.bindings
                .iter()
                .map(|(k, v)| format!("{:?} {}", k, v))
                .format(" ")
        )?;
        write!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_nest_envs() {
        let mut parent = Env::new();
        let bindings = &[("hi".into(), Expr::Bool(true)), ("there".into(), Expr::Nil)];
        parent.add_bindings(bindings);

        let mut child = Env::with_parent(&parent);
        let child_bindings = &[("in-the-child".into(), Expr::Number(22))];
        child.add_bindings(child_bindings);
    }
}
