use std::collections::HashMap;
use std::fmt;

use crate::typeinfer::Type;

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Type(Type),
    Variable(String),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Type(s) => write!(f, "{}", s),
            Term::Variable(s) => write!(f, "{}", s),
        }
    }
}

fn unify_variable<S: ::std::hash::BuildHasher>(
    var: &str,
    x: &Term,
    bindings: &mut HashMap<String, Term, S>,
) -> bool {
    match x {
        Term::Type(s) => match bindings.get(var) {
            Some(Term::Type(t)) => s == t,
            Some(Term::Variable(t)) => {
                unify_variable(&t.to_string(), &Term::Type(s.clone()), bindings)
            }
            None => {
                bindings.insert(var.to_string(), Term::Type(s.clone()));
                true
            }
        },
        Term::Variable(s) => match bindings.get(var) {
            Some(Term::Type(t)) => {
                let s = s.to_string();
                let t = t.clone();
                bindings.insert(s, Term::Type(t));
                true
            }
            Some(Term::Variable(t)) => {
                if s == t {
                    true
                } else {
                    unify_variable(&t.to_string(), &Term::Variable(s.to_string()), bindings)
                }
            }
            None => match bindings.get(s) {
                Some(token) => unify_variable(&s.to_string(), &token.clone(), bindings),
                None => {
                    bindings.insert(var.to_string(), Term::Variable(s.to_string()));
                    true
                }
            },
        },
    }
}

pub fn unify<S: ::std::hash::BuildHasher>(
    x: &[Term],
    y: &[Term],
    bindings: &mut HashMap<String, Term, S>,
) -> bool {
    let mut x_iter = x.iter();
    let mut y_iter = y.iter();
    let mut matched = true;

    while matched {
        match x_iter.next() {
            Some(Term::Type(s)) => match y_iter.next() {
                Some(Term::Type(t)) => {
                    matched = s == t;
                }
                Some(Term::Variable(t)) => {
                    matched = unify_variable(t, &Term::Type(s.clone()), bindings);
                }
                None => {
                    matched = false;
                }
            },
            Some(Term::Variable(s)) => match y_iter.next() {
                Some(token) => {
                    matched = unify_variable(s, &token, bindings);
                }
                None => {
                    matched = false;
                }
            },
            None => {
                matched = y_iter.next().is_none();
                break;
            }
        }
    }

    matched
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::unification::*;

    #[test]
    fn unifications() {
        let x = vec![Term::Type(Type::Integer), Term::Type(Type::Integer)];

        let mut bindings: HashMap<String, Term> = HashMap::new();
        assert!(unify(&x, &x, &mut bindings));
        assert_eq!(bindings.len(), 0);

        let y = vec![Term::Type(Type::Integer), Term::Type(Type::Unit)];

        let mut bindings: HashMap<String, Term> = HashMap::new();
        assert!(!unify(&x, &y, &mut bindings));
        assert_eq!(bindings.len(), 0);

        let y = vec![Term::Variable("'a".to_string()), Term::Type(Type::Integer)];

        let mut bindings: HashMap<String, Term> = HashMap::new();
        assert!(unify(&x, &y, &mut bindings));
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings.get("'a"), Some(&Term::Type(Type::Integer)));

        let y = vec![
            Term::Variable("'a".to_string()),
            Term::Type(Type::Integer),
            Term::Type(Type::Integer),
        ];

        let mut bindings: HashMap<String, Term> = HashMap::new();
        assert!(!unify(&x, &y, &mut bindings));
    }
}
