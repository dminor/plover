use std::collections::HashMap;

use crate::typeinfer::Type;

fn unify_variable<S: ::std::hash::BuildHasher>(
    var: &str,
    x: &Type,
    bindings: &mut HashMap<String, Type, S>,
) -> bool {
    match x {
        Type::Polymorphic(s) => match bindings.get(var) {
            Some(Type::Polymorphic(t)) => {
                if s == t {
                    true
                } else {
                    unify_variable(&t.to_string(), &Type::Polymorphic(s.to_string()), bindings)
                }
            }
            Some(t) => {
                let s = s.to_string();
                let t = t.clone();
                bindings.insert(s, t);
                true
            }
            None => match bindings.get(s) {
                Some(token) => unify_variable(&s.to_string(), &token.clone(), bindings),
                None => {
                    bindings.insert(var.to_string(), Type::Polymorphic(s.to_string()));
                    true
                }
            },
        },
        s => match bindings.get(var) {
            Some(Type::Polymorphic(t)) => unify_variable(&t.to_string(), s, bindings),
            Some(t) => s == t,
            None => {
                bindings.insert(var.to_string(), s.clone());
                true
            }
        },
    }
}

pub fn unify<S: ::std::hash::BuildHasher>(
    x: &[Type],
    y: &[Type],
    bindings: &mut HashMap<String, Type, S>,
) -> bool {
    let mut x_iter = x.iter();
    let mut y_iter = y.iter();
    let mut matched = true;

    while matched {
        match x_iter.next() {
            Some(Type::Polymorphic(s)) => match y_iter.next() {
                Some(token) => {
                    matched = unify_variable(s, &token, bindings);
                }
                None => {
                    matched = false;
                }
            },
            Some(Type::Tuple(s_elements)) => match y_iter.next() {
                Some(Type::Polymorphic(t)) => {
                    matched = unify_variable(t, &Type::Tuple(s_elements.to_vec()), bindings);
                }
                Some(Type::Tuple(t_elements)) => {
                    matched = unify(&s_elements[..], &t_elements[..], bindings);
                }
                _ => {
                    matched = false;
                }
            },
            Some(s) => match y_iter.next() {
                Some(Type::Polymorphic(t)) => {
                    matched = unify_variable(t, s, bindings);
                }
                Some(t) => {
                    matched = s == t;
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
        let x = vec![Type::Integer, Type::Integer];

        let mut bindings: HashMap<String, Type> = HashMap::new();
        assert!(unify(&x, &x, &mut bindings));
        assert_eq!(bindings.len(), 0);

        let y = vec![Type::Integer, Type::Unit];

        let mut bindings: HashMap<String, Type> = HashMap::new();
        assert!(!unify(&x, &y, &mut bindings));
        assert_eq!(bindings.len(), 0);

        let y = vec![Type::Polymorphic("'a".to_string()), Type::Integer];

        let mut bindings: HashMap<String, Type> = HashMap::new();
        assert!(unify(&x, &y, &mut bindings));
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings.get("'a"), Some(&Type::Integer));

        let y = vec![
            Type::Polymorphic("'a".to_string()),
            Type::Integer,
            Type::Integer,
        ];

        let mut bindings: HashMap<String, Type> = HashMap::new();
        assert!(!unify(&x, &y, &mut bindings));
    }
}
