use std::collections::HashMap;
use crate::ast::*;

// Add proper type checking, with results, make use of Loc

pub fn type_of(e: &Expr) -> Type {
    // Assumes the expression is type checked, then gives it a type.
    // The following implication holds:
    // Expression is typechecked ==> type_of(e) = it's actual, typechecked type
    use Type::*;
    use BinOpcode::*;
    use UnOpcode::*;

    match e {
        Expr::IntLit(_) => Int,
        Expr::BoolLit(_) => Bool,
        Expr::Var(WithLoc { elem: Var(_, t), .. }) => *t,
        // TODO: Call needs global function type map
        Expr::Call(_, _) => panic!("Call not handled"),
        Expr::BinOp(WithLoc { elem: (Add | Sub | Mul | Div | Mod), .. }, _, _) => Int,
        Expr::BinOp(WithLoc { elem: (Eq | Ne | Lt | Gt | Le | Ge | And | Or), .. }, _, _) => Bool,
        Expr::UnOp(WithLoc { elem: Neg, .. }, _) => Int,
        Expr::UnOp(WithLoc { elem: Not, .. }, _) => Bool,
    }
}

pub struct VariableTypeContext(Vec<HashMap<String, Type>>);

impl VariableTypeContext {
    pub fn new() -> VariableTypeContext {
        VariableTypeContext(Vec::new())
    }

    pub fn insert(&mut self, s: String, t: Type) {
        self.0.last_mut().unwrap().insert(s, t);
    }

    pub fn new_scope(&mut self) {
        self.0.push(HashMap::new());
    }

    pub fn close_scope(&mut self) {
        self.0.pop().unwrap();
    }

    pub fn lookup(&self, s: &str) -> Option<Type> {
        for type_map in &self.0 {
            if type_map.contains_key(s) {
                return Some(type_map[s]);
            }
        }

        None
    }
}
