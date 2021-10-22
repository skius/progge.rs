use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use crate::ast::*;

// Add proper type checking, with results, make use of Loc

pub struct FuncTypeContext(HashMap<String, (Vec<Param>, Type)>);

impl<P: Borrow<Program>> From<P> for FuncTypeContext {
    fn from(p: P) -> Self {
        let map = p.borrow().0.iter()
            .map(|fd| (&*fd.name ,(&fd.params, &*fd.retty)))
            .map(|(name, (params, retty))| {
                (name.clone(), (params.clone(), retty.clone()))
            })
            .collect::<HashMap<_, _>>();

        FuncTypeContext(map)
    }
}

impl Deref for FuncTypeContext {
    type Target = HashMap<String, (Vec<Param>, Type)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct TcErrorInner {
    kind: String,
    loc: Loc,
}

impl TcErrorInner {
    pub fn new<S: AsRef<str>>(msg: S, loc: Loc) -> TcErrorInner {
        TcErrorInner {
            kind: msg.as_ref().to_string(),
            loc
        }
    }
}

impl Display for TcErrorInner {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.loc.line, f)?;
        f.write_str(":")?;
        Display::fmt(&self.loc.col, f)?;
        f.write_str(": ")?;
        Display::fmt(&self.kind, f)
    }
}

#[derive(Debug)]
pub struct TcError(Vec<TcErrorInner>);

impl TcError {
    pub fn new<S: AsRef<str>>(msg: S, loc: Loc) -> TcError {
        TcError(vec![TcErrorInner {
            kind: msg.as_ref().to_string(),
            loc
        }])
    }

    pub fn print_error_message<S: AsRef<str>>(&self, src: S) {
        self.0.iter()
            .for_each(|inner| {
                print!("{}:{}\n", src.as_ref(), inner)
            })
    }
}

impl IntoIterator for TcError {
    type Item = TcErrorInner;
    type IntoIter = std::vec::IntoIter<TcErrorInner>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

// TODO: might get rid of FromIterator
impl FromIterator<TcError> for TcError {
    fn from_iter<T: IntoIterator<Item=TcError>>(iter: T) -> Self {
        TcError(
            iter.into_iter()
                .map(|item| item.0.into_iter())
                .flatten()
                .collect::<Vec<_>>()

        )
    }
}

impl FromIterator<TcErrorInner> for TcError {
    fn from_iter<T: IntoIterator<Item=TcErrorInner>>(iter: T) -> Self {
        TcError(
            iter.into_iter()
                .collect::<Vec<_>>()

        )
    }
}

type Result<T> = core::result::Result<T, TcError>;

pub struct TypeChecker {
    f_ty_ctx: FuncTypeContext,
    src_file: String,
}

impl TypeChecker {
    pub fn new<S: AsRef<str>>(f_ty_ctx: FuncTypeContext, s: S) -> TypeChecker {
        TypeChecker {
            f_ty_ctx,
            src_file: s.as_ref().to_string(),
        }
    }


    pub fn tc_prog(&self, prog: &WithLoc<Program>) -> Result<()> {
        let mut errs = vec![];

        if !self.f_ty_ctx.contains_key("main") {
            errs.push(TcErrorInner::new("function `main` not found", prog.loc));
        }

        let err_fdefs = prog
            .iter()
            .filter_map(|fdef| {
                self.tc_fdef(fdef).err()
            })
            .map(|err| err.into_iter())
            .flatten()
            .collect::<Vec<_>>();
        // TODO: See if there's a smarter way?
        errs.extend(err_fdefs);
        if errs.len() > 0 {
            return Err(errs.into_iter().collect());
        }

        Ok(())
    }

    pub fn tc_fdef(&self, fdef: &WithLoc<FuncDef>) -> Result<()> {
        let mut errs = vec![];

        let mut seen_params: HashMap<String, WithLoc<Var>> = HashMap::new();

        fdef.params.iter().for_each(|param| {
           if let Some(entry) = seen_params.get(param.0.as_str()) {
                errs.push(TcErrorInner::new(
                    format!("duplicate formal parameter `{}`", entry.elem),
                        param.0.loc,
                ))
           } else {
               seen_params.insert(param.0.to_string(), param.0.clone());
           }
        });

        self.tc_block(&fdef.body);

        if errs.len() > 0 {
            return Err(errs.into_iter().collect());
        }

        Ok(())
    }

    // Return type: (retty, returns?)
    pub fn tc_block(&self, block: &WithLoc<Block>) -> Result<(Type, bool)> {
        Ok((Type::Unit, true))
    }
}

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
