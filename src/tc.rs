use std::borrow::{Borrow, BorrowMut};
use std::cell::RefCell;
use std::collections::HashMap;

use std::fmt::{Display, Formatter};
use std::ops::Deref;
use std::rc::{Rc, Weak};
use petgraph::graph::DiGraph;

use crate::ast::*;

// Add proper type checking, with results, make use of Loc

/*
   Idea for type context:
   Make it a tree. i.e. have each scope be a node
   and the tree's "child_of" relation is "scope_contained_in" for scopes.

    TODO: still need a way to refer to type checking results _after_ type checking.
    currently variables store their Type, but do we need more?
*/

pub struct ScopedTypeContext {
    // Wrap parent in RefCell if it turns out that it's needed.
    parent: Weak<ScopedTypeContext>,
    children: RefCell<Vec<Rc<ScopedTypeContext>>>,
    var_type: RefCell<HashMap<String, Type>>,
    var_name: RefCell<HashMap<String, String>>,
    var_counts: Rc<RefCell<HashMap<String, usize>>>,
}

impl ScopedTypeContext {
    pub fn new() -> Rc<ScopedTypeContext> {
        Rc::new(ScopedTypeContext {
            parent: Weak::new(),
            children: RefCell::new(vec![]),
            var_type: RefCell::new(HashMap::new()),
            var_name: RefCell::new(HashMap::new()),
            // Only keeps track of current function
            var_counts: Rc::new(RefCell::new(HashMap::new())),
        })
    }

    pub fn insert(self: &Rc<ScopedTypeContext>, s: String, t: Type) {
        *self.var_counts.deref().borrow_mut().entry(s.clone()).or_insert(0) += 1;
        let count = *self.var_counts.deref().borrow().get(s.as_str()).unwrap();
        self.var_type.borrow_mut().insert(s.clone(), t);
        // let depth = self.depth_of_var(s.as_str()).unwrap();
        // let name = if count != 1 {
        //     format!("{}_{}", s, count)
        // } else {
        //     format!("{}", s)
        // };

        // Necessary for the following program:
        //  let inner_2 = 0;
        //  let inner = 1;
        //  let inner = 1;
        //  inner_2 = 5;
        //  return inner;
        // This should return 1, not 5, but inner_2 would implicitely refer to the last inner, because it wouldn't be translated to inner_2_1.
        let name = format!("{}_{}", s, count);

        self.var_name.borrow_mut().insert(s.clone(), name);

    }

    pub fn clear_var_count(self: &Rc<ScopedTypeContext>) {
        self.var_counts.deref().borrow_mut().clear();
    }

    pub fn new_scope(self: &mut Rc<ScopedTypeContext>) {
        let new_ctx = Rc::new(ScopedTypeContext {
            parent: Rc::downgrade(self),
            children: RefCell::new(vec![]),
            var_type: RefCell::new(HashMap::new()),
            var_name: RefCell::new(HashMap::new()),
            var_counts: self.var_counts.clone(),
        });
        self.children.borrow_mut().push(new_ctx.clone());
        *self = new_ctx;
    }

    pub fn close_scope(self: &mut Rc<ScopedTypeContext>) {
        let parent = self.parent.borrow().upgrade().unwrap();
        *self = parent;
    }

    fn lookup_and_where(self: &Rc<ScopedTypeContext>, s: &str) -> Option<(Type, Rc<ScopedTypeContext>)> {
        let mut curr = Some(self.clone());

        while let Some(ctx) = curr {
            let entry = ctx.var_type.borrow().get(s).map(|t| *t);
            if let Some(t) = entry {
                return Some((t, ctx));
            }
            curr = ctx.parent.borrow().upgrade();
        }

        None
    }

    pub fn lookup_name(self: &Rc<ScopedTypeContext>, s: &str) -> Option<String> {
        let mut curr = Some(self.clone());

        while let Some(ctx) = curr {
            let entry = ctx.var_name.borrow().get(s).map(|t| t.clone());
            if let Some(t) = entry {
                return Some(t);
            }
            curr = ctx.parent.borrow().upgrade();
        }

        None
    }

    pub fn lookup(self: &Rc<ScopedTypeContext>, s: &str) -> Option<Type> {
        self.lookup_and_where(s).map(|(t, _)| t)
    }

    // pub fn depth_of_var(self: &Rc<ScopedTypeContext>, s: &str) -> Option<usize> {
    //     match self.var_type.borrow().get(s) {
    //         Some(_) => Some(1 + self.parent
    //             .upgrade()
    //             .and_then(|p| p.depth_of_var(s))
    //             .unwrap_or(0)
    //         ),
    //         None => self.parent.upgrade().and_then(|p| p.depth_of_var(s))
    //     }
    //
    //
    //     // self.lookup_and_where(s).map(|(_, ctx)| ctx.depth())
    // }
    //
    // pub fn depth(self: &Rc<ScopedTypeContext>) -> usize {
    //     if let Some(parent) = self.parent.upgrade() {
    //         1 + parent.depth()
    //     } else {
    //         0
    //     }
    // }

    // pub fn add_to_graph(self: &Rc<ScopedTypeContext>, graph: &mut DiGraph<&'static str, usize>) {
    //     if let Some(parent) = self.parent.borrow().upgrade() {
    //
    //     }
    // }
    //
    // pub fn graphviz(self: &Rc<ScopedTypeContext>) -> String {}
}

pub struct FuncTypeContext(HashMap<String, (Vec<Param>, Type)>);

impl<P: Borrow<Program>> From<P> for FuncTypeContext {
    fn from(p: P) -> Self {
        let map = p
            .borrow()
            .0
            .iter()
            .map(|fd| (&*fd.name, (&fd.params, &*fd.retty)))
            .map(|(name, (params, retty))| (name.clone(), (params.clone(), retty.clone())))
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
            loc,
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

#[derive(Debug, Clone)]
pub struct TcError(Vec<TcErrorInner>);

impl TcError {
    pub fn new<S: AsRef<str>>(msg: S, loc: Loc) -> TcError {
        TcError(vec![TcErrorInner {
            kind: msg.as_ref().to_string(),
            loc,
        }])
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn print_error_message<S: AsRef<str>>(&self, src: S) {
        self.0
            .iter()
            .for_each(|inner| print!("{}:{}\n", src.as_ref(), inner))
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
    fn from_iter<T: IntoIterator<Item = TcError>>(iter: T) -> Self {
        TcError(
            iter.into_iter()
                .map(|item| item.0.into_iter())
                .flatten()
                .collect::<Vec<_>>(),
        )
    }
}

impl FromIterator<TcErrorInner> for TcError {
    fn from_iter<T: IntoIterator<Item = TcErrorInner>>(iter: T) -> Self {
        TcError(iter.into_iter().collect::<Vec<_>>())
    }
}

type Result<T> = core::result::Result<T, TcError>;

pub struct TypeChecker {
    f_ty_ctx: FuncTypeContext,
    src_file: String,
    curr_s_ty_ctx: Rc<ScopedTypeContext>,
    root_s_ty_ctx: Rc<ScopedTypeContext>,
}

impl TypeChecker {
    pub fn new<S: AsRef<str>>(f_ty_ctx: FuncTypeContext, s: S) -> TypeChecker {
        let s_ty_ctx = ScopedTypeContext::new();
        TypeChecker {
            f_ty_ctx,
            src_file: s.as_ref().to_string(),
            curr_s_ty_ctx: s_ty_ctx.clone(),
            root_s_ty_ctx: s_ty_ctx,
        }
    }

    // If we don't want to mutate the prog while typechecking, an alternative could really be to
    // just redo a pass with the same scoping rules, but that doesn't seem DRY
    pub fn tc_prog(&mut self, prog: &mut WithLoc<Program>) -> Result<()> {
        let mut errs = vec![];

        // if !self.f_ty_ctx.contains_key("main") {
        //     errs.push(TcErrorInner::new("function `main` not found", prog.loc));
        // }

        let err_fdefs = prog
            .iter_mut()
            .filter_map(|fdef| self.tc_fdef(fdef).err())
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

    fn open_scope(&mut self) {
        self.curr_s_ty_ctx.new_scope();
    }

    fn close_scope(&mut self) {
        self.curr_s_ty_ctx.close_scope();
    }

    fn disambig_var(&mut self, v: &mut Var) {
        v.0 = self.curr_s_ty_ctx.lookup_name(v.as_str()).unwrap();
    }

    pub fn tc_fdef(&mut self, fdef: &mut WithLoc<FuncDef>) -> Result<()> {
        let mut errs = vec![];
        // reset var counts, completely different scope.
        self.curr_s_ty_ctx.clear_var_count();
        let mut seen_params: HashMap<String, WithLoc<Var>> = HashMap::new();

        // self.open_scope();

        fdef.params.iter_mut().for_each(|param| {
            self.curr_s_ty_ctx.insert(param.0.to_string(), *param.1);
            self.disambig_var(&mut param.0);
            param.0.set_type(*param.1);

            if let Some(entry) = seen_params.get(param.0.as_str()) {
                errs.push(TcErrorInner::new(
                    format!("duplicate formal parameter `{}`", entry.elem),
                    param.0.loc,
                ))
            } else {
                seen_params.insert(param.0.to_string(), param.0.clone());
            }
        });

        let retty_expected = *fdef.retty;
        let returns_res = self.tc_block(&mut fdef.body, retty_expected);
        match returns_res {
            Err(err) => {
                errs.extend(err);
            }
            Ok(None) => errs.push(TcErrorInner::new(
                format!(
                    "function `{}` is missing an explicit `return` statement",
                    fdef.name
                ),
                fdef.loc,
            )),
            Ok(Some(t)) => {
                if t != *fdef.retty {
                    errs.push(TcErrorInner::new(
                        format!(
                            "function `{}` returns type `{}`, expected `{}`",
                            fdef.name, t, fdef.retty
                        ),
                        fdef.loc,
                    ))
                }
            }
        }

        // self.close_scope();

        if errs.len() > 0 {
            return Err(errs.into_iter().collect());
        }

        Ok(())
    }

    // Return type: Some(retty) if it returns, None if it doesn't return.
    // Change it to WithLoc, so we know there the return type is coming from?
    // TODO: maybe also change all Results to actually be tuples, because we're doing
    // "recoverable" errors? by which I mean grabbing as many errors as possible in one go
    // for that we need to proceed even after a sub-call fails
    pub fn tc_block(&mut self, block: &mut WithLoc<Block>, retty_expected: Type) -> Result<Option<Type>> {
        // open type-check scope
        let prev_scope = self.curr_s_ty_ctx.clone();
        self.open_scope();


        let mut errs = vec![];

        let returns = block.iter_mut().fold(None, |returns, stmt| {
            let stmt_returns = self.tc_stmt(stmt, retty_expected);
            if let Err(err) = stmt_returns {
                errs.extend(err);
                return returns;
            }

            returns.or(stmt_returns.unwrap())
        });

        // close type-check scope
        self.curr_s_ty_ctx = prev_scope;

        if errs.len() > 0 {
            return Err(errs.into_iter().collect());
        }

        Ok(returns)
    }

    pub fn tc_stmt(&mut self, stmt: &mut WithLoc<Stmt>, retty_expected: Type) -> Result<Option<Type>> {
        let mut errs = vec![];

        let res = match &mut stmt.elem {
            Stmt::Testcase() => None,
            Stmt::Unreachable() => None,
            // TODO: typecheck that return is actually returning the correct type here, needs curr_fn string though
            Stmt::Return(e_opt) => {
                let (retty, loc)  = match e_opt {
                    Some(e) => (self.tc_exp(e)?, e.loc),
                    None => (Type::Unit, stmt.loc),
                };

                if retty != retty_expected {
                    return Err(TcError::new(
                        format!("returning type `{}` but expected type `{}`", retty, retty_expected),
                        loc,
                    ));
                }

                Some(retty)
            },
            Stmt::Decl(v, e) => {
                let t_exp_res = self.tc_exp(e);
                if let Err(err) = t_exp_res {
                    errs.extend(err);
                    // Non-recoverable, since we don't know what type to assign to `v`.
                    // Actually, nevermind, this would be fixed by changing Res to (,)
                    return Err(errs.into_iter().collect());
                }

                // let binding opens a new scope
                self.open_scope();

                let t_exp = t_exp_res.unwrap();
                self.curr_s_ty_ctx.insert(v.to_string(), t_exp);
                // println!("inserted: {}", t_exp);
                self.disambig_var(&mut *v);
                v.set_type(t_exp);
                None
            }
            Stmt::Assn(v, e) => {
                // println!("in assn: {}", stmt);

                let curr_ty = self.curr_s_ty_ctx.lookup(v.as_str());
                if curr_ty.is_none() {
                    errs.push(TcErrorInner::new(
                        format!("variable `{}` is assigned to before declared", v),
                        stmt.loc,
                    ));
                    // Non-recoverable, since it might cause cascading errors
                    return Err(errs.into_iter().collect());
                }

                let curr_ty = curr_ty.unwrap();

                let t_exp_res = self.tc_exp(e);
                // println!("in assn: {}", &t_exp_res.clone().unwrap());

                match t_exp_res {
                    Err(err) => {
                        errs.extend(err);
                    }
                    Ok(t) => {
                        v.set_type(t);
                        if t != curr_ty {
                            errs.push(TcErrorInner::new(
                                format!("type `{}` of expression doesn't match type `{}` of variable `{}`", t, curr_ty, v),
                                e.loc,
                            ))
                        }
                    }
                }

                self.disambig_var(&mut *v);
                None
            }
            Stmt::IfElse {
                cond,
                if_branch,
                else_branch,
            } => {
                let cond_t_res = self.tc_exp(cond);
                match cond_t_res {
                    Err(err) => errs.extend(err),
                    Ok(t) if t != Type::Bool => errs.push(TcErrorInner::new(
                        format!(
                            "if condition is of type `{}`, must be of type `{}`",
                            t,
                            Type::Bool
                        ),
                        cond.loc,
                    )),
                    _ => {}
                }

                // go on, treat cond as if it were a bool.

                let if_res = self.tc_block(if_branch, retty_expected);
                let else_res = self.tc_block(else_branch, retty_expected);

                // Check if either if_res or else_res has is an error. we want both errors, however
                if let Err(err) = if_res.clone() {
                    errs.extend(err);
                }
                if let Err(err) = else_res.clone() {
                    errs.extend(err);
                }

                // But we need return-types moving forward, hence early return
                if errs.len() > 0 {
                    return Err(errs.into_iter().collect());
                }

                let if_ret = if_res.unwrap();
                let else_ret = else_res.unwrap();

                if_ret.and(else_ret)
            }
            Stmt::While { cond, block } => {
                let cond_t_res = self.tc_exp(cond);
                match cond_t_res {
                    Err(err) => errs.extend(err),
                    Ok(t) if t != Type::Bool => errs.push(TcErrorInner::new(
                        format!(
                            "while condition is of type `{}`, must be of type `{}`",
                            t,
                            Type::Bool
                        ),
                        cond.loc,
                    )),
                    _ => {}
                }

                // go on, treat cond as if it were a bool.

                let block_res = self.tc_block(block, retty_expected);

                match block_res {
                    Err(err) => {
                        errs.extend(err);
                        // arbitrary choice. has no effect:
                        None
                    }
                    Ok(t) => t,
                }
            }
        };

        if errs.len() > 0 {
            return Err(errs.into_iter().collect());
        }

        Ok(res)
    }

    pub fn tc_exp(&mut self, exp: &mut WithLoc<Expr>) -> Result<Type> {
        match &mut exp.elem {
            Expr::IntLit(_) => Ok(Type::Int),
            Expr::BoolLit(_) => Ok(Type::Bool),
            Expr::Var(v) => {
                let t = self.curr_s_ty_ctx.lookup(v.as_str());
                match t {
                    None => Err(TcError::new(
                        format!("variable `{}` used before declared", v),
                        v.loc,
                    )),
                    Some(t) => {
                        self.disambig_var(&mut *v);
                        v.set_type(t);
                        Ok(t)
                    },
                }
            }
            Expr::Call(name, args) => {
                let (param_tys, retty) = &self.f_ty_ctx[name.as_str()];
                let retty = *retty;

                let params_len = param_tys.len();
                let args_len = args.len();

                if params_len != args_len {
                    // Returning, because it makes no sense to typecheck unmatching iters.. or does it?
                    return Err(TcError::new(
                        format!("argument count mismatch for call to `{}`: {} args given but function expects {}", name, args_len, params_len),
                        exp.loc,
                    ))
                }

                let param_tys = param_tys.iter().map(|p| *p.1).collect::<Vec<_>>();

                let err = param_tys.into_iter().zip(args.iter_mut()).map(|(param_t, arg)| {
                    let arg_t = self.tc_exp(arg)?;

                    if arg_t != param_t {
                        return Err(TcError::new(
                            format!("argument type mismatch for call to `{}`: expected type `{}` got type `{}`", name, param_t, arg_t),
                            arg.loc,
                        ))
                    }

                    Ok(())
                }).filter_map(|res| res.err()).collect::<TcError>();

                if !err.is_empty() {
                    Err(err)
                } else {
                    Ok(retty)
                }
            }
            Expr::BinOp(op, left, right) => {
                let op_type = op.get_type();
                // TODO: don't short-circuit yet, but collect *both* errors and then break out
                let left_t = self.tc_exp(left)?;
                let right_t = self.tc_exp(right)?;

                let mut errs = vec![];

                if op_type.0 .0 != left_t {
                    errs.push(TcErrorInner::new(
                        format!(
                            "first argument of `{}` is type `{}`, but must be type `{}`",
                            op, left_t, op_type.0 .0
                        ),
                        left.loc,
                    ))
                }
                if op_type.0 .1 != right_t {
                    errs.push(TcErrorInner::new(
                        format!(
                            "second argument of `{}` is type `{}`, but must be type `{}`",
                            op, right_t, op_type.0 .1
                        ),
                        right.loc,
                    ))
                }

                if errs.len() > 0 {
                    return Err(errs.into_iter().collect());
                }

                Ok(op_type.1)
            }
            Expr::UnOp(op, inner) => {
                let op_type = op.get_type();
                let inner_t = self.tc_exp(inner)?;

                if op_type.0 != inner_t {
                    return Err(TcError::new(
                        format!(
                            "argument of `{}` is type {}, but must be type {}",
                            op, inner_t, op_type.0
                        ),
                        inner.loc,
                    ));
                }

                Ok(op_type.1)
            }
        }
    }
}

// THESE ARE USED FOR THE PARSER AT THE MOMENT:

pub fn type_of(e: &Expr) -> Type {
    // Assumes the expression is type checked, then gives it a type.
    // The following implication holds:
    // Expression is typechecked ==> type_of(e) = it's actual, typechecked type
    use BinOpcode::*;
    use Type::*;
    use UnOpcode::*;

    match e {
        Expr::IntLit(_) => Int,
        Expr::BoolLit(_) => Bool,
        Expr::Var(WithLoc {
            elem: Var(_, t), ..
        }) => *t,
        // TODO: Call needs global function type map
        // we're kind of not caring about type_of.
        Expr::Call(_, _) => Unit,
        Expr::BinOp(
            WithLoc {
                elem: Add | Sub | Mul | Div | Mod,
                ..
            },
            _,
            _,
        ) => Int,
        Expr::BinOp(
            WithLoc {
                elem: Eq | Ne | Lt | Gt | Le | Ge | And | Or,
                ..
            },
            _,
            _,
        ) => Bool,
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
