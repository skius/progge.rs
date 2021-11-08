use std::borrow::{Borrow, BorrowMut};
use std::cell::RefCell;
use std::collections::HashMap;

use std::fmt::{Display, Formatter};
use std::ops::{Deref, Range};
use std::rc::{Rc, Weak};
use ariadne::{Color, ColorGenerator, Fmt, Label, Report, ReportBuilder, Source};
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

pub struct FuncTypeContext(HashMap<String, (WithLoc<String>, WithLoc<Vec<Param>>, WithLoc<Type>)>);

impl<P: Borrow<Program>> From<P> for FuncTypeContext {
    fn from(p: P) -> Self {
        let map = p
            .borrow()
            .0
            .iter()
            .map(|fd| (&fd.name, (&fd.params, &fd.retty)))
            .map(|(name, (params, retty))| (name.elem.clone(), (name.clone(), params.clone(), retty.clone())))
            .collect::<HashMap<_, _>>();

        FuncTypeContext(map)
    }
}

impl Deref for FuncTypeContext {
    type Target = HashMap<String, (WithLoc<String>, WithLoc<Vec<Param>>, WithLoc<Type>)>;

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

    pub fn add<S: ToString>(&mut self, msg: S, loc: Loc) {
        self.0.push(TcErrorInner {
            kind: msg.to_string(),
            loc,
        });
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
    src_content: String,
    errors: TcError,
    curr_s_ty_ctx: Rc<ScopedTypeContext>,
    root_s_ty_ctx: Rc<ScopedTypeContext>,
}

impl TypeChecker {
    pub fn new<S: AsRef<str>>(f_ty_ctx: FuncTypeContext, src_file: S, src: String) -> TypeChecker {
        let s_ty_ctx = ScopedTypeContext::new();
        TypeChecker {
            f_ty_ctx,
            src_file: src_file.as_ref().to_string(),
            src_content: src,
            errors: TcError(vec![]),
            curr_s_ty_ctx: s_ty_ctx.clone(),
            root_s_ty_ctx: s_ty_ctx,
        }
    }

    fn report(&self, msg: &str, offset: usize) -> ReportBuilder<(&String, Range<usize>)> {
        Report::build(ariadne::ReportKind::Error, &self.src_file, offset)
        .with_message::<&str>(msg)

    }

    // If we don't want to mutate the prog while typechecking, an alternative could really be to
    // just redo a pass with the same scoping rules, but that doesn't seem DRY
    pub fn tc_prog(&mut self, prog: &mut WithLoc<Program>) -> Result<()> {

        // if !self.f_ty_ctx.contains_key("main") {
        //     errs.push(TcErrorInner::new("function `main` not found", prog.loc));
        // }

        let mut seen_funcs: HashMap<String, WithLoc<String>> = HashMap::new();

        prog.iter_mut()
            .for_each(|fdef| {
                if let Some(entry) = seen_funcs.get(fdef.name.as_str()) {
                    let [color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, fdef.name.loc.start)
                        .with_message::<&str>("duplicate function name")
                        .with_label(
                            Label::new(
                                (&self.src_file, fdef.name.loc.range())
                            )
                                .with_message(
                                    format!("function {} redefined here", fdef.name.as_str().fg(color1))
                                )
                                .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, entry.loc.range())
                            )
                                .with_message(
                                    format!("first definition of function {} here", entry.as_str().fg(color2))
                                )
                                .with_color(color2)
                        )
                        .with_note(
                            format!("function names must be distinct")
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!("duplicate function name `{}`", entry.elem),
                        fdef.name.loc
                    );
                } else {
                    seen_funcs.insert(fdef.name.elem.clone(), fdef.name.clone());
                }

                self.tc_fdef(fdef);
            });

        if !self.errors.is_empty() {
            return Err(self.errors.clone());
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
        if let Some(s) = self.curr_s_ty_ctx.lookup_name(v.as_str()) {
            v.0 = s;
        } // If we can't find the variable in the type context, it means it's not defined and was propagated through errors.
    }

    pub fn tc_fdef(&mut self, fdef: &mut WithLoc<FuncDef>) {
        // reset var counts, completely different scope.
        self.curr_s_ty_ctx.clear_var_count();
        let mut seen_params: HashMap<String, WithLoc<Var>> = HashMap::new();

        // self.open_scope();

        fdef.params.iter_mut().for_each(|param| {
            param.0.set_type(*param.1);

            if let Some(entry) = seen_params.get(param.0.as_str()) {
                let [color1, color2] = colors();

                Report::build(ariadne::ReportKind::Error, &self.src_file, param.0.loc.start)
                    .with_message::<&str>("duplicate formal parameter")
                    .with_label(
                        Label::new(
                            (&self.src_file, param.0.loc.range())
                        )
                        .with_message(
                            format!("parameter {} redefined here", param.0.to_string().fg(color1))
                        )
                        .with_color(color1)
                    )
                    .with_label(
                        Label::new(
                            (&self.src_file, entry.loc.range())
                        )
                        .with_message(
                            format!("first definition of parameter {} here", entry.to_string().fg(color2))
                        )
                        .with_color(color2)
                    )
                    .with_note(
                        format!("a function's formal parameters must be distinct")
                    )
                    .finish()
                    .print((&self.src_file, Source::from(self.src_content.clone())))
                    .unwrap();

                self.errors.add(
                    format!("duplicate formal parameter `{}`", entry.elem),
                    param.0.loc,
                );
            } else {
                seen_params.insert(param.0.to_string(), param.0.clone());
                self.curr_s_ty_ctx.insert(param.0.to_string(), *param.1);
                self.disambig_var(&mut param.0);
            }
        });

        let retty_expected = fdef.retty.clone();
        let returns_res = self.tc_block(&mut fdef.body, retty_expected);
        match returns_res {
            None => {
                let [color_ret, color1] = colors();

                Report::build(ariadne::ReportKind::Error, &self.src_file, fdef.name.loc.start)
                    .with_message::<&str>("function may not return")
                    .with_label(
                        Label::new(
                            (&self.src_file, fdef.name.loc.range())
                        )
                        .with_message(
                            format!("function {} may not {}", fdef.name.to_string().fg(color1), "return".fg(color_ret))
                        )
                        .with_color(color1)
                    )
                    .with_note(
                        format!("all paths through a function must end in a {}-statement", "return".fg(color_ret))
                    )
                    .finish()
                    .print((&self.src_file, Source::from(self.src_content.clone())))
                    .unwrap();

                self.errors.add(
                    format!(
                        "function `{}` is missing an explicit `return` statement",
                        fdef.name
                    ),
                    fdef.loc,
                )
            },
            Some(t) => {
                // I don't think we need this, return handles this already
                // if t != *fdef.retty {
                //     self.errors.add(
                //         format!(
                //             "function `{}` returns type `{}`, expected `{}`",
                //             fdef.name, t, fdef.retty
                //         ),
                //         fdef.loc,
                //     )
                // }
            }
        }
    }

    // Return type: Some(retty) if it returns, None if it doesn't return.
    // Change it to WithLoc, so we know there the return type is coming from?
    // TODO: maybe also change all Results to actually be tuples, because we're doing
    // "recoverable" errors? by which I mean grabbing as many errors as possible in one go
    // for that we need to proceed even after a sub-call fails
    pub fn tc_block(&mut self, block: &mut WithLoc<Block>, retty_expected: WithLoc<Type>) -> Option<Type> {
        // open type-check scope
        let prev_scope = self.curr_s_ty_ctx.clone();
        self.open_scope();


        let returns = block.iter_mut().fold(None, |returns, stmt| {
            let stmt_returns = self.tc_stmt(stmt, retty_expected.clone());

            returns.or(stmt_returns)
        });

        // close type-check scope
        self.curr_s_ty_ctx = prev_scope;

        returns
    }

    pub fn tc_stmt(&mut self, stmt: &mut WithLoc<Stmt>, retty_expected: WithLoc<Type>) -> Option<Type> {

        let res = match &mut stmt.elem {
            Stmt::Testcase() => None,
            Stmt::Unreachable() => None,
            // TODO: typecheck that return is actually returning the correct type here, needs curr_fn string though
            Stmt::Return(e_opt) => {
                let (retty, loc)  = match e_opt {
                    Some(e) => (self.tc_exp(e), e.loc),
                    None => (Type::Unit, stmt.loc),
                };

                if retty != *retty_expected {
                    let [color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, loc.start)
                        .with_message::<&str>("return type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, loc.range())
                            )
                                .with_message(
                                    format!("returned expression has type {}", retty.to_string().fg(color1))
                                )
                                .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, retty_expected.loc.range())
                            )
                                .with_message(
                                    format!("expected return type is {}", retty_expected.to_string().fg(color2))
                                )
                                .with_color(color2)
                        )
                        .with_note(
                            format!("functions must return their specified types")
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!("returning type `{}` but expected type `{}`", retty, retty_expected),
                        loc,
                    );
                }

                Some(retty)
            },
            Stmt::Decl(v, e) => {
                let t = self.tc_exp(e);


                // let binding opens a new scope
                self.open_scope();

                self.curr_s_ty_ctx.insert(v.to_string(), t);
                // println!("inserted: {}", t_exp);
                self.disambig_var(&mut *v);
                v.set_type(t);
                None
            }
            Stmt::Assn(v, e) => {
                // println!("in assn: {}", stmt);

                let t = self.tc_exp(e);
                // println!("in assn: {}", &t_exp_res.clone().unwrap());

                let mut curr_ty = self.curr_s_ty_ctx.lookup(v.as_str());
                if curr_ty.is_none() {
                    let [color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, v.loc.start)
                        .with_message::<&str>("variable assigned to before declared")
                        .with_label(
                            Label::new(
                                (&self.src_file, v.loc.range())
                            )
                                .with_message(
                                    format!("variable {} assigned to before declared", v.elem.as_str().fg(color1))
                                )
                                .with_color(color1)
                        )
                        .with_note(
                            format!(
                                "variables must be introduced e.g. by a {}-statement prior to being assigned",
                                "let".fg(color2)
                            )
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!("variable `{}` is assigned to before declared", v),
                        stmt.loc,
                    );

                    // To allow further type checking, we just pretend the variable has been declared with the type returned by tc_exp
                    curr_ty = Some(t);
                    self.curr_s_ty_ctx.insert(v.to_string(), t);
                }

                let curr_ty = curr_ty.unwrap();



                // To allow continuing type checking, we set the type to the possibly incorrect expression's type
                v.set_type(t);

                if t != curr_ty && t != Type::Unknown {
                    let [color_var, color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, e.loc.start)
                        .with_message::<&str>("variable assignment type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, e.loc.range())
                            )
                                .with_message(
                                    format!(
                                        "assigned expression of type {}, but variable {} is of type {}",
                                        t.fg(color2),
                                        v.elem.as_str().fg(color_var),
                                        curr_ty.fg(color1),
                                    )
                                )
                                .with_color(color2)
                        )
                        .with_note(
                            format!(
                                "variables must always be assigned their type"
                            )
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!("type `{}` of expression doesn't match type `{}` of variable `{}`", t, curr_ty, v),
                        e.loc,
                    );
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
                if cond_t_res != Type::Bool {
                    let [color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, cond.loc.start)
                        .with_message::<&str>("condition type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, cond.loc.range())
                            )
                                .with_message(
                                    format!(
                                        "condition is of type {}, but must be of type {}",
                                        cond_t_res.to_string().fg(color1),
                                        "bool".fg(color2)
                                    )
                                )
                                .with_color(color1)
                        )
                        .with_note(
                            format!(
                                "conditions must always be {}s",
                                "bool".fg(color2)
                            )
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                     format!(
                            "if condition is of type `{}`, must be of type `{}`",
                            cond_t_res,
                            Type::Bool
                        ),
                        cond.loc
                    );
                }

                // go on, treat cond as if it were a bool.

                let if_res = self.tc_block(if_branch, retty_expected.clone());
                let else_res = self.tc_block(else_branch, retty_expected.clone());

                if_res.and(else_res)
            }
            Stmt::While { cond, block } => {
                let cond_t_res = self.tc_exp(cond);
                if cond_t_res != Type::Bool {
                    let [color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, cond.loc.start)
                        .with_message::<&str>("condition type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, cond.loc.range())
                            )
                                .with_message(
                                    format!(
                                        "condition is of type {}, but must be of type {}",
                                        cond_t_res.to_string().fg(color1),
                                        "bool".fg(color2)
                                    )
                                )
                                .with_color(color1)
                        )
                        .with_note(
                            format!(
                                "conditions must always be {}s",
                                "bool".fg(color2)
                            )
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                     format!(
                            "while condition is of type `{}`, must be of type `{}`",
                            cond_t_res,
                            Type::Bool
                        ),
                        cond.loc
                    );
                }
            

                // go on, treat cond as if it were a bool.

                let block_res = self.tc_block(block, retty_expected.clone());

                block_res
            }
        };

        res
    }

    pub fn tc_exp(&mut self, exp: &mut WithLoc<Expr>) -> Type {
        match &mut exp.elem {
            Expr::IntLit(_) => Type::Int,
            Expr::BoolLit(_) => Type::Bool,
            Expr::Var(v) => {
                let t = self.curr_s_ty_ctx.lookup(v.as_str());
                match t {
                    None => {
                        // TODO: Pass "print errors" flag that prints errors with ariadne live, otherwise just accumulate them and return
                        // TODO: extract v.loc.start..v.loc.end into v.loc.span()

                        let [color1, color2] = colors();

                        Report::build(ariadne::ReportKind::Error, &self.src_file, v.loc.start)
                            .with_message::<&str>("variable used before declared")
                            .with_label(
                                Label::new(
                                    (&self.src_file, v.loc.start..v.loc.end)
                                )
                                .with_message(
                                    format!("variable {} used before declared", v.elem.as_str().fg(color1))
                                )
                                .with_color(color1)
                            )
                            .with_note(
                                format!(
                                    "variables must be introduced e.g. by a {}-statement prior to being used",
                                    "let".fg(color2)
                                )
                            )
                            .finish()
                            .print((&self.src_file, Source::from(self.src_content.clone())))
                            .unwrap();

                        self.errors.add(
                            format!("variable `{}` used before declared", v),
                            v.loc,
                        );
                        Type::Unknown
                    },
                    Some(t) => {
                        self.disambig_var(&mut *v);
                        v.set_type(t);
                        t
                    },
                }
            }
            Expr::Call(name, args) => {
                // TODO: Typecheck that function exists
                let (_, param_tys, retty) = &self.f_ty_ctx[name.as_str()];
                let retty = **retty;

                let params_len = param_tys.len();
                let args_len = args.len();

                if params_len != args_len {
                    let [color_name, color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, exp.loc.start)
                        .with_message::<&str>("argument count mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, args.loc.start..args.loc.end)
                                )
                                .with_message(
                                    format!("call to function {} with {} arguments", name.as_str().fg(color_name), args_len.to_string().fg(color1))
                                )
                                .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, param_tys.loc.start..param_tys.loc.end)
                            )
                                .with_message(
                                    format!("function {} has {} parameters", name.as_str().fg(color_name), params_len.to_string().fg(color2))
                                )
                                .with_color(color2)
                        )
                        .with_note(
                            format!("function calls must provide the same number of arguments as the function expects")
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!("argument count mismatch for call to `{}`: {} args given but function expects {}", name, args_len, params_len),
                        exp.loc,
                    );
                }

                let param_tys = param_tys.iter().map(|p| p.1.clone()).collect::<Vec<_>>();

                param_tys.into_iter().zip(args.iter_mut()).for_each(|(param_t, arg)| {
                    let arg_t = self.tc_exp(arg);

                    if arg_t != *param_t {
                        let [a, b] = colors();
                        
                        self.report("argument type mismatch", arg.loc.start)
                        .with_label(
                            Label::new(
                                (&self.src_file, arg.loc.start..arg.loc.end)
                            )
                            .with_message(
                                format!("this expression has type {}", arg_t.to_string().fg(a))
                            )
                            .with_color(a)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, param_t.loc.start..param_t.loc.end)
                            )
                            .with_message(
                                format!("this parameter has type {}", param_t.elem.to_string().fg(b))
                            )
                            .with_color(b)
                        )
                        .with_note(
                            format!(
                                "the types of {} and respective {} must match in a call expression",
                                "arguments".fg(a),
                                "parameters".fg(b)
                            )
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                        self.errors.add(
                            format!("argument type mismatch for call to `{}`: expected type `{}` got type `{}`", name, param_t, arg_t),
                            arg.loc,
                        );
                    }
                });

                retty
            }
            Expr::BinOp(op, left, right) => {
                let op_type = op.get_type();
                // TODO: don't short-circuit yet, but collect *both* errors and then break out
                let left_t = self.tc_exp(left);
                let right_t = self.tc_exp(right);

                if op_type.0 .0 != left_t {
                    let [color_op, color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, left.loc.start)
                        .with_message::<&str>("operator type mismatch")
                        .with_label(
                        Label::new(
                                (&self.src_file, left.loc.range())
                            )
                            .with_message(
                                format!("first operand of {} is of type {}", op.to_string().fg(color_op), left_t.to_string().fg(color1))
                            )
                            .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, op.loc.range())
                            )
                            .with_message(
                                format!("operator {} expects {} and {}", op.to_string().fg(color_op), op_type.0.0.to_string().fg(color2), op_type.0.1.to_string().fg(color2))
                            )
                            .with_color(color_op)
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!(
                            "first argument of `{}` is type `{}`, but must be type `{}`",
                            op, left_t, op_type.0 .0
                        ),
                        left.loc,
                    );
                }
                if op_type.0 .1 != right_t {
                    let [color_op, color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, right.loc.start)
                        .with_message::<&str>("operator type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, right.loc.range())
                            )
                                .with_message(
                                    format!("second operand of {} is of type {}", op.to_string().fg(color_op), right_t.to_string().fg(color1))
                                )
                                .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, op.loc.range())
                            )
                                .with_message(
                                    format!("operator {} expects {} and {}", op.to_string().fg(color_op), op_type.0.0.to_string().fg(color2), op_type.0.1.to_string().fg(color2))
                                )
                                .with_color(color_op)
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!(
                            "second argument of `{}` is type `{}`, but must be type `{}`",
                            op, right_t, op_type.0 .1
                        ),
                        right.loc,
                    );
                }

                op_type.1
            }
            Expr::UnOp(op, inner) => {
                let op_type = op.get_type();
                let inner_t = self.tc_exp(inner);

                if op_type.0 != inner_t {
                    let [color_op, color1, color2] = colors();

                    Report::build(ariadne::ReportKind::Error, &self.src_file, inner.loc.start)
                        .with_message::<&str>("operator type mismatch")
                        .with_label(
                            Label::new(
                                (&self.src_file, inner.loc.range())
                            )
                            .with_message(
                                format!("operand of {} is of type {}", op.to_string().fg(color_op), inner_t.to_string().fg(color1))
                            )
                            .with_color(color1)
                        )
                        .with_label(
                            Label::new(
                                (&self.src_file, op.loc.range())
                            )
                            .with_message(
                                format!("operator {} expects {}", op.to_string().fg(color_op), op_type.0.to_string().fg(color2))
                            )
                            .with_color(color_op)
                        )
                        .finish()
                        .print((&self.src_file, Source::from(self.src_content.clone())))
                        .unwrap();

                    self.errors.add(
                        format!(
                            "argument of `{}` is type {}, but must be type {}",
                            op, inner_t, op_type.0
                        ),
                        inner.loc,
                    );
                }

                op_type.1
            }
        }
    }
}

// Helper to generate a bunch of colors
fn colors<const N: usize>() -> [Color; N] {
    let mut color_gen = ColorGenerator::new();

    let res = [0usize; N];
    res.map(|_| color_gen.next())
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
