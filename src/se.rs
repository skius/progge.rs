use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::ops::{Deref, DerefMut, Neg};
use std::path::Path;
use z3::ast::Ast;
use z3::{Context};
use crate::ast::*;
use crate::ir::IntraProcCFG;

// Invariant (perhaps): Only variables in a symbolic store are the symbolic variables, e.g. obtained
// as arguments or from black-box function calls. The other variables should be stored as expression
// of the symbolic variables.
#[derive(Clone, Debug)]
pub struct SymbolicStore(pub HashMap<String, Expr>);

// pub struct PathConstraint(pub Expr);
type PathConstraint = Expr;

impl SymbolicStore {
    fn symbolize(&self, symex: &mut SymbolicExecutor, exp: &Expr, pct: &PathConstraint) -> Vec<(Expr, PathConstraint)> {
        match exp {
            Expr::Var(v) => vec![(self.0.get(&v.elem.0).unwrap().clone(), pct.clone())],
            Expr::Call(name, args) => {
                // If we've reached recursion limit, assume `false` and underapproximate.
                // This is equivalent to returning to paths to continue from.

                // println!("Reached call with {}, loc: {:?}, pct: {}", name, name.loc, pct);
                // println!("{:?}", symex.function_invocations);

                if *symex.function_invocations.entry((name.loc, name.to_string())).or_insert(0) >= RECURSION_LIMIT {
                    return vec![];
                }
                *symex.function_invocations.get_mut(&(name.loc, name.to_string())).unwrap() += 1;

                // vector of (args and path contraint)
                let symbolized_args: Vec<(Vec<Expr>, PathConstraint)> = args.iter().fold(vec![(vec![], pct.clone())], |mut acc, arg| {
                    // transform each path in acc into N paths that have the current argument added
                    acc.into_iter().flat_map(|(args, pct)| {
                        self.symbolize(symex, arg, &pct).into_iter().map(|(arg_val, pct)| {
                            let mut args = args.clone();
                            args.push(arg_val);
                            (args, pct)
                        }).collect::<Vec<_>>()
                    }).collect()
                });

                symbolized_args.into_iter().flat_map(|(args, pct)| {
                    symex.run_func(&symex.prog.find_funcdef(name.as_str()).unwrap().clone(), args, &pct).into_iter().map(|(pct, ret_val)| {
                        (ret_val.unwrap(), pct)
                    })
                }).collect()
            }
            Expr::BinOp(op, left, right) => {
                self.symbolize(symex, left, pct).into_iter().flat_map(|(l, pl)| {
                    self.symbolize(symex, right, &pl).into_iter().map(|(r, pr)| {
                        (
                            Expr::BinOp(
                                op.clone(),
                                Box::new(WL::new(l.clone(), left.loc)),
                                Box::new(WL::new(r, right.loc)),
                            ),
                            pr
                        )
                    }).collect::<Vec<_>>().into_iter()
                }).collect()
                // Expr::BinOp(
                //     op.clone(),
                //     Box::new(WL::new(self.symbolize(left), left.loc)),
                //     Box::new(WL::new(self.symbolize(right), right.loc))
                // )
            }
            Expr::UnOp(op, inner) => {
                self.symbolize(symex, inner, pct).into_iter().map(|(sym_exp, pct)| {
                    (
                        Expr::UnOp(
                            op.clone(),
                            Box::new(WL::new(sym_exp, inner.loc)),
                        ),
                        pct
                    )
                }).collect()
            }
            // Expr::Array(_) => {}
            // Expr::DefaultArray { .. } => {}
            // Expr::Index(_, _) => {}
            exp => vec![(exp.clone(), pct.clone())],
        }
    }

    fn assign(&self, symex: &mut SymbolicExecutor, var: &str, exp: &Expr, pct: &PathConstraint) -> Vec<(SymbolicStore, PathConstraint)> {
        self.symbolize(symex, exp, pct).into_iter().map(|(val, pct)| {
            let mut new_store = self.clone();
            new_store.0.insert(var.to_string(), val);
            (new_store, pct)
        }).collect()
    }
}

impl Deref for SymbolicStore {
    type Target = HashMap<String, Expr>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SymbolicStore {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for SymbolicStore {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in self.0.iter() {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{} = {}", k, v)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

pub fn run_intra_symbolic_execution(prog: Program) -> SymbolicExecutor {
    let mut store = SymbolicStore(HashMap::new());
    let mut pct = Expr::BoolLit(true);

    let func_start = prog.find_funcdef("analyze").unwrap().clone();

    for (a, _) in func_start.params.iter() {
        store.insert(a.elem.0.clone(), Expr::Var(a.clone()));
    }

    let mut symex = SymbolicExecutor {
        unreachable_paths: HashMap::new(),
        testcases: HashMap::new(),
        prog,
        function_invocations: HashMap::new(),
    };

    // println!("Starting symbolic execution with state ({}, {}) ", &store, &pct);
    let paths = symex.run_block(&func_start.body, &store, &pct, &None);

    symex
}

pub static RECURSION_LIMIT: usize = 6;

// TODO: because of mutable self, we will probably need to clone functions very often. Wasteful.
pub struct SymbolicExecutor {
    pub unreachable_paths: HashMap<Loc, Model>,
    pub testcases: HashMap<Loc, Vec<Model>>,
    pub prog: Program,
    pub function_invocations: HashMap<(Loc, String), usize>,
}

impl SymbolicExecutor {
    // returns list of pct and return values
    fn run_func(&mut self, func: &FuncDef, args: Vec<Expr>, pct: &Expr) -> Vec<(PathConstraint, Option<Expr>)> {
        let mut new_store = SymbolicStore(HashMap::new());
        let mut new_pct = pct.clone();

        let recs_prev = self.function_invocations.clone();

        for (i, (v, _)) in func.params.iter().enumerate() {
            new_store.insert(v.elem.0.clone(), args[i].clone());
        }

        // println!("______ running func {}", func.name.as_str());
        // println!("input was: {}, sat? {:?}", pct, satisfiable(pct));
        let paths = self.run_block(&func.body, &new_store, &new_pct, &None);

        // // TODO: why is a sat input producing no outputs?
        // println!("{:?}\n", &paths);

        // Need to restore function invocations - we count "recursion-depth", not how many times we call a function in total.
        self.function_invocations = recs_prev;

        paths.into_iter().map(|(_, pct, retval)| (pct, retval)).collect()
    }

    // Returns the set of all possible exiting paths
    fn run_block(&mut self, block: &Block, store: &SymbolicStore, pct: &PathConstraint, ret_val: &Option<Expr>) -> Vec<(SymbolicStore, PathConstraint, Option<Expr>)> {
        // If in this path we have already returned, then we can just break out.
        if let Some(ret_val) = ret_val {
            // println!("already returned {}", ret_val);
            return vec![(store.clone(), pct.clone(), Some(ret_val.clone()))];
        }

        // Then check if PCT is sat.
        if satisfiable(pct).is_unsat() {
            // println!("PCT {} is not satisfiable", pct);
            return vec![];
        }


        block.0.iter().fold(
            vec![(store.clone(), pct.clone(), ret_val.clone())],
            |paths, stmt| {
                paths.iter().map(|(store, pct, retval)| {
                    if retval.is_some() {
                        // Already returned, so we short-circuit
                        // println!("already returned before execing {} : {}", stmt.clone(), retval.clone().unwrap());
                        return vec![(store.clone(), pct.clone(), retval.clone())];
                    }
                    self.run_stmt(stmt, store, pct, retval)
                }).flatten().collect()
            }
        )
    }

    fn run_stmt(&mut self, stmt: &WithLoc<Stmt>, store: &SymbolicStore, pct: &PathConstraint, ret_val: &Option<Expr>) -> Vec<(SymbolicStore, PathConstraint, Option<Expr>)> {
        match &stmt.elem {
            Stmt::IfElse { cond, if_branch, else_branch } => {
                store.symbolize(self, cond, pct).into_iter().flat_map(|(cond_symb, pct)| {
                    let cond = WL::new(cond_symb, cond.loc);
                    // send help
                    let taken_pct = Expr::BinOp(WL::no_loc(BinOpcode::And), Box::new(WL::no_loc(pct.clone())), Box::new(cond.clone()));
                    let not_taken_pct = Expr::BinOp(WL::no_loc(BinOpcode::And), Box::new(WL::no_loc(pct.clone())), Box::new(WL::no_loc(Expr::UnOp(WL::no_loc(UnOpcode::Not), Box::new(cond.clone())))));
                    let mut paths_taken = self.run_block(if_branch, store, &taken_pct, ret_val);
                    let paths_not_taken = self.run_block(else_branch, store, &not_taken_pct, ret_val);
                    paths_taken.extend(paths_not_taken);
                    paths_taken.into_iter()
                }).collect()
            }
            Stmt::Decl(v, exp) => {
                store.assign(self, &v.elem.0, exp, pct).into_iter().map(|(store, pct)| {
                    // println!("decl exp: {}, pct: {}, ret {:?}", exp, pct, ret_val);
                    // println!("satres: {:?}", satisfiable(&pct));
                    (store, pct, ret_val.clone())
                }).collect()
            }
            Stmt::Assn(le, exp) => {
                match &le.elem {
                    LocExpr::Var(v) => {
                        store.assign(self, &v.elem.0, exp, pct).into_iter().map(|(store, pct)| {
                            (store, pct, ret_val.clone())
                        }).collect()
                    }
                    LocExpr::Index(_, _) => {panic!("no")}
                }
            }
            Stmt::While { .. } => panic!("While should have been removed in loop bounding"),
            Stmt::Call(name, args) if name.as_str() == "assume!" => {
                // TODO: Will need to handle Stmt::Call in the future when arrays are supported.
                let new_pct = Expr::BinOp(
                    WL::no_loc(BinOpcode::And),
                    Box::new(WL::no_loc(pct.clone())),
                    Box::new(args[0].clone()),
                );
                return vec![(store.clone(), new_pct, ret_val.clone())];
            }
            Stmt::Testcase() => {
                let satres = satisfiable(&pct);
                if let SatResult::Sat(mut model) = satres {
                    self.testcases.entry(stmt.loc).or_insert(Vec::new()).push(model);
                }
                vec![(store.clone(), pct.clone(), ret_val.clone())]
            }
            Stmt::Unreachable() => {
                let satres = satisfiable(&pct);
                if let SatResult::Sat(model) = satres{
                    self.unreachable_paths.insert(stmt.loc, model);
                }
                vec![(store.clone(), pct.clone(), ret_val.clone())]
            }
            Stmt::Return(Some(exp)) => {
                // println!("Returning {}, store: {:?}", exp, store);
                store.symbolize(self, exp, pct).into_iter().map(|(ret_val, pct)| {
                    // println!("Returning {}", &ret_val);
                    (store.clone(), pct, Some(ret_val))
                }).collect()
            }
            Stmt::Return(None) => {
                // TODO: Hmm. Option<Expr> does not distinguish between all cases, "Not returned yet", "Returned void", "Returned expr", so we'll just use a placeholder for now.
                vec![(store.clone(), pct.clone(), Some(Expr::IntLit(-42)))]
            }
            _ => vec![(store.clone(), pct.clone(), ret_val.clone())],
        }
    }
}

pub fn string_of_model<'a>((int_map, bool_map): &Model, order: impl Iterator<Item = &'a Var>) -> String {
    let mut res = String::new();
    let mut first = true;
    res.push_str("{ ");
    for v in order {
        let (k, _) = v.rsplit_once("_").unwrap();

        let val_string = match &v.1 {
            Type::Int => int_map[v.as_str()].to_string(),
            Type::Bool => bool_map[v.as_str()] .to_string(),
            t => panic!("unexpected type {:?}", t),
        };

        if !first {
            res.push_str(", ");
        } else {
            first = false;
        }
        res.push_str(&format!("{} = {}", k, val_string));
    }
    res.push_str(" }");
    res
}

pub fn fill_model((int_map, bool_map): &mut Model, fv: &HashSet<Var>) {
    for v in fv {
        match &v.1 {
            Type::Int => {
                if int_map.contains_key(v.as_str()) {
                    continue;
                }
                int_map.insert(v.to_string(), 0);
            }
            Type::Bool => {
                if bool_map.contains_key(v.as_str()) {
                    continue;
                }
                bool_map.insert(v.to_string(), false);
            }
            t => panic!("unexpected type {:?}", t),
        }
    }
}

// pub enum Value {
//     Int(i64),
//     Bool(bool),
// }

pub type Model = (HashMap<String, i64>, HashMap<String, bool>);

#[derive(Debug)]
pub enum SatResult {
    Unsat,
    Unknown(String),
    Sat(Model),
}

impl SatResult {
    pub fn is_sat(&self) -> bool {
        match self {
            SatResult::Sat(_) => true,
            _ => false,
        }
    }

    pub fn is_unsat(&self) -> bool {
        match self {
            SatResult::Unsat => true,
            _ => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            SatResult::Unknown(_) => true,
            _ => false,
        }
    }
}

pub fn satisfiable(pct: &Expr) -> SatResult {
    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(1000);

    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    solver.assert(&expr_to_z3_bool(&ctx, pct));

    let res = solver.check();

    match res {
        z3::SatResult::Sat => {
            let model = map_of_model(&ctx, solver.get_model().unwrap(), &pct.free_vars());
            SatResult::Sat(model)
        },
        z3::SatResult::Unsat => SatResult::Unsat,
        z3::SatResult::Unknown => SatResult::Unknown(solver.get_reason_unknown().unwrap()),
    }
}

fn map_of_model(ctx: &z3::Context, model: z3::Model, fv: &HashSet<Var>) -> (HashMap<String, i64>, HashMap<String, bool>) {
    let mut int_map = HashMap::new();
    let mut bool_map = HashMap::new();

    for v in fv {
        match &v.1 {
            Type::Int => {
                let val = model.eval(&z3::ast::Int::new_const(ctx, v.as_str()), false).unwrap().as_i64();
                if let Some(val) = val {
                    int_map.insert(v.as_str().to_string(), val);
                }
            }
            Type::Bool => {
                let val = model.eval(&z3::ast::Bool::new_const(ctx, v.as_str()), false).unwrap().as_bool();
                if let Some(val) = val {
                    bool_map.insert(v.to_string(), val);
                }
            }
            t => panic!("Unexpected type: {:?}", t),
        }
    }

    (int_map, bool_map)
}

fn expr_to_z3_bool<'a>(ctx: &'a Context, exp: &Expr) -> z3::ast::Bool<'a> {
    match exp {
        Expr::BoolLit(b) => {
            z3::ast::Bool::from_bool(ctx, *b)
        }
        Expr::Var(v) => {
            z3::ast::Bool::new_const(ctx, v.as_str())
        }
        Expr::BinOp(op, left, right)
            if op.elem.get_type() == OpcodeType((Type::Int, Type::Int), Type::Bool)
        => {
            let left = expr_to_z3_int(ctx, left);
            let right = expr_to_z3_int(ctx, right);

            let constr = match &op.elem {
                BinOpcode::Lt => z3::ast::Int::lt,
                BinOpcode::Le => z3::ast::Int::le,
                BinOpcode::Gt => z3::ast::Int::gt,
                BinOpcode::Ge => z3::ast::Int::ge,
                BinOpcode::Eq => z3::ast::Int::_eq,
                BinOpcode::Ne => return left._eq(&right).not(),
                op => panic!("unsupported binop: {:?}", op),
            };

            constr(&left, &right)
        }
        Expr::BinOp(op, left, right)
            if op.elem.get_type() == OpcodeType((Type::Bool, Type::Bool), Type::Bool)
        => {
            let constr = match &op.elem {
                BinOpcode::And => z3::ast::Bool::and,
                BinOpcode::Or => z3::ast::Bool::or,
                op => panic!("unsupported binop: {:?}", op),
            };
            let left = expr_to_z3_bool(ctx, left);
            let right = expr_to_z3_bool(ctx, right);
            constr(ctx, &[&left, &right])
        }
        Expr::UnOp(op, inner) => {
            match &op.elem {
                UnOpcode::Not => expr_to_z3_bool(ctx, inner).not(),
                op => panic!("unsupported unop: {:?}", op),
            }
        }
        exp => panic!("unsupported bool expr: {:?}", exp),
    }
}

fn expr_to_z3_int<'a>(ctx: &'a Context, exp: &Expr) -> z3::ast::Int<'a> {
    match exp {
        Expr::IntLit(i) => z3::ast::Int::from_i64(ctx, *i),
        Expr::Var(v) => z3::ast::Int::new_const(ctx, v.as_str()),
        Expr::BinOp(op, left, right) => {
            // At the moment this can only be int*int->int
            let left = expr_to_z3_int(ctx, left);
            let right = expr_to_z3_int(ctx, right);
            match &op.elem {
                BinOpcode::Add => {
                    z3::ast::Int::add(ctx, &[&left, &right])
                },
                BinOpcode::Sub => {
                    z3::ast::Int::sub(ctx, &[&left, &right])
                },
                BinOpcode::Mul => {
                    z3::ast::Int::mul(ctx, &[&left, &right])
                },
                BinOpcode::Div => {
                    left.div(&right)
                },
                BinOpcode::Mod => {
                    left.modulo(&right)
                },
                op => panic!("unsupported binop: {:?}", op),
            }
        }
        Expr::UnOp(op, inner) => {
            match &op.elem {
                UnOpcode::Neg => expr_to_z3_int(ctx, inner).neg(),
                op => panic!("unsupported unop: {:?}", op),
            }
        }
        exp => panic!("unsupported int expr: {:?}", exp),
    }
}

// loop bounding

pub static UNROLL_FACTOR: usize = 5;

type WL<T> = WithLoc<T>;

/// This function takes a program, and returns a copy of the Program with bounded loops,
/// by unrolling them by a factor of [`UNROLL_FACTOR`]. Also returns whether any loop bounding was actually done or not.
pub fn bound_loops(prog: &Program) -> (Program, bool) {
    /*
    Perhaps a slight issue: Currently, there are let-bindings in a loop's body, these will not be renamed,
    since we don't TC afterwards. This does not seem to be an issue however, as we are just overwriting
    variable's symbolic states that are not relevant anymore.

    e.g.
    while true {
        let i = n;
        i = i + 1;
    }

    I think it should be fine.
    */

    let mut did_bound = false;
    let mut new_prog = Program(Vec::new());
    for func in prog.0.iter() {
        new_prog.0.push(WithLoc::new(bound_loops_fn(&*func, &mut did_bound), func.loc));
    }

    (new_prog, did_bound)
}

pub fn bound_loops_fn(func: &FuncDef, did_bound: &mut bool) -> FuncDef {
    let mut new_func = FuncDef {
        name: func.name.clone(),
        params: func.params.clone(),
        retty: func.retty.clone(),
        body: WL::new(bound_loops_block(&*func.body, did_bound), func.body.loc),
    };
    new_func
}

pub fn bound_loops_block(block: &Block, did_bound: &mut bool) -> Block {
    let mut new_block = Block(Vec::new());
    for stmt in block.0.iter() {
        new_block.0.push(WL::new(bound_loops_stmt(&*stmt, did_bound), stmt.loc));
    }
    new_block
}

pub fn bound_loops_stmt(stmt: &Stmt, did_bound: &mut bool) -> Stmt {
    match stmt {
        Stmt::IfElse { cond, if_branch, else_branch } => {
            Stmt::IfElse {
                cond: cond.clone(),
                if_branch: WithLoc::new(bound_loops_block(&*if_branch, did_bound), if_branch.loc),
                else_branch: WithLoc::new(bound_loops_block(&*else_branch, did_bound), else_branch.loc),
            }
        }
        Stmt::While { cond, block } => {
            *did_bound = true;
            let empty_else = WL::no_loc(Block(Vec::new()));

            // We need to underapproximate, e.g. if the condition is still true after unrolling, assume
            // that's impossible instead of working with an inconsistent state

            // {
            //     assume!(false)
            // }
            let base_case_block = Block(vec![
               WL::no_loc(Stmt::Call(
                   WL::no_loc("assume!".to_string()),
                   WL::no_loc(vec![
                       WL::no_loc(Expr::BoolLit(false)),
                   ])
               )),
            ]);

            let unrolled_block = WL::new(bound_loops_block(&*block, did_bound), block.loc);

            let base_case_if = Stmt::IfElse {
                cond: cond.clone(),
                if_branch: WL::no_loc(base_case_block),
                else_branch: empty_else.clone()
            };

            // Unroll UNROLL_FACTOR times
            let res = (0..UNROLL_FACTOR).into_iter().fold(
                base_case_if,
                |acc, _| {
                    let mut new_if_branch = unrolled_block.clone();
                    new_if_branch.0.push(WithLoc::new(acc.clone(), block.loc));

                    Stmt::IfElse {
                        cond: cond.clone(),
                        if_branch: new_if_branch,
                        else_branch: empty_else.clone(),
                    }
                }
            );
            res
        }
        _ => stmt.clone(),
    }
}