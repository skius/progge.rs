use std::borrow::{Borrow, BorrowMut};
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::ops::{Deref, DerefMut, Neg};
use std::cell::RefCell;
use std::hash::Hash;
use std::sync::{Arc, Mutex};
use std::time::SystemTime;
use z3::ast::Ast;
use z3::{Context};
use rayon::prelude::*;
use crate::ast::*;
use crate::ir::IntraProcCFG;
use crate::opt::{get_bests, sexp_of_expr};


#[derive(Debug, Clone)]
pub enum SymbolicValue {
    Expr(Expr),
    HeapPtr(usize),
}

impl SymbolicValue {
    pub fn is_expr(&self) -> bool {
        match self {
            SymbolicValue::Expr(_) => true,
            _ => false,
        }
    }

    pub fn is_heap_ptr(&self) -> bool {
        match self {
            SymbolicValue::HeapPtr(_) => true,
            _ => false,
        }
    }

    pub fn into_expr(self) -> Option<Expr> {
        match self {
            SymbolicValue::Expr(e) => Some(e),
            _ => None,
        }
    }

    pub fn into_heap_ptr(self) -> Option<usize> {
        match self {
            SymbolicValue::HeapPtr(i) => Some(i),
            _ => None,
        }
    }
}

impl Display for SymbolicValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SymbolicValue::Expr(e) => write!(f, "{}", e),
            SymbolicValue::HeapPtr(ptr) => write!(f, "{}", ptr),
        }
    }
}

#[derive(Clone, Debug)]
pub enum SymbolicArray {
    ExplicitArray(Vec<SymbolicValue>),
    DefaultArray {
        length: Expr,
        default: SymbolicValue,
        values: HashMap<Expr, SymbolicValue>,
    }
}

impl SymbolicArray {
    fn insert(&mut self, idx: &Expr, new_val: SymbolicValue) {
        match self {
            SymbolicArray::ExplicitArray(arr) => {
                if let Expr::IntLit(idx) = idx {
                    arr[*idx as usize] = new_val;
                } else {
                    panic!("ExplicitArray must always be indexed with IntLit")
                }
            }
            SymbolicArray::DefaultArray { length, default, values } => {
                values.insert(idx.clone(), new_val);
            }
        }
    }

    fn get(&self, idx: &Expr) -> &SymbolicValue {
        match self {
            SymbolicArray::ExplicitArray(els) => {
                if let Expr::IntLit(idx) = idx {
                    els.get(*idx as usize).unwrap()
                } else {
                    panic!("ExplicitArray must always be indexed with IntLit")
                }
            }
            SymbolicArray::DefaultArray { values, default, .. } => {
                values.get(idx).unwrap_or(default)
            }
        }
    }
}

impl Display for SymbolicArray {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SymbolicArray::ExplicitArray(els) => {
                write!(f, "[")?;
                for (i, el) in els.iter().enumerate() {
                    write!(f, "{}", el)?;
                    if i < els.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            SymbolicArray::DefaultArray { default, length, values } => {
                write!(f, "[{}; {}]", default, length);
                write!(f, "{{")?;
                let mut first = true;
                for (k, v) in values.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} -> {}", k, v)?;
                }
                write!(f, "}}")
            }
        }
    }
}

// SymbolicHeap is array_uid -> sym_array
#[derive(Clone, Debug)]
pub struct SymbolicHeap(pub HashMap<usize, SymbolicArray>);

impl SymbolicHeap {
    pub fn new_ptr(&self) -> usize {
        self.0.len()
    }
}

impl Display for SymbolicHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, sym_arr) in self.0.iter() {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", k, sym_arr)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Deref for SymbolicHeap {
    type Target = HashMap<usize, SymbolicArray>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SymbolicHeap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// Invariant (perhaps): Only variables in a symbolic store are the symbolic variables, e.g. obtained
// as arguments or from black-box function calls. The other variables should be stored as expression
// of the symbolic variables.
#[derive(Clone, Debug)]
pub struct SymbolicStore(pub HashMap<String, SymbolicValue>);

// pub struct PathConstraint(pub Expr);
type PathConstraint = Expr;

impl SymbolicStore {
    fn symbolize(&self, symex: &Arc<SymbolicExecutor>, exp: &Expr, pct: &PathConstraint, sym_heap: &SymbolicHeap) -> Vec<(SymbolicValue, PathConstraint, SymbolicHeap)> {
        match exp {
            Expr::Var(v) => vec![(self.0.get(&v.elem.0).unwrap().clone(), pct.clone(), sym_heap.clone())],
            Expr::Call(name, args) => {
                // Handle builtins
                if name.as_str() == "int_arg" {
                    // Treat it as a new symbolic variable
                    // Must be one argument
                    let arg = &args[0];
                    return self.symbolize(symex, arg, pct, sym_heap).into_par_iter().map(|(arg, pct, sym_heap)| {
                        let args = WL::no_loc(vec![WL::no_loc(arg.into_expr().unwrap())]);
                        (SymbolicValue::Expr(Expr::Call(name.clone(), args)), pct.clone(), sym_heap.clone())
                    }).collect();
                }
                if name.as_str() == "print_int" {
                    // print_int just passes the single argument through
                    return self.symbolize(symex, &args[0], pct, sym_heap);
                }



                symex.run_call(name.as_str(), args, self, pct, sym_heap, |pct, sym_heap, ret_val| {
                    (ret_val.unwrap(), pct, sym_heap)
                })
            }
            Expr::BinOp(op, left, right) => {
                self.symbolize(symex, left, pct, sym_heap).into_par_iter().flat_map(|(l, pl, sym_heapl)| {
                    self.symbolize(symex, right, &pl, &sym_heapl).into_par_iter().map(|(r, pr, sym_heapr)| {
                        (
                            SymbolicValue::Expr(Expr::BinOp(
                                op.clone(),
                                Box::new(WL::new(l.clone().into_expr().unwrap(), left.loc)),
                                Box::new(WL::new(r.into_expr().unwrap(), right.loc)),
                            )),
                            pr,
                            sym_heapr,
                        )
                    }).collect::<Vec<_>>()
                }).collect()
                // Expr::BinOp(
                //     op.clone(),
                //     Box::new(WL::new(self.symbolize(left), left.loc)),
                //     Box::new(WL::new(self.symbolize(right), right.loc))
                // )
            }
            Expr::UnOp(op, inner) => {
                self.symbolize(symex, inner, pct, sym_heap).into_par_iter().map(|(sym_exp, pct, sym_heap)| {
                    (
                        SymbolicValue::Expr(Expr::UnOp(
                            op.clone(),
                            Box::new(WL::new(sym_exp.into_expr().unwrap(), inner.loc)),
                        )),
                        pct,
                        sym_heap,
                    )
                }).collect()
            }
            Expr::Array(exps) => {
                /*
                Arrays point into the SymbolicHeap. SymbolicHeap: usize -> (Expr -> SymbolicValue), i.e.
                a map from some pointer (an ID) to an array represented as a mapping from indices to symbolic values.
                These mappings need to be sanitized in the sense that all path constraints must make sure that
                the indices are disjoint, i.e. if an array is (Var(n) -> Int(0), Var(m) -> Int(1)) then n!=m must be in the PCT.

                */

                let arr_len = exps.len();

                let folded = exps.iter().fold(
                    vec![(vec![], (pct.clone(), sym_heap.clone()))],
                    |acc, exp| {
                        acc.into_par_iter().flat_map(|(sym_args, (pct, sym_heap))| {
                            self.symbolize(symex, exp, &pct, &sym_heap).into_par_iter().map(|(sym_exp, pct, sym_heap)| {
                                let mut sym_args = sym_args.clone();
                                sym_args.push(sym_exp);

                                (sym_args, (pct, sym_heap))
                            }).collect::<Vec<_>>()
                        }).collect()
                    }
                );

                folded.into_par_iter().map(|(sym_args, (pct, mut sym_heap))| {
                    debug_assert!(sym_args.len() == arr_len);

                    let ptr = sym_heap.new_ptr();

                    sym_heap.insert(ptr, SymbolicArray::ExplicitArray(sym_args));

                    // for (i, sym_arg) in sym_args.into_iter().enumerate() {
                    //     sym_heap.entry(ptr).or_insert(HashMap::new()).insert(Expr::IntLit(i as i64), sym_arg);
                    // }

                    (SymbolicValue::HeapPtr(ptr), pct, sym_heap)
                }).collect()
            }
            // TODO: Default array. needs a different representation in SymbolicHeap I assume.
            Expr::DefaultArray { default_value, size } => {
                self.symbolize(symex, default_value, pct, sym_heap).into_par_iter().flat_map(|(sym_default, pct, sym_heap)| {
                    self.symbolize(symex, size, &pct, &sym_heap).into_par_iter().map(|(sym_size, pct, mut sym_heap)| {
                        let ptr = sym_heap.new_ptr();
                        // Must be Expr, typechecking would've caught this otherwise.
                        let sym_size = sym_size.into_expr().unwrap();

                        sym_heap.insert(ptr, SymbolicArray::DefaultArray {
                            default: sym_default.clone(),
                            length: sym_size,
                            values: HashMap::new(),
                        });

                        (SymbolicValue::HeapPtr(ptr), pct, sym_heap)
                    }).collect::<Vec<_>>()
                }).collect()
            }
            Expr::Index(arr, idx) => {
                symex.run_index(
                    arr,
                    idx,
                    self,
                    pct,
                    sym_heap,
                    |symex, sym_heap, pct| {
                        vec![(sym_heap, pct, ())]
                    },
                    |symex, sym_arr, sym_idx, pct, sym_heap, _| {
                        vec![(sym_heap[&sym_arr].get(&sym_idx).clone(), pct.clone(), sym_heap.clone())]
                    },
                )
            }
            exp => vec![(SymbolicValue::Expr(exp.clone()), pct.clone(), sym_heap.clone())],
        }
    }

    fn assign(&self, symex: &Arc<SymbolicExecutor>, var: &str, exp: &Expr, pct: &PathConstraint, sym_heap: &SymbolicHeap) -> Vec<(SymbolicStore, PathConstraint, SymbolicHeap)> {
        self.symbolize(symex, exp, pct, sym_heap).into_par_iter().map(|(val, pct, sym_heap)| {
            let mut new_store = self.clone();
            new_store.0.insert(var.to_string(), val);
            (new_store, pct, sym_heap)
        }).collect()
    }
}

impl Deref for SymbolicStore {
    type Target = HashMap<String, SymbolicValue>;

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

pub fn run_symbolic_execution(prog: Program) -> Arc<SymbolicExecutor> {
    let mut store = SymbolicStore(HashMap::new());
    let mut pct = Expr::BoolLit(true);

    let func_start = prog.find_funcdef("analyze").unwrap().clone();

    for (a, _) in func_start.params.iter() {
        store.insert(a.elem.0.clone(), SymbolicValue::Expr(Expr::Var(a.clone())));
    }

    let mut symex = Arc::new(SymbolicExecutor {
        unreachable_paths: Mutex::new(HashMap::new()),
        testcases: Mutex::new(HashMap::new()),
        prog,
        function_invocations: Mutex::new(HashMap::new()),
    });

    let sym_heap = SymbolicHeap(HashMap::new());

    // println!("Starting symbolic execution with state ({}, {}) ", &store, &pct);
    let paths = symex.run_block(&func_start.body, &store, &pct, &sym_heap, &None);

    // for (sym_store, pct, sym_heap, ret_val) in paths {
    //     if !satisfiable(&pct).is_sat() {
    //         continue;
    //     }
    //
    //     println!("\nResulting path:");
    //     println!("store: {}", sym_store);
    //     println!("pct: {}", pct);
    //     println!("heap: {}", sym_heap);
    //     println!("ret: {:?}", ret_val);
    // }
    // println!();

    cache::CACHE.with(|c| {
        // println!("Cache contained: {:?}", c.borrow().keys().collect::<Vec<_>>());
        println!("Cache contained {:?} entries", c.borrow().keys().len());
    });

    Z3_CACHE_HITS.with(|c| {
        println!("Cache hits: {}", c.borrow());
    });

    Z3_TIME.with(|t| {
       println!("Took Z3: {}ms, {}s", *t.borrow(), (*t.borrow())/1000);
    });
    Z3_INVOCATIONS.with(|t| {
        println!("Called Z3 {} times", *t.borrow());
    });


    symex
}

pub static RECURSION_LIMIT: usize = 5;

// TODO: because of mutable self, we will probably need to clone functions very often. Wasteful.
pub struct SymbolicExecutor {
    pub unreachable_paths: Mutex<HashMap<Loc, Model>>,
    pub testcases: Mutex<HashMap<Loc, Vec<Model>>>,
    pub prog: Program,
    pub function_invocations: Mutex<HashMap<(Loc, String), usize>>,
}

impl SymbolicExecutor {
    // returns list of pct and return values
    fn run_func(self: &Arc<Self>, func: &FuncDef, args: Vec<SymbolicValue>, pct: &Expr, sym_heap: &SymbolicHeap) -> Vec<(PathConstraint, SymbolicHeap, Option<SymbolicValue>)> {
        // if satisfiable(pct).is_unsat() {
        //     // println!("PCT {} is not satisfiable", pct);
        //     return vec![];
        // }

        let mut new_store = SymbolicStore(HashMap::new());

        let recs_prev = self.function_invocations.lock().unwrap().clone();

        // The reason we modify here, is because only for the current function scope do we want to increase
        // the recursion depth. if we do it outside, then we're changing the depth ("the no. of times we called the function")
        // for all paths.
        // TODO: improve Loc stuff here
        if *self.function_invocations.lock().unwrap().entry((WL::no_loc(()).loc, func.name.to_string())).or_insert(0) >= RECURSION_LIMIT {
            return vec![];
        }
        *self.function_invocations.lock().unwrap().get_mut(&(WL::no_loc(()).loc, func.name.to_string())).unwrap() += 1;

        for (i, (v, _)) in func.params.iter().enumerate() {
            new_store.insert(v.elem.0.clone(), args[i].clone());
        }

        // println!("______ running func {}", func.name.as_str());
        // println!("pct {}", pct);
        // println!("invocs {:?}", self.function_invocations);
        // println!("input was: {}, sat? {:?}", pct, satisfiable(pct));
        let paths = self.run_block(&func.body, &new_store, &pct, sym_heap, &None);

        // println!("{}\n", &paths.len());

        // Need to restore function invocations - we count "recursion-depth", not how many times we call a function in total.
        *self.function_invocations.lock().unwrap() = recs_prev;

        paths.into_iter().map(|(_, pct, sym_heap, retval)| (pct, sym_heap, retval)).collect()
    }

    // Returns the set of all possible exiting paths
    fn run_block(self: &Arc<Self>, block: &Block, store: &SymbolicStore, pct: &PathConstraint, sym_heap: &SymbolicHeap, ret_val: &Option<SymbolicValue>) -> Vec<(SymbolicStore, PathConstraint, SymbolicHeap, Option<SymbolicValue>)> {
        // If in this path we have already returned, then we can just break out.
        if let Some(ret_val) = ret_val {
            // println!("already returned {}", ret_val);
            return vec![(store.clone(), pct.clone(), sym_heap.clone(), Some(ret_val.clone()))];
        }

        // Then check if PCT is sat.
        // very inefficient to invoke Z3 for every block
        // update- no, not really, in fact it's essentially to necessary in the context of loop unrolling and dynamically sized arrays
        if satisfiable(pct).is_unsat() {
            // println!("PCT {} is not satisfiable", pct);
            return vec![];
        }


        block.0.iter().fold(
            vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())],
            |paths, stmt| {
                paths.into_par_iter().map(|(store, pct, sym_heap, ret_val)| {
                    if ret_val.is_some() {
                        // Already returned, so we short-circuit
                        // println!("already returned before execing {} : {}", stmt.clone(), retval.clone().unwrap());
                        return vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())];
                    }
                    self.run_stmt(stmt, &store, &pct, &sym_heap, &ret_val)
                }).flatten().collect::<Vec<_>>()
                // }).collect::<Vec<_>>()
            }
        )
    }

    fn run_stmt(self: &Arc<Self>, stmt: &WithLoc<Stmt>, store: &SymbolicStore, pct: &PathConstraint, sym_heap: &SymbolicHeap, ret_val: &Option<SymbolicValue>) -> Vec<(SymbolicStore, PathConstraint, SymbolicHeap, Option<SymbolicValue>)> {
        match &stmt.elem {
            Stmt::IfElse { cond, if_branch, else_branch } => {
                store.symbolize(self, cond, pct, sym_heap).into_iter().flat_map(|(cond_symb, pct, sym_heap)| {
                    let cond = WL::new(cond_symb.into_expr().unwrap(), cond.loc);
                    // send help
                    let taken_pct = Expr::BinOp(WL::no_loc(BinOpcode::And), Box::new(WL::no_loc(pct.clone())), Box::new(cond.clone()));
                    let not_taken_pct = Expr::BinOp(WL::no_loc(BinOpcode::And), Box::new(WL::no_loc(pct.clone())), Box::new(WL::no_loc(Expr::UnOp(WL::no_loc(UnOpcode::Not), Box::new(cond.clone())))));
                    let mut paths_taken = self.run_block(if_branch, store, &taken_pct, &sym_heap, ret_val);
                    let paths_not_taken = self.run_block(else_branch, store, &not_taken_pct, &sym_heap, ret_val);
                    paths_taken.extend(paths_not_taken);
                    paths_taken.into_iter()
                }).collect()
            }
            Stmt::Decl(v, exp) => {
                store.assign(self, &v.elem.0, exp, pct, sym_heap).into_iter().map(|(store, pct, sym_heap)| {
                    // println!("decl exp: {}, pct: {}, ret {:?}", exp, pct, ret_val);
                    // println!("satres: {:?}", satisfiable(&pct));
                    (store, pct, sym_heap, ret_val.clone())
                }).collect()
            }
            Stmt::Assn(le, exp) => {
                match &le.elem {
                    LocExpr::Var(v) => {
                        store.assign(self, &v.elem.0, exp, pct, sym_heap).into_iter().map(|(store, pct, sym_heap)| {
                            (store, pct, sym_heap, ret_val.clone())
                        }).collect()
                    }
                    LocExpr::Index(arr, idx) => {
                        self.run_index(
                            arr,
                            idx,
                            store,
                            pct,
                            sym_heap,
                            |symex, pct, sym_heap| {
                                store.symbolize(symex, exp, &pct, &sym_heap).into_iter().map(|(sym_exp, pct, sym_heap)| {
                                    (pct, sym_heap, sym_exp)
                                }).collect()
                            },
                            |symex, sym_arr, sym_idx, pct, sym_heap, sym_exp| {
                                let mut new_sym_heap = sym_heap.clone();
                                new_sym_heap.get_mut(&sym_arr).unwrap().insert(sym_idx, sym_exp.clone());
                                vec![(store.clone(), pct.clone(), new_sym_heap, ret_val.clone())]
                            },
                        )
                    }
                }
            }
            Stmt::While { .. } => panic!("While should have been removed in loop bounding"),
            Stmt::Call(name, args) if name.as_str() == "assume!" => {
                // assume! has one arg
                store.symbolize(self, &args[0], pct, sym_heap).into_par_iter().filter_map(|(sym_arg, pct, sym_heap)| {
                    let assmpt = sym_arg.into_expr().unwrap();
                    if satisfiable(&assmpt).is_unsat() {
                        return None;
                    }
                    let new_pct = Expr::BinOp(
                        WL::no_loc(BinOpcode::And),
                        Box::new(WL::no_loc(pct)),
                        Box::new(WL::no_loc(assmpt)),
                    );
                    Some((store.clone(), new_pct, sym_heap, ret_val.clone()))
                }).collect()
            }
            Stmt::Call(name, args) => {
                // Built-ins' only side-effects are that they might change the symbolic heap.
                if name.as_str() == "analyze!" {
                    return args.iter().fold(
                        vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())],
                        |acc, arg| {
                            acc.into_par_iter().flat_map(|(store, pct, sym_heap, ret_val)| {
                                store.symbolize(self, arg, &pct, &sym_heap).into_iter().map(|(sym_arg, pct, sym_heap)| {
                                    (store.clone(), pct, sym_heap, ret_val.clone())
                                }).collect::<Vec<_>>()
                            }).collect()
                        },
                    );
                }


                self.run_call(name.as_str(), args, store, pct, sym_heap, |pct, sym_heap, _ret_val| {
                    (store.clone(), pct, sym_heap, ret_val.clone())
                })
            }
            Stmt::Testcase() => {
                // println!("\ntestcase line{}, \npct: {}\nsym_heap: {}", stmt.loc.line, &pct, &sym_heap);

                let satres = satisfiable(&pct);
                if let SatResult::Sat(mut model) = satres {
                    // println!("sat: {:?}, {:?}", &model.0, &model.1);
                    self.testcases.lock().unwrap().entry(stmt.loc).or_insert(Vec::new()).push(model);
                }
                vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())]
            }
            Stmt::Unreachable() => {
                if !self.unreachable_paths.lock().unwrap().contains_key(&stmt.loc) {
                    // If we already have a model for an unreachable! we don't need to compute again
                    let satres = satisfiable(&pct);
                    if let SatResult::Sat(model) = satres{
                        self.unreachable_paths.lock().unwrap().insert(stmt.loc, model);
                    }
                }

                vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())]
            }
            Stmt::Return(Some(exp)) => {
                // println!("Returning {}, store: {:?}", exp, store);
                store.symbolize(self, exp, pct, sym_heap).into_iter().map(|(ret_val, pct, sym_heap)| {
                    // println!("Returning {}", &ret_val);
                    (store.clone(), pct, sym_heap, Some(ret_val))
                }).collect()
            }
            Stmt::Return(None) => {
                // TODO: Hmm. Option<Expr> does not distinguish between all cases, "Not returned yet", "Returned void", "Returned expr", so we'll just use a placeholder for now.
                vec![(store.clone(), pct.clone(), sym_heap.clone(), Some(SymbolicValue::Expr(Expr::IntLit(-42))))]
            }
            _ => vec![(store.clone(), pct.clone(), sym_heap.clone(), ret_val.clone())],
        }
    }

    fn run_call<F, T>(self: &Arc<Self>, name: &str, args: &Vec<WithLoc<Expr>>, store: &SymbolicStore, pct: &PathConstraint, sym_heap: &SymbolicHeap, f: F) -> Vec<T>
    where
        F: Fn(PathConstraint, SymbolicHeap, Option<SymbolicValue>) -> T + Sync,
        T: Send
    {
        let symbolized_args: Vec<(Vec<SymbolicValue>, PathConstraint, SymbolicHeap)> = args.iter().fold(vec![(vec![], pct.clone(), sym_heap.clone())], |mut acc, arg| {
            // transform each path in acc into N paths that have the current argument added
            acc.into_par_iter().flat_map(|(args, pct, sym_heap)| {
                store.symbolize(self, arg, &pct, &sym_heap).into_par_iter().map(|(arg_val, pct, sym_heap)| {
                    let mut args = args.clone();
                    args.push(arg_val);
                    (args, pct, sym_heap)
                }).collect::<Vec<_>>()
            }).collect()
        });

        symbolized_args.into_par_iter().flat_map(|(args, pct, sym_heap)| {
            self.run_func(&self.prog.find_funcdef(name).unwrap().clone(), args, &pct, &sym_heap).into_par_iter().map(|(pct, sym_heap, ret_val)| {
                f(pct, sym_heap, ret_val)
            }).collect::<Vec<_>>()
        }).collect()
    }

    // Takes arr expression, idx expression, symbolizes it with the given context, and returns the result of running the given
    // function
    /*
    Quick reason why the "prior_fn" parameter is necessary:

    fn analyze(x: int, y: int) {
        let arr = [-1; 3];
        arr[0] = non_det_42(y, arr);
        let i = 0;
        while i < 3 {
            if arr[i] == 42 {
                testcase!;
            }
            i = i + 1;
        }
        return;
    }

    fn non_det_42(idx: int, arr: [int]) -> int {
        arr[idx] = 42;
        return 69;
    }

    if we did not have prior_fn, then the store from non_det_42 would essentially get lost in the assignment statement,
    and we end with the following testcases:
    { x = 0, y = 0 } **
    { x = 0, y = 1 }
    { x = 0, y = 2 }

    however the ** marked one is not correct - if y is 0 then arr[0] = arr[y] will be overwritten and arr[i] can never be 42.

    For this reason, when calculating the indices that we pass to `f` we must work with the symbolic heap returned by the last evaluated expression,
    which in this case is the RHS of an index-assignment statement. This is what prior_fn is for, it allows us to specify other functionality to be run before
    calculating indices, i.e. evaluating the RHS.

    See the tag "symex-buggy-run-index" to see this for yourself.
     */
    fn run_index<F, T, G, U>(self: &Arc<Self>, arr: &Expr, idx: &Expr, store: &SymbolicStore, pct: &PathConstraint, sym_heap: &SymbolicHeap, prior_fn: G, f: F)
        -> Vec<T>
        where
            // TODO: Adjust Vec<T>? maybe IntoIter?
            // takes symex, sym_arr, sym_idx, pct, sym_heap
            F: Fn(&Arc<Self>, usize, &Expr, &PathConstraint, &SymbolicHeap, &U) -> Vec<T> + Sync,
            // takes symex, pct, sym_heap and returns something that will be used prior to indexing (i.e. the sym_idx passed to f is from prior_fn's returned SymbolicHeaps
            G: Fn(&Arc<Self>, PathConstraint, SymbolicHeap) -> Vec<(PathConstraint, SymbolicHeap, U)> + Sync,
            T: Send,
            U: Send + Sync,
    {
        store.symbolize(self, arr, pct, sym_heap).into_par_iter().flat_map(|(sym_arr, pct, sym_heap)| {
            // 1. sym_arr must be heap_ptr.
            let sym_arr = sym_arr.into_heap_ptr().unwrap();
            store.symbolize(self, idx, &pct, &sym_heap).into_par_iter().flat_map(|(sym_idx, pct, sym_heap)| {
                // 2. sym_idx must be an Expr.
                let sym_idx = sym_idx.into_expr().unwrap();

                prior_fn(self, pct, sym_heap).into_par_iter().flat_map(|(pct, sym_heap, data)| {
                    // TODO: additionally assume out of bounds, see if that's satisfiable, if so throw warning

                    // TODO: check out of bounds?
                    let arr_map = sym_heap.get(&sym_arr).unwrap();
                    match arr_map {
                        SymbolicArray::ExplicitArray(els) => {
                            match &sym_idx {
                                // TODO: out of bounds check
                                sym_idx@Expr::IntLit(_) => {
                                    return f(self, sym_arr, &sym_idx, &pct, &sym_heap, &data)
                                }
                                _ => {}
                            }

                            els.into_par_iter().enumerate().flat_map(|(idx, el)| {
                                // Maybe factor this out into an Index enum that is either constant, for explicit arrays, or an Expr, for default arrays?
                                let idx_exp = Expr::IntLit(idx as i64);

                                let pct_with_idx_assmpt = Expr::BinOp(
                                    WL::no_loc(BinOpcode::And),
                                    Box::new(WL::no_loc(pct.clone())),
                                    Box::new(WL::no_loc(Expr::BinOp(
                                        WL::no_loc(BinOpcode::Eq),
                                        Box::new(WL::no_loc(idx_exp.clone())),
                                        Box::new(WL::no_loc(sym_idx.clone()))
                                    )))
                                );
                                // TODO: might have an issue with this order - inside f we might (i.e. in an index assign statement)
                                // change the sym_heap once again, e.g. if the RHS is a Call, and then the actual final heap might have different indices
                                f(self, sym_arr, &idx_exp, &pct_with_idx_assmpt, &sym_heap, &data)
                            }).collect::<Vec<_>>()
                        },
                        SymbolicArray::DefaultArray { length, default, values } => {
                            // Need to do the following three things:
                            // 1. check if idx is equal to all exprs in values.keys()
                            // 2. assume idx is not equal to any of those AND length is greater than count of values.keys() AND idx is in bounds
                            // TODO 3. assume idx is out of bounds and throw warning

                            let mut paths1 = values.keys().flat_map(|idx_exp| {
                                let pct_with_idx_assmpt = Expr::BinOp(
                                    WL::no_loc(BinOpcode::And),
                                    Box::new(WL::no_loc(pct.clone())),
                                    Box::new(WL::no_loc(Expr::BinOp(
                                        WL::no_loc(BinOpcode::Eq),
                                        Box::new(WL::no_loc(idx_exp.clone())),
                                        Box::new(WL::no_loc(sym_idx.clone()))
                                    )))
                                );

                                f(self, sym_arr, &idx_exp, &pct_with_idx_assmpt, &sym_heap, &data)

                            }).collect::<Vec<_>>();

                            // All current indices are different from sym_idx
                            let paths2_pct_disjointness = values.keys().fold(
                                pct.clone(),
                                |curr_pct, idx_exp| {
                                    Expr::BinOp(
                                        WL::no_loc(BinOpcode::And),
                                        Box::new(WL::no_loc(curr_pct)),
                                        Box::new(WL::no_loc(Expr::BinOp(
                                            WL::no_loc(BinOpcode::Ne),
                                            Box::new(WL::no_loc(idx_exp.clone())),
                                            Box::new(WL::no_loc(sym_idx.clone()))
                                        )))
                                    )
                                }
                            );

                            // There must still be space for more explicitly-indexed elements
                            let paths2_pct_length = Expr::BinOp(
                                WL::no_loc(BinOpcode::Lt),
                                Box::new(WL::no_loc(Expr::IntLit(values.keys().len() as i64))),
                                Box::new(WL::no_loc(length.clone()))
                            );

                            // sym_idx < length && sym_idx >= 0
                            let paths2_pct_in_bounds = Expr::BinOp(
                                WL::no_loc(BinOpcode::And),
                                Box::new(WL::no_loc(Expr::BinOp(
                                    WL::no_loc(BinOpcode::Lt),
                                    Box::new(WL::no_loc(sym_idx.clone())),
                                    Box::new(WL::no_loc(length.clone()))
                                ))),
                                Box::new(WL::no_loc(Expr::BinOp(
                                    WL::no_loc(BinOpcode::Ge),
                                    Box::new(WL::no_loc(sym_idx.clone())),
                                    Box::new(WL::no_loc(Expr::IntLit(0)))
                                )))
                            );

                            let paths2_pct = Expr::BinOp(
                                WL::no_loc(BinOpcode::And),
                                Box::new(WL::no_loc(paths2_pct_disjointness)),
                                Box::new(WL::no_loc(Expr::BinOp(
                                    WL::no_loc(BinOpcode::And),
                                    Box::new(WL::no_loc(paths2_pct_length)),
                                    Box::new(WL::no_loc(paths2_pct_in_bounds))
                                )))
                            );

                            let paths2 = f(self, sym_arr, &sym_idx, &paths2_pct, &sym_heap, &data);

                            paths1.extend(paths2);

                            paths1
                        },
                    }
                }).collect::<Vec<_>>()
            }).collect::<Vec<_>>()
        }).collect()
    }
}

pub fn string_of_model<'a>((int_map, bool_map): &Model, order: impl Iterator<Item = &'a Var>) -> String {
    let mut visited = HashSet::new();

    let mut res = String::new();
    let mut first = true;
    res.push_str("{ ");
    for v in order {
        visited.insert(&v.0);
        let (k, _) = v.rsplit_once("_").unwrap();

        let val_string = match &v.1 {
            Type::Int => int_map[v.as_str()].to_string(),
            Type::Bool => bool_map[v.as_str()].to_string(),
            t => panic!("unexpected type {:?}", t),
        };

        if !first {
            res.push_str(", ");
        } else {
            first = false;
        }
        res.push_str(&format!("{} = {}", k, val_string));
    }
    for (iv, i) in int_map {
        if !visited.contains(iv) {
            if !first {
                res.push_str(", ");
            } else {
                first = false;
            }
            res.push_str(&format!("{} = {}", iv, i));
        }
    }

    for (bv, b) in bool_map {
        if !visited.contains(bv) {
            if !first {
                res.push_str(", ");
            } else {
                first = false;
            }
            res.push_str(&format!("{} = {}", bv, b));
        }
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

thread_local! {
    pub static Z3_TIME: RefCell<u128> = RefCell::new(0);
    pub static Z3_INVOCATIONS: RefCell<u64> = RefCell::new(0);
    pub static Z3_CACHE_HITS: RefCell<u64> = RefCell::new(0);
}

pub fn satisfiable(pct: &Expr) -> SatResult {
    // let pct_sexp = sexp_of_expr(pct);
    // let pct_egg = pct_sexp.parse().unwrap();
    // println!("pct orig sexp: {}", pct_sexp);
    // let bests = get_bests(vec![&pct_egg]);
    // println!("pct best sexp: {}", bests[0].to_string());

    // Uncomment if you want caching (slower atm) -- update(20-11): seems faster?
    if let Some(model) = cache::satisfiable(pct) {
        // println!("Cache hit! PCT: {}, model {:?}", pct, &model);
        cache::insert(pct, model.clone());
        Z3_CACHE_HITS.with(|c| *c.borrow_mut() += 1);
        return SatResult::Sat(model);
    }

    let start = SystemTime::now();

    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(1000);

    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    solver.assert(&expr_to_z3_bool(&ctx, pct));

    let res = solver.check();

    let res = match res {
        z3::SatResult::Sat => {
            // if bests[0].to_string() == "false" {
            //     println!("egg said false, z3 didn't");
            // }
            let fv = pct.free_vars();
            let calls = call_fv(pct);
            let model = map_of_model(&ctx, solver.get_model().unwrap(), &fv, &calls);
            // Uncomment if you want caching (slower atm)
            cache::insert(pct, model.clone());
            SatResult::Sat(model)
        },
        z3::SatResult::Unsat => SatResult::Unsat,
        z3::SatResult::Unknown => SatResult::Unknown(solver.get_reason_unknown().unwrap()),
    };

    let d = SystemTime::now().duration_since(start).unwrap();
    Z3_TIME.with(|t| {
        *t.borrow_mut() += d.as_millis();
    });

    Z3_INVOCATIONS.with(|t| {
        *t.borrow_mut() += 1;
    });

    res
}

fn simplify_int(e: &Expr) -> Option<i64> {
    match e {
        Expr::IntLit(i) => Some(*i),
        Expr::BinOp(op, left, right) => {
            let left = simplify_int(left)?;
            let right = simplify_int(right)?;
            let res = match &op.elem {
                BinOpcode::Add => left + right,
                BinOpcode::Sub => left - right,
                BinOpcode::Mul => left * right,
                BinOpcode::Div => left / right,
                // TODO: rem_euclid?
                BinOpcode::Mod => left % right,
                _ => return None,
            };
            Some(res)
        }
        Expr::UnOp(op, inner) => {
            let inner = simplify_int(inner)?;
            match &op.elem {
                UnOpcode::Neg => Some(-inner),
                _ => None,
            }
        }
        _ => None,
    }
}

fn call_fv(e: &Expr) -> HashSet<(String, Expr)> {
    let mut res = HashSet::new();
    match e {
        c@Expr::Call(name, args) => {
            // TODO: Assuming int_arg
            let arg_calls = args.elem.iter()
                .map(|arg| call_fv(arg))
                .fold(HashSet::new(), |mut acc, fv| {
                    acc.extend(fv);
                    acc
                });
            let args = if let Some(i) = simplify_int(&args[0]) {
                WL::no_loc(vec![WL::no_loc(Expr::IntLit(i))])
            } else { args.clone() };
            let call = Expr::Call(name.clone(), args);
            res.insert((call.to_string(), call));
            res.extend(arg_calls);
            res
        }
        Expr::BinOp(_, left, right) => {
            res.extend(call_fv(left));
            res.extend(call_fv(right));
            res
        }
        Expr::UnOp(_, inner) => {
            res.extend(call_fv(inner));
            res
        }
        Expr::Array(els) => {
            for el in els.iter() {
                res.extend(call_fv(el));
            }
            res
        }
        Expr::DefaultArray { default_value, size } => {
            res.extend(call_fv(default_value));
            res.extend(call_fv(size));
            res
        }
        Expr::Index(arr, idx) => {
            res.extend(call_fv(arr));
            res.extend(call_fv(idx));
            res
        }
        _ => res,
    }
}

fn map_of_model(ctx: &z3::Context, model: z3::Model, fv: &HashSet<Var>, calls: &HashSet<(String, Expr)>) -> (HashMap<String, i64>, HashMap<String, bool>) {
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

    for (call_name, call) in calls {
        let val = model.eval(&expr_to_z3_int(ctx, call), false).unwrap().as_i64();
        if let Some(val) = val {
            int_map.insert(call_name.clone(), val);
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
        Expr::Call(name, args) => {
            // only builtins should appear here such as int_arg
            if name.as_str() != "int_arg" {
                panic!("unsupported call: {}", exp);
            }
            let args = args.iter().map(|arg| expr_to_z3_int(ctx, arg)).collect::<Vec<_>>();
            let dynamic_args = args.iter().map(|arg| arg as &dyn z3::ast::Ast).collect::<Vec<_>>();
            // TODO: adjust these types
            let f = z3::FuncDecl::new(ctx, name.as_str(), &[&z3::Sort::int(ctx)], &z3::Sort::int(ctx));
            f.apply(&dynamic_args[..]).as_int().unwrap()
        }
        exp => panic!("unsupported int expr: {:?}", exp),
    }
}

// loop bounding

pub static UNROLL_FACTOR: usize = 9;

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


// Supposed to speed up satisfiability checks
mod cache {
    use std::borrow::Borrow;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use crate::ast::{BinOpcode, Expr, Type, WithLoc};
    use crate::se::Model;
    thread_local! {
        pub static CACHE: RefCell<HashMap<String, super::Model>> = RefCell::new(HashMap::new());
    }

    pub fn insert(exp: &Expr, model: Model) {
        CACHE.with(|cache| {
            cache.borrow_mut().insert(exp.to_string(), model.clone());
        });

        // Recursively insert AND'ed subexpressions, since having a model for an AND means
        // having a model for both conjuncts.
        match exp {
            Expr::BinOp(op, left, right) => {
                if op.elem == BinOpcode::And {
                    insert(&*left, model.clone());
                    insert(&*right, model);
                }
            }
            _ => {}
        }
    }

    pub fn satisfiable(exp: &Expr) -> Option<Model> {
        // let mut wl = WithLoc::no_loc(exp.clone());
        // wl.set_type_loc(&Type::Bool);
        satisfiable_rec(exp, 5)
    }

    fn satisfiable_rec(exp: &Expr, limit: usize) -> Option<Model> {
        if limit <= 0 {
            return None;
        }
        // As soon as we reach integers, we can stop recursing
        // not perfectly safe, as we don't add types to the PCTs we generate during symbolic execution
        // if exp.typ == Type::Int {
        //     return None;
        // }

        let exp_string = exp.to_string();
        let curr = CACHE.with(|c| {
            c.borrow().get(&exp_string).map(|m| m.clone())
        });
        if let Some(model) = curr {
            return Some(model);
        }

        match exp {
            Expr::BoolLit(true) => Some((HashMap::new(), HashMap::new())),
            Expr::BoolLit(false) => None,
            Expr::Var(v) => {
                let b_map = HashMap::from([(v.elem.to_string(), true)]);
                Some((HashMap::new(), b_map))
            }
            Expr::BinOp(op, left, right) => {
                // arg type is int
                if op.elem.get_type().0.0 == Type::Int {
                    return None;
                }

                let left_model = satisfiable_rec(left, limit - 1);

                if let Some(left_model) = left_model {
                    if super::interp::interp_bool(exp, &left_model) {
                        return Some(left_model);
                    }
                }

                let right_model = satisfiable_rec(right, limit - 1);

                if let Some(right_model) = right_model {
                    if super::interp::interp_bool(exp, &right_model) {
                        return Some(right_model);
                    }
                }

                None
            }
            Expr::UnOp(op, inner) => {
                // arg type is int
                if op.elem.get_type().0 == Type::Int {
                    return None;
                }

                let inner_model = satisfiable_rec(inner, limit - 1);

                if let Some(inner_model) = inner_model {
                    if super::interp::interp_bool(exp, &inner_model) {
                        return Some(inner_model);
                    }
                }

                None
            }
            // TODO: think about how to do this better, maybe exprs need tighter integration with
            // their types
            // _ => None,
            exp => panic!("Unsupported expression: {:?}", exp),
        }
    }

}

mod interp {
    use super::Model;
    use crate::ast::{BinOpcode, Expr, OpcodeType, Type, UnOpcode};

    pub fn interp_bool(exp: &Expr, model: &Model) -> bool {
        match exp {
            Expr::BoolLit(b) => *b,
            Expr::Var(v) => *model.1.get(v.as_str()).unwrap_or(&false),
            Expr::BinOp(op, left, right)
            if op.elem.get_type() == OpcodeType((Type::Int, Type::Int), Type::Bool)
            => {
                let left_val = interp_int(left, model);
                let right_val = interp_int(right, model);

                match &op.elem {
                    BinOpcode::Lt => left_val < right_val,
                    BinOpcode::Le => left_val <= right_val,
                    BinOpcode::Gt => left_val > right_val,
                    BinOpcode::Ge => left_val >= right_val,
                    BinOpcode::Eq => left_val == right_val,
                    BinOpcode::Ne => left_val != right_val,
                    op => panic!("Unsupported binop: {}", op),
                }

            }
            Expr::BinOp(op, left, right)
            if op.elem.get_type() == OpcodeType((Type::Bool, Type::Bool), Type::Bool)
            => {
                let left_val = interp_bool(left, model);
                let right_val = interp_bool(right, model);

                match &op.elem {
                    BinOpcode::And => left_val && right_val,
                    BinOpcode::Or => left_val || right_val,
                    op => panic!("Unsupported binop: {}", op),
                }
            }
            Expr::UnOp(op, inner) => {
                let inner_val = interp_bool(inner, model);

                match &op.elem {
                    UnOpcode::Not => !inner_val,
                    op => panic!("Unsupported unop: {}", op),
                }
            }
            // In case we call interp_bool from se::cache on an integer
            // _ => true,
            e => panic!("Unsupported expression: {}", e),
        }
    }

    pub fn interp_int(exp: &Expr, model: &Model) -> i64 {
        match exp {
            Expr::IntLit(i) => *i,
            Expr::Var(v) => *model.0.get(v.as_str()).unwrap_or(&0),
            Expr::BinOp(op, left, right) => {
                let left_val = interp_int(left, model);
                let right_val = interp_int(right, model);

                // println!("interpreting {} {} {}", left_val, &op.elem, right_val);

                match &op.elem {
                    BinOpcode::Add => left_val + right_val,
                    BinOpcode::Sub => left_val - right_val,
                    BinOpcode::Mul => left_val * right_val,
                    BinOpcode::Div => left_val / right_val,
                    // TODO: instead return Option?
                    BinOpcode::Mod => left_val.checked_rem(right_val).unwrap_or(0),
                    op => panic!("Unsupported binop: {}", op),
                }

            }
            Expr::UnOp(op, inner) => {
                let inner_val = interp_int(inner, model);

                match &op.elem {
                    UnOpcode::Neg => -inner_val,
                    op => panic!("Unsupported unop: {}", op),
                }
            }
            c@Expr::Call(name, args) => {
                // Should be only builtins
                if name.as_str() == "int_arg" {
                    let call_name = c.to_string();
                    *model.0.get(call_name.as_str()).unwrap_or(&0)
                } else {
                    panic!("Unsupported function call to: {}", name);
                }
            }
            e => panic!("Unsupported expression: {}", e),
        }
    }

}