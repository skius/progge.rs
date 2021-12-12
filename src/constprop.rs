use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use petgraph::Direction;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use crate::ast::{BinOpcode, Block, Expr, FuncDef, Loc, LocExpr, Stmt, Type, UnOpcode, Var, WithLoc};
use crate::ir::{IntraProcCFG, IREdge, IRNode};
use crate::dfa;

struct Graph(IntraProcCFG);

impl dfa::Graph for Graph {
    type Node = NodeIndex;
    type Edge = EdgeIndex;

    fn succs(&self, node: Self::Node) -> Vec<Self::Node> {
        self.0.graph.neighbors_directed(node, Direction::Outgoing).collect()
    }

    fn preds(&self, node: Self::Node) -> Vec<Self::Node> {
        self.0.graph.neighbors_directed(node, Direction::Incoming).collect()

    }

    fn edge_between(&self, from: Self::Node, to: Self::Node) -> Option<Self::Edge> {
        self.0.graph.edges_connecting(from, to).next().map(|e| e.id())

    }

    fn entry_nodes(&self) -> HashSet<Self::Node> {
        HashSet::from([self.0.entry])
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Value {
    Int(i64),
    Bool(bool),
}

impl Value {
    fn force_int(&self) -> i64 {
        match self {
            Value::Int(i) => *i,
            Value::Bool(b) => unreachable!(),
        }
    }

    fn force_bool(&self) -> bool {
        match self {
            Value::Int(_) => unreachable!(),
            Value::Bool(b) => *b,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Const {
    // Undefined variables don't really occur at the moment, because they are represented in a Fact by
    // not being represented
    Undefined,
    NonConst,
    Const(Value),
}

impl Const {
    fn merge(&self, other: &Const) -> Const {
        match (self, other) {
            (Const::NonConst, _) => Const::NonConst,
            (_, Const::NonConst) => Const::NonConst,
            (&Const::Const(v1), &Const::Const(v2)) if v1 != v2 => Const::NonConst,
            (&Const::Const(v1), _) => Const::Const(v1),
            (_, &Const::Const(v2)) => Const::Const(v2),
            (Const::Undefined, Const::Undefined) => Const::Undefined,
        }
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Const::Undefined => write!(f, "undef"),
            Const::NonConst => write!(f, "nonconst"),
            Const::Const(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
struct Fact(pub HashMap<Var, Const>);

impl dfa::Fact<Graph> for Fact {
    fn merge<'a>(_: &Graph, facts: impl IntoIterator<Item=&'a Self>) -> Self where Self: 'a {
        let mut acc: HashMap<Var, Const> = HashMap::new();

        for fact in facts.into_iter() {
            for (var, new_const) in fact.0.iter() {
                match acc.entry(var.clone()) {
                    Entry::Occupied(mut entry) => {
                        entry.insert(new_const.merge(entry.get()));
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(new_const.clone());
                    }
                }
            }
        }

        Fact(acc)
    }
}

impl Display for Fact {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, (v, c)) in self.0.iter().enumerate() {
            write!(f, "{}: {}", v, c)?;
            if i < self.0.len() - 1 {
                write!(f, ",\\n")?;
            }
        }
        write!(f, "}}")
    }
}

fn eval_const_exp(exp: &Expr, state: &HashMap<Var, Const>) -> Option<Value> {
    match exp {
        Expr::IntLit(i) => Some(Value::Int(*i)),
        Expr::BoolLit(b) => Some(Value::Bool(*b)),
        Expr::Var(v) => {
            let elt = state.get(v)?;
            match elt {
                Const::Const(v) => Some(v.clone()),
                _ => None,
            }
        },
        Expr::BinOp(op, left, right) => {
            let left = eval_const_exp(left, state)?;
            let right = eval_const_exp(right, state)?;
            match &op.elem {
                BinOpcode::Add => Some(Value::Int(left.force_int() + right.force_int())),
                BinOpcode::Sub => Some(Value::Int(left.force_int() - right.force_int())),
                BinOpcode::Mul => Some(Value::Int(left.force_int() * right.force_int())),
                BinOpcode::Div => Some(Value::Int(left.force_int() / right.force_int())),
                BinOpcode::Mod => Some(Value::Int(left.force_int() % right.force_int())),
                BinOpcode::Eq => Some(Value::Bool(left == right)),
                BinOpcode::Ne => Some(Value::Bool(left != right)),
                BinOpcode::Lt => Some(Value::Bool(left.force_int() < right.force_int())),
                BinOpcode::Le => Some(Value::Bool(left.force_int() <= right.force_int())),
                BinOpcode::Gt => Some(Value::Bool(left.force_int() > right.force_int())),
                BinOpcode::Ge => Some(Value::Bool(left.force_int() >= right.force_int())),
                BinOpcode::And => Some(Value::Bool(left.force_bool() && right.force_bool())),
                BinOpcode::Or => Some(Value::Bool(left.force_bool() || right.force_bool())),
            }
        }
        Expr::UnOp(op, inner) => {
            let inner = eval_const_exp(inner, state)?;
            match &op.elem {
                UnOpcode::Neg => Some(Value::Int(-inner.force_int())),
                UnOpcode::Not => Some(Value::Bool(!inner.force_bool())),
            }
        }
        _ => None,
    }
}

pub fn run(func: FuncDef) -> FuncDef {
    let graph = Graph(IntraProcCFG::from(&func));

    let flow = |node: NodeIndex, fact: Fact, _prev_fact: &Fact| -> HashMap<Var, Const> {
        let mut state = fact.0;
        let ir_node = graph.0.graph.node_weight(node).unwrap();

        match &ir_node.elem {
            IRNode::IRDecl(v, exp) => {
                match eval_const_exp(exp, &state) {
                    Some(val) => {
                        state.insert(v.clone(), Const::Const(val));
                    },
                    None => {},
                }
            }
            IRNode::IRAssn(LocExpr::Var(v), exp) => {
                match eval_const_exp(exp, &state) {
                    Some(val) => {
                        state.insert(v.elem.clone(), Const::Const(val));
                    },
                    None => {},
                }
            }
            // The rest doesn't change state
            _ => {}
        }

        state
    };

    let get_succ_fact = |edge: EdgeIndex, i: &HashMap<Var, Const>| {
        // It doesn't matter which edge we're passing this information over
        Fact(i.clone())
    };

    let (in_flows, edge_flows) = dfa::dfa(
        &graph,
        flow,
        get_succ_fact,
        // TODO: Actually, start fact should be NonConst for all parameters
        &Fact(HashMap::new()));


    graph.graphviz(&edge_flows);

    // Now constant propagation would be:
    // for every expression, replace occurences of vars with their dfa values if they're constant
    // -- ok done
    let mut new_func = func.clone();
    let state_map = in_flows.into_iter().map(|(node_idx, fact)| {
        let node = graph.0.graph.node_weight(node_idx).unwrap();
        (node.loc, fact.0)
    }).collect();
    replace_consts_block(&mut new_func.body, &state_map);
    println!("{}", new_func);

    let live_out = crate::liveness::run(IntraProcCFG::from(&new_func));

    let live_map = live_out.into_iter().map(|(node_idx, fact)| {
        // TODO: graph should actually be the new graph from new_func
        let node = graph.0.graph.node_weight(node_idx).unwrap();
        (node.loc, fact.0)
    }).collect();

    new_func.body.elem = dce_block(&new_func.body.elem, &live_map);

    println!("{}", new_func);

    let assign_cfg = IntraProcCFG::from(&new_func);
    let assign_cfg_copy = IntraProcCFG::from(&new_func);

    let assign_live_out = crate::assign_liveness::run(assign_cfg);

    let assign_live_map = assign_live_out.into_iter().map(|(node_idx, fact)| {
        let node = assign_cfg_copy.graph.node_weight(node_idx).unwrap();
        (node.loc, fact.0)
    }).collect();

    new_func.body.elem = dce_block_assign(&new_func.body.elem, &assign_live_map);

    println!("{}", new_func);

    new_func
}

// TODO: clean all this up

// TODO: implement assign-liveness analysis that just checks whether for some let-binding a variable is being reassigned
// because then if in "let x = ..." x is not assign-live out, then we can savely get rid of the let-binding.
// done, see the assign_ stuff

// TODO: in constant propagation check ifs and always do if resp. else if cond is true resp. false

fn dce_block_assign(block: &Block, assign_live_map: &HashMap<Loc, HashSet<Var>>) -> Block {
    let mut new_block = vec![];

    for stmt in block.iter() {
        let assign_live = assign_live_map.get(&stmt.loc).unwrap();
        match &stmt.elem {
            Stmt::Decl(v, _) => {
                if assign_live.contains(&v.elem) {
                    new_block.push(stmt.clone());
                }
            }
            Stmt::Assn(le, _) => {
                match &le.elem {
                    LocExpr::Var(v) => {
                        if assign_live.contains(&v.elem) {
                            new_block.push(stmt.clone());
                        }
                    },
                    _ => {
                        new_block.push(stmt.clone());
                    },
                }
            }
            Stmt::IfElse { cond, if_branch, else_branch } => {
                let new_if_branch = dce_block_assign(if_branch, assign_live_map);
                let new_else_branch = dce_block_assign(else_branch, assign_live_map);
                new_block.push(WithLoc::new(Stmt::IfElse {
                    cond: cond.clone(),
                    if_branch: WithLoc::new(new_if_branch, if_branch.loc),
                    else_branch: WithLoc::new(new_else_branch, else_branch.loc),
                }, stmt.loc));
            }
            Stmt::While { cond, block } => {
                let new_w_block = dce_block_assign(block, assign_live_map);
                new_block.push(WithLoc::new(Stmt::While {
                    cond: cond.clone(),
                    block: WithLoc::new(new_w_block, block.loc),
                }, stmt.loc));
            }
            _ => {
                new_block.push(stmt.clone());
            }
        }
    }

    Block(new_block)
}

fn dce_block(block: &Block, live_map: &HashMap<Loc, HashSet<Var>>) -> Block {
    let mut new_block = vec![];

    for stmt in block.iter() {
        let live = live_map.get(&stmt.loc).unwrap();
        match &stmt.elem {
            Stmt::Assn(le, _) => {
                match &le.elem {
                    LocExpr::Var(v) => {
                        if live.contains(&v.elem) {
                            new_block.push(stmt.clone());
                        }
                    },
                    _ => {
                        new_block.push(stmt.clone());
                    },
                }
            }
            Stmt::IfElse { cond, if_branch, else_branch } => {
                let new_if_branch = dce_block(if_branch, live_map);
                let new_else_branch = dce_block(else_branch, live_map);
                new_block.push(WithLoc::new(Stmt::IfElse {
                    cond: cond.clone(),
                    if_branch: WithLoc::new(new_if_branch, if_branch.loc),
                    else_branch: WithLoc::new(new_else_branch, else_branch.loc),
                }, stmt.loc));
            }
            Stmt::While { cond, block } => {
                let new_w_block = dce_block(block, live_map);
                new_block.push(WithLoc::new(Stmt::While {
                    cond: cond.clone(),
                    block: WithLoc::new(new_w_block, block.loc),
                }, stmt.loc));
            }
            _ => {
                new_block.push(stmt.clone());
            }
        }
    }

    Block(new_block)
}

fn replace_consts_block(b: &mut Block, state_map: &HashMap<Loc, HashMap<Var, Const>>) {
    for stmt in b.iter_mut() {
        let state = &state_map[&stmt.loc];
        replace_consts_stmt(stmt, state_map, state);
    }
}

fn replace_consts_stmt(stmt: &mut Stmt, state_map: &HashMap<Loc, HashMap<Var, Const>>, state: &HashMap<Var, Const>) {
    match stmt {
        Stmt::Return(Some(exp)) => {
            replace_consts_exp(exp, state_map, state);
        },
        Stmt::Decl(_, exp) => {
            replace_consts_exp(exp, state_map, state);
        },
        Stmt::Assn(le, exp) => {
            replace_consts_exp(exp, state_map, state);
            match &mut le.elem {
                LocExpr::Index(src, idx) => {
                    replace_consts_exp(src, state_map, state);
                    replace_consts_exp(idx, state_map, state);
                },
                _ => {},
            }
        },
        Stmt::Call(_, args) => {
            for arg in args.iter_mut() {
                replace_consts_exp(arg, state_map, state);
            }
        }
        Stmt::IfElse { cond, if_branch, else_branch } => {
            replace_consts_exp(cond, state_map, state);
            replace_consts_block(if_branch, state_map);
            replace_consts_block(else_branch, state_map);
        },
        Stmt::While { cond, block } => {
            replace_consts_exp(cond, state_map, state);
            replace_consts_block(block, state_map);
        },
        _ => {},
    }
}

fn replace_consts_exp(exp: &mut Expr, state_map: &HashMap<Loc, HashMap<Var, Const>>, state: &HashMap<Var, Const>) {
    match exp {
        Expr::IntLit(_) => {}
        Expr::BoolLit(_) => {}
        Expr::Var(v) => {
            match state.get(v) {
                Some(Const::Const(val)) => {
                    match &v.elem.1 {
                        Type::Int => *exp = Expr::IntLit(val.force_int()),
                        Type::Bool => *exp = Expr::BoolLit(val.force_bool()),
                        _ => unreachable!(),
                    };
                },
                _ => {},
            }
        }
        Expr::Call(_, args) => {
            for arg in args.iter_mut() {
                replace_consts_exp(arg, state_map, state);
            }
        }
        Expr::BinOp(op, left, right) => {
            replace_consts_exp(left, state_map, state);
            replace_consts_exp(right, state_map, state);
        }
        Expr::UnOp(_, inner) => {
            replace_consts_exp(inner, state_map, state);
        }
        Expr::Array(els) => {
            for el in els.iter_mut() {
                replace_consts_exp(el, state_map, state);
            }
        }
        Expr::DefaultArray { default_value, size } => {
            replace_consts_exp(default_value, state_map, state);
            replace_consts_exp(size, state_map, state);
        },
        Expr::Index(src, idx) => {
            replace_consts_exp(src, state_map, state);
            replace_consts_exp(idx, state_map, state);
        }
    }
}

impl Graph {
    fn graphviz(&self, edge_flows: &HashMap<EdgeIndex, Fact>) {
        let edge_getter = |_, edge: EdgeReference<IREdge>| {
            format!(
                "label = \"{}\"",
                &edge_flows[&edge.id()]
            )
        };
        let node_getter = |_, _| format!("");

        let dot = Dot::with_attr_getters(
            &self.0.graph,
            &[Config::EdgeNoLabel],
            &edge_getter,
            &node_getter,
        );
        println!("{}", dot)
    }
}