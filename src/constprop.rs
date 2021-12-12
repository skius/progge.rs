// TODO: perhaps extract all the various analyses into a separate module?

use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::fmt::{Display, Formatter};
use petgraph::Direction;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use crate::ast::{BinOpcode, Expr, LocExpr, UnOpcode, Var, WithLoc};
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
struct Fact(HashMap<Var, Const>);

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

pub fn run(cfg: IntraProcCFG) {
    let graph = Graph(cfg);

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
        &Fact(HashMap::new()));


    graph.graphviz(&edge_flows);
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