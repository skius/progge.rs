// TODO: perhaps extract all the various analyses into a separate module?

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use petgraph::Direction;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::EdgeRef;
use crate::ast::{LocExpr, Var, WithLoc};
use crate::ir::{IntraProcCFG, IREdge, IRNode};
use crate::dfa;

struct Graph(IntraProcCFG);

impl dfa::Graph for Graph {
    type Node = NodeIndex;
    type Edge = EdgeIndex;

    fn succs(&self, node: Self::Node) -> Vec<Self::Node> {
        // Reverse Incoming/Outgoing, because Liveness is a backwards analysis
        self.0.graph.neighbors_directed(node, Direction::Incoming).collect()
    }

    fn preds(&self, node: Self::Node) -> Vec<Self::Node> {
        self.0.graph.neighbors_directed(node, Direction::Outgoing).collect()

    }

    fn edge_between(&self, from: Self::Node, to: Self::Node) -> Option<Self::Edge> {
        // to and from reversed, because Liveness is a backwards analysis
        self.0.graph.edges_connecting(to, from).next().map(|e| e.id())

    }

    fn entry_nodes(&self) -> HashSet<Self::Node> {
        // TODO: do I really want IntraProcCFG to only have one exit? currently all returns go to a skip
        HashSet::from([self.0.exit])
    }
}

#[derive(Clone, Eq, PartialEq)]
struct Fact(HashSet<Var>);

impl dfa::Fact<Graph> for Fact {
    fn merge<'a>(_: &Graph, facts: impl IntoIterator<Item=&'a Self>) -> Self where Self: 'a {
        facts.into_iter().fold(Fact(HashSet::new()), |mut acc, fact| {
            acc.0.extend(fact.0.iter().cloned());
            acc
        })
    }
}

impl Display for Fact {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, v) in self.0.iter().enumerate() {
            write!(f, "{}", v)?;
            if i < self.0.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

fn gen(node: &IRNode) -> HashSet<Var> {
    let mut res = HashSet::new();
    match node {
        IRNode::IRDecl(_, exp) => exp.free_vars(),
        IRNode::IRAssn(LocExpr::Index(src, idx), exp) => {
            let mut res = exp.free_vars();
            res.extend(src.free_vars());
            res.extend(idx.free_vars());
            res
        }
        IRNode::IRCall(_, exps) => {
            exps.iter()
                .fold(res, |mut acc, exp| {
                    acc.extend(exp.free_vars());
                    acc
                })
        }
        IRNode::IRReturn(exp) => exp.as_ref().map(|e| e.free_vars()).unwrap_or(res),
        IRNode::IRCBranch(exp) => exp.free_vars(),
        _ => res,
    }
}

fn kill(node: &IRNode) -> HashSet<Var> {
    let mut res = HashSet::new();
    match node {
        IRNode::IRDecl(v, _) => HashSet::from([v.clone()]),
        IRNode::IRAssn(LocExpr::Var(v), _) => HashSet::from([v.elem.clone()]),
        _ => res,
    }
}

pub fn run(cfg: IntraProcCFG) {
    // TODO: perhaps provide generic adaptor in IntraProcCFG for data-flow analyses?
    // would have forward/backwards and may/must over some set over generic T

    let graph = Graph(cfg);

    let flow = |node: NodeIndex, fact: Fact, _prev_fact: &Fact| -> HashSet<Var> {
        let mut live = fact.0;
        let ir_node = graph.0.graph.node_weight(node).unwrap();

        let gen = gen(&ir_node);
        let kill = kill(&ir_node);

        let live = live.difference(&kill).cloned().collect::<HashSet<_>>();
        let live = live.union(&gen).cloned().collect::<HashSet<_>>();

        // We forward (remember backwards, so our input fact comes from our successors and we compute what we pass
        // onwards to our predecessors) the set: GEN + (LIVE - KILL)

        live
    };

    let get_succ_fact = |edge: EdgeIndex, i: &HashSet<Var>| {
        // It doesn't matter which edge we're passing this information over
        Fact(i.clone())
    };

    // Again, because of backwards analysis, the "in_flows" are actually out-flows
    let (in_flows, edge_flows) = dfa::dfa(
        &graph,
        flow,
        get_succ_fact,
        // Nothing is live at the exits
        &Fact(HashSet::new()));


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