use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::ops::Deref;
use petgraph::Direction;
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::dot::{Config, Dot};
use crate::ast::*;
use petgraph::graph::{DiGraph, NodeIndex};
use crate::ast::Stmt::Testcase;

pub struct IntraProcCFG {
    pub graph: IntraGraph,
    pub entry: NodeIndex,
    pub params: Vec<Param>,
}

type IntraGraph = DiGraph<IRNode, IREdge>;

use IRNode::*;
use IREdge::*;

#[derive(Clone, Debug)]
pub enum IRNode {
    IRTestcase,
    IRUnreachable,
    IRSkip,
    IRDecl(Var, Expr),
    IRAssn(Var, Expr),
    IRReturn(Expr),

    IRCBranch(Expr),
    IRBranch,
}

impl IRNode {
    pub fn free_vars(&self) -> Vec<Var> {
        match self {
            IRDecl(v, e) | IRAssn(v, e) => {
                let mut fv = e.free_vars();
                fv.push(v.clone());
                fv
            },
            IRReturn(e) => e.free_vars(),
            IRCBranch(e) => e.free_vars(),
            _ => vec![],
        }
    }
}

impl Display for IRNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            IRTestcase => f.write_str("testcase!"),
            IRUnreachable => f.write_str("unreachable!"),
            IRSkip => f.write_str("skip"),
            IRDecl(v, e) => f.write_str(&format!("let {} = {}", v, e)),
            IRAssn(v, e) => f.write_str(&format!("{} = {}", v, e)),
            IRReturn(e) => f.write_str(&format!("return {}", e)),
            IRCBranch(e) => f.write_str(&format!("<cbranch> {}", e)),
            IRBranch => f.write_str("<branch>"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IREdge {
    Fallthrough,
    Taken,
    NotTaken,
}

impl Display for IREdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Fallthrough => f.write_str(""),
            Taken => f.write_str("true"),
            NotTaken => f.write_str("false"),
        }
    }
}

fn add_block_to_graph(graph: &mut IntraGraph, block: &Block, mut prev_nodes: Vec<(NodeIndex, IREdge)>) -> Vec<(NodeIndex, IREdge)> {
    for stm in &**block {
        match **stm {
            Stmt::Testcase() => {
                let added = graph.add_node(IRTestcase);
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, added, *connect_prev);
                }
                prev_nodes = vec![(added, Fallthrough)];
            }
            Stmt::Unreachable() => {
                let added = graph.add_node(IRUnreachable);
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, added, *connect_prev);
                }
                prev_nodes = vec![(added, Fallthrough)];
            }
            Stmt::Return(ref e) => {
                let added = graph.add_node(IRReturn(e.elem.clone()));
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, added, *connect_prev);
                }
                // prev_nodes = vec![(added, Fallthrough)];
                prev_nodes = vec![];
            }
            Stmt::Decl(ref v, ref e) => {
                let added = graph.add_node(IRDecl(v.elem.clone(), e.elem.clone()));
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, added, *connect_prev);
                }
                prev_nodes = vec![(added, Fallthrough)];
            }
            Stmt::Assn(ref v, ref e) => {
                let added = graph.add_node(IRAssn(v.elem.clone(), e.elem.clone()));
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, added, *connect_prev);
                }
                prev_nodes = vec![(added, Fallthrough)];
            }
            Stmt::IfElse { ref cond, ref if_branch, ref else_branch } => {
                let branch = graph.add_node(IRCBranch(cond.deref().clone()));
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, branch, *connect_prev);
                }

                // let if_root = graph.add_node(IRSkip);
                // let else_root = graph.add_node(IRSkip);
                // graph.add_edge(branch, if_root, Taken);
                // graph.add_edge(branch, else_root, NotTaken);

                let mut prev_nodes_if = add_block_to_graph(graph, if_branch, vec![(branch, Taken)]);
                let mut prev_nodes_else = add_block_to_graph(graph, else_branch, vec![(branch, NotTaken)]);

                prev_nodes_if.append(&mut prev_nodes_else);
                prev_nodes = prev_nodes_if;
            }
            Stmt::While { ref cond, ref block } => {

                // prev -> branch -TRUE-> block_root -> ...block... |
                //          | /\-------------------------------------
                //          |
                //          -FALSE---> after_node

                let branch = graph.add_node(IRCBranch(cond.deref().clone()));
                for (prev_node, connect_prev) in &prev_nodes {
                    graph.add_edge(*prev_node, branch, *connect_prev);
                }
                // let block_root = graph.add_node(IRSkip);
                // graph.add_edge(branch, block_root, Taken);
                let prev_nodes_block = add_block_to_graph(graph, block, vec![(branch, Taken)]);
                for (prev_node, connect_prev) in prev_nodes_block {
                    graph.add_edge(prev_node, branch, connect_prev);
                }

                prev_nodes = vec![(branch, NotTaken)];
            }
        }

        if prev_nodes.is_empty() {
            // will never add new nodes
            break;
        }
    }

    prev_nodes
}

impl From<&FuncDef> for IntraProcCFG {
    fn from(f: &FuncDef) -> Self {
        let mut graph = DiGraph::new();
        let entry = graph.add_node(IRSkip);

        let mut prev_node = entry;
        let exit_nodes = add_block_to_graph(&mut graph, &f.body, vec![(prev_node, Fallthrough)]);

        IntraProcCFG {
            graph,
            entry,
            params: f.params.clone(),
        }
    }
}

// fn add_to_new(old_graph: &IntraGraph, graph: &mut IntraGraph, old_to_new: &mut HashMap<NodeIndex, NodeIndex>, old_idx: NodeIndex) -> NodeIndex {
//     let new_idx = if !old_to_new.contains_key(&old_idx) {
//         let new_neighbor = graph.add_node(old_graph[old_idx].clone());
//         old_to_new.insert(old_idx, new_neighbor);
//         new_neighbor
//     } else {
//         old_to_new[&old_idx]
//     };
//     new_idx
// }
//
// pub fn remove_unnecessary_skips(cfg: &IntraProcCFG) -> IntraProcCFG {
//     let mut graph = IntraGraph::new();
//     let old_graph = &cfg.graph;
//     let mut old_to_new: HashMap<NodeIndex, NodeIndex> = HashMap::new();
//
//     let mut succs_of_old = |idx: NodeIndex| {
//         // I think IRSkip can only have one successor by construction
//         let outgoing_neighbors = old_graph.neighbors_directed(idx, Outgoing);
//         let outgoing_neighbors = outgoing_neighbors.collect::<Vec<_>>();
//         // assert_eq!(outgoing_neighbors.len(), 1);
//         // let succ = outgoing_neighbors[0];
//         // succ
//         outgoing_neighbors
//     };
//
//     // let mut add_to_new = |old_idx: NodeIndex| {
//     //
//     // };
//
//     for node_idx in old_graph.node_indices() {
//         let node = &old_graph[node_idx];
//         if let IRSkip = node {
//             let succs = succs_of_old(node_idx);
//             if succs.len() == 0 {
//                 // if incoming edge is fallthrough we can delete, only branch must be kept
//                 continue;
//             } else if succs.len() > 1 {
//                 assert!(false);
//             }
//             let succ = succs[0];
//
//             let incoming_neighbors = old_graph.neighbors_directed(node_idx, Incoming);
//             for neighbor in incoming_neighbors {
//                 let edges = old_graph.edges_connecting(neighbor, node_idx);
//                 let edges: Vec<_> = edges.collect();
//                 let edge = edges[0];
//                 let edge = *edge.weight();
//
//                 // let new_neighbor = if !old_to_new.contains_key(&neighbor) {
//                 //     let new_neighbor = graph.add_node(old_graph[neighbor].clone());
//                 //     old_to_new.insert(neighbor, new_neighbor);
//                 //     new_neighbor
//                 // } else {
//                 //     old_to_new[neighbor]
//                 // };
//                 let new_neighbor = add_to_new(&old_graph, &mut graph, &mut old_to_new, neighbor);
//                 let new_succ = add_to_new(&old_graph, &mut graph, &mut old_to_new, succ);
//
//                 graph.add_edge(new_neighbor, new_succ, edge);
//             }
//         } else {
//             // Not IRSkip
//             let new_idx = add_to_new(&old_graph, &mut graph, &mut old_to_new, node_idx);
//
//             let inc_neighbors = old_graph.neighbors_directed(node_idx, Incoming);
//             for neighbor in inc_neighbors {
//                 let edge = old_graph.edges_connecting(neighbor, node_idx).collect::<Vec<_>>()[0];
//                 let edge = *edge.weight();
//
//                 let new_neighbor = add_to_new(&old_graph, &mut graph, &mut old_to_new, neighbor);
//                 graph.add_edge(new_neighbor, new_idx, edge);
//             }
//         }
//     }
//
//     IntraProcCFG {
//         graph,
//         entry: cfg.entry,
//         params: cfg.params.clone(),
//     }
// }

impl IntraProcCFG {
    pub fn graphviz(&self) -> String {
        format!("{}", Dot::with_config(&self.graph, &[]))
    }
}




pub fn do_stuff() {
    // let x = IntraProcCFG(DiGraph::new());
    // let mut x = x.0;
    //
    // let tc = x.add_node(IRTestcase);
    // let tc2 = x.add_node(IRTestcase);
    //
    // // x.edges_directed(tc, Direction::Incoming);
    //
    // println!("{}", x.node_count());
}