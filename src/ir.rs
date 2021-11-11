use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::ops::Deref;

use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};

use IREdge::*;
use IRNode::*;

use crate::ast::*;

pub struct IntraProcCFG {
    pub graph: IntraGraph,
    pub entry: NodeIndex,
    pub exit: NodeIndex,
    pub params: Vec<Param>,
}

type IntraGraph = DiGraph<WithLoc<IRNode>, IREdge>;

#[derive(Clone, Debug)]
pub enum IRNode {
    IRTestcase,
    IRUnreachable,
    IRSkip,
    IRDecl(Var, Expr),
    IRAssn(LocExpr, Expr),
    IRCall(WithLoc<String>, WithLoc<Vec<Expr>>),
    IRReturn(Option<Expr>),

    IRCBranch(Expr),
    IRBranch,
}

impl IRNode {
    pub fn free_vars(&self) -> HashSet<Var> {
        match self {
            IRDecl(v, e) => {
                let mut fv = e.free_vars();
                fv.insert(v.clone());
                fv
            }
            IRAssn(le, e) => {
                let mut fv = e.free_vars();
                fv.extend(le.free_vars());
                fv
            }
            IRCall(_, es) => {
                let mut fv = HashSet::new();
                for e in es.iter() {
                    fv.extend(e.free_vars());
                }
                fv
            }
            IRReturn(Some(e)) => e.free_vars(),
            IRReturn(None) => HashSet::new(),
            IRCBranch(e) => e.free_vars(),
            IRUnreachable | IRTestcase | IRSkip | IRBranch => HashSet::new(),
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
            IRCall(name, args) => {
                f.write_str(&format!("{}({})", name, sep_string_display(args, ", ")))
            }
            IRReturn(Some(e)) => f.write_str(&format!("return {}", e)),
            IRReturn(None) => f.write_str(&format!("return")),
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

impl IntraProcCFG {
    fn add_block_to_graph(
        &mut self,
        block: &Block,
        mut prev_nodes: Vec<(NodeIndex, IREdge)>,
    ) -> Vec<(NodeIndex, IREdge)> {
        for stm in &**block {
            match **stm {
                Stmt::Testcase() => {
                    let added = self.graph.add_node(WithLoc::new(IRTestcase, stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    prev_nodes = vec![(added, Fallthrough)];
                }
                Stmt::Unreachable() => {
                    let added = self.graph.add_node(WithLoc::new(IRUnreachable, stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    prev_nodes = vec![(added, Fallthrough)];
                }
                Stmt::Return(ref e_opt) => {
                    let added = match e_opt {
                        Some(e) => self.graph.add_node(WithLoc::new(IRReturn(Some(e.elem.clone())), stm.loc)),
                        None => self.graph.add_node(WithLoc::new(IRReturn(None), stm.loc)),
                    };
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    // prev_nodes = vec![(added, Fallthrough)];
                    self.graph.add_edge(added, self.exit, Fallthrough);
                    prev_nodes = vec![];
                }
                Stmt::Decl(ref v, ref e) => {
                    let added = self.graph.add_node(WithLoc::new(IRDecl(v.elem.clone(), e.elem.clone()), stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    prev_nodes = vec![(added, Fallthrough)];
                }
                Stmt::Assn(ref le, ref e) => {
                    let added = self.graph.add_node(WithLoc::new(IRAssn(le.elem.clone(), e.elem.clone()), stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    prev_nodes = vec![(added, Fallthrough)];
                }
                Stmt::Call(ref f, ref args) => {
                    let added = self.graph.add_node(WithLoc::new(IRCall(f.clone(), WithLoc::new(args.iter().map(|arg| arg.elem.clone()).collect(), args.loc)), stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, added, *connect_prev);
                    }
                    prev_nodes = vec![(added, Fallthrough)];
                }
                Stmt::IfElse {
                    ref cond,
                    ref if_branch,
                    ref else_branch,
                } => {
                    let branch = self.graph.add_node(WithLoc::new(IRCBranch(cond.deref().clone()), stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, branch, *connect_prev);
                    }

                    // let if_root = graph.add_node(IRSkip);
                    // let else_root = graph.add_node(IRSkip);
                    // graph.add_edge(branch, if_root, Taken);
                    // graph.add_edge(branch, else_root, NotTaken);

                    let mut prev_nodes_if = self.add_block_to_graph(if_branch, vec![(branch, Taken)]);
                    let mut prev_nodes_else =
                        self.add_block_to_graph(else_branch, vec![(branch, NotTaken)]);

                    prev_nodes_if.append(&mut prev_nodes_else);
                    prev_nodes = prev_nodes_if;
                }
                Stmt::While {
                    ref cond,
                    ref block,
                } => {
                    // prev -> branch -TRUE-> block_root -> ...block... |
                    //          | /\-------------------------------------
                    //          |
                    //          -FALSE---> after_node

                    let branch = self.graph.add_node(WithLoc::new(IRCBranch(cond.deref().clone()), stm.loc));
                    for (prev_node, connect_prev) in &prev_nodes {
                        self.graph.add_edge(*prev_node, branch, *connect_prev);
                    }
                    // let block_root = graph.add_node(IRSkip);
                    // graph.add_edge(branch, block_root, Taken);
                    let prev_nodes_block = self.add_block_to_graph(block, vec![(branch, Taken)]);
                    for (prev_node, connect_prev) in prev_nodes_block {
                        self.graph.add_edge(prev_node, branch, connect_prev);
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
}

impl From<&FuncDef> for IntraProcCFG {
    fn from(f: &FuncDef) -> Self {
        let mut graph = IntraGraph::new();
        let entry = graph.add_node(WithLoc::no_loc(IRSkip));
        let exit = graph.add_node(WithLoc::no_loc(IRSkip));

        let mut res = IntraProcCFG {
            graph,
            entry,
            exit,
            params: f.params.elem.clone(),
        };

        let prev_node = entry;
        let _exit_nodes = res.add_block_to_graph(&f.body, vec![(prev_node, Fallthrough)]);

        res
    }
}

impl IntraProcCFG {
    pub fn graphviz(&self) -> String {
        format!("{}", Dot::with_config(&self.graph, &[]))
    }
}
