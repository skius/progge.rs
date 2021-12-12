use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

pub trait Graph {
    type Node: Copy + Hash + Eq;
    type Edge: Copy + Hash + Eq;

    fn succs(&self, node: Self::Node) -> Vec<Self::Node>;
    fn preds(&self, node: Self::Node) -> Vec<Self::Node>;
    fn edge_between(&self, from: Self::Node, to: Self::Node) -> Option<Self::Edge>;

    fn entry_nodes(&self) -> HashSet<Self::Node>;
}

// TODO: Decide if these functions really need a reference to the graph
pub trait Fact<G: Graph>: Clone + Eq {
    fn merge<'a>(graph: &G, facts: impl IntoIterator<Item = &'a Self>) -> Self
    where
        Self: 'a;

    fn bottom(graph: &G) -> Self {
        Self::merge(graph, [])
    }
}

// Returns in-flows and edge-flows of each Node and Edge
// (L for Lattice, facts are part of a lattice)
/*
Idea is that you can flow(curr_node, in_fact, prev_in_fact) and that results in some intermediate: I.
then for each successor of current_node, you get it's new state with get_succ_fact(edge, intermediate)
*/
pub fn dfa<G, L, F, F2, I>(graph: &G, mut flow: F, mut get_succ_fact: F2, start_fact: &L) -> (HashMap<G::Node, L>, HashMap<G::Edge, L>)
where
    G: Graph,
    L: Fact<G>,
    F: FnMut(G::Node, L, &L) -> I,
    F2: FnMut(G::Edge, &I) -> L,
{
    // Iterative DFA worklist algorithm

    let mut in_flow = HashMap::new();
    let mut edge_flows: HashMap<G::Edge, L> = HashMap::new();

    let entry_nodes = graph.entry_nodes();

    let mut worklist = entry_nodes.clone().into_iter().collect::<VecDeque<_>>();
    let bottom = L::bottom(graph);

    // We want to handle all edges at least once
    let mut visited = HashSet::new();

    while !worklist.is_empty() {
        let node = worklist.pop_front().unwrap();


        let in_fact = if entry_nodes.contains(&node) {
            start_fact.clone()
        } else {
            let mut in_facts = Vec::new();
            for pred in graph.preds(node) {
                let pred_fact = edge_flows.get(&graph.edge_between(pred, node).unwrap()).unwrap_or_else(|| &bottom);
                in_facts.push(pred_fact);
            }

            L::merge(graph, in_facts.into_iter())
        };

        let prev_in_fact = in_flow.get(&node).unwrap_or_else(|| &bottom).clone();
        if prev_in_fact == in_fact && visited.contains(&node) {
            // Nothing changed, so we can skip handling the outflow of this node IF we have handled it once before
            continue;
        }
        visited.insert(node);

        in_flow.insert(node, in_fact.clone());

        let out_fact = flow(node, in_fact, &prev_in_fact);

        for succ in graph.succs(node) {
            let e = graph.edge_between(node, succ).unwrap();
            let succ_fact = get_succ_fact(e, &out_fact);
            edge_flows.insert(e, succ_fact);
            worklist.push_back(succ);
        }
    }

    (in_flow, edge_flows)
}
