use std::collections::{HashMap, VecDeque};
use elina::ast::{Abstract, Environment, Hcons, Manager, OptPkManager, Tcons, Texpr, TexprBinop, TexprUnop};
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference};
use petgraph::prelude::Dfs;
use petgraph::visit::{EdgeRef, IntoEdges, Visitable};
use crate::ast::{Expr, UnOpcode, WithLoc};
use crate::ast::BinOpcode;
use crate::ir::{IntraProcCFG, IREdge, IRNode};

// TODO: current state of affairs: Need abstract equal to allow for loops, also need abstract widening for that.
// TODO: free_vars should work with a HashSet

pub fn graphviz_with_states<M: Manager>(
    cfg: &IntraProcCFG,
    man: &M,
    env: &Environment,
    state_map: &HashMap<EdgeIndex, Abstract>
) -> String {
    let edge_getter = |_, edge: EdgeReference<IREdge>| {
        let mut intervals = "".to_owned();
        let vars = env.keys().map(|v| v.as_str()).collect::<Vec<_>>();
        // let vars = &["x", "res"];
        for v in vars {
            intervals += &format!("{}: {:?}\\n", v, state_map[&edge.id()].get_bounds(man, env, v));
        }

        let abs_string = state_map[&edge.id()].to_string(man, env);

        let color = match edge.weight() {
            IREdge::Fallthrough => "black",
            IREdge::Taken => "green",
            IREdge::NotTaken => "red",
        };

        format!("label = \"{}\\n{}\\n{}\" color = {}", *edge.weight(), abs_string, intervals, color)
    };
    let node_getter = |_, _| {
        format!("")
    };

    let dot = Dot::with_attr_getters(
        &cfg.graph,
        &[Config::EdgeNoLabel],
        &edge_getter,
        &node_getter
    );
    format!("{}", dot)
}

pub fn run(cfg: &IntraProcCFG) -> HashMap<EdgeIndex, Abstract> {
    let graph = &cfg.graph;
    let entry = cfg.entry;

    let man = OptPkManager::default();

    let mut free_vars = vec![];

    let mut dfs = Dfs::new(graph, entry);
    while let Some(nx) = dfs.next(graph) {
        let irn = &graph[nx];
        free_vars.append(&mut irn.free_vars());
    }

    let mut free_vars = free_vars.into_iter().map(|v| v.0).collect::<Vec<_>>();
    free_vars.sort();
    free_vars.dedup_by(|a, b| a == b);
    println!("{:?}", free_vars);
    let env = Environment::new(free_vars);

    let mut edge_state_map = HashMap::new();

    for edge in graph.edge_indices() {
        edge_state_map.insert(edge, Abstract::bottom(&man, &env));
    }

    let entry_outs = graph
        .edges_directed(entry, Outgoing)
        .map(|e| e.id())
        .collect::<Vec<_>>();

    for entry_out in &entry_outs {
        edge_state_map.insert(*entry_out, Abstract::top(&man, &env));
    }

    let mut worklist = VecDeque::new();
    worklist.push_back(entry);

    while !worklist.is_empty() {
        let curr_node = worklist.pop_front().unwrap();

        let incoming_states = graph
            .edges_directed(curr_node, Incoming)
            .map(|e| &edge_state_map[&e.id()])
            .collect::<Vec<_>>();



        let mut incoming_state = Abstract::bottom(&man, &env);
        for state in &incoming_states {
            // TODO: add join &[Abstract] to elina?
            incoming_state.join(&man, *state);
        }
        if incoming_states.len() == 0 {
            // Must be an entry node
            incoming_state = Abstract::top(&man, &env);
        }

        // Need to compute outgoing state
        let curr_irnode = graph[curr_node].clone();
        let taken_state = handle_irnode(&man, &env, &curr_irnode, &mut incoming_state);

        let outgoing_edges = graph
            .edges_directed(curr_node, Outgoing)
            // .map(|e| e.id())
            .collect::<Vec<_>>();

        for out_edge in outgoing_edges {
            let edge_kind = *out_edge.weight();
            match edge_kind {
                IREdge::Fallthrough | IREdge::NotTaken => {
                    // edge_state_map[&out_edge.id()] = incoming_state.clone();
                    edge_state_map.insert(out_edge.id(), incoming_state.clone());
                    // if old_state != incoming_state then add to worklist
                    worklist.push_back(out_edge.target());
                }
                IREdge::Taken => {
                    // curr_node must be CBranch and we must have gotten a Some(taken) result state
                    // edge_state_map[&out_edge.id()] = taken_state.unwrap().clone();
                    edge_state_map.insert(out_edge.id(), taken_state.clone().unwrap());
                    // if old_state != taken_state then add to worklist
                    worklist.push_back(out_edge.target());
                }
            }
        }


    }

    println!("{}", graphviz_with_states(cfg, &man, &env, &edge_state_map));

    edge_state_map
}

fn handle_irnode<M: Manager>(man: &M, env: &Environment, ir: &IRNode, state: &mut Abstract) -> Option<Abstract> {
    use IRNode::*;

    // TODO: in Decl/Assn cases check that we are assigning int variable, otherwise skip
    match ir {
        // "true" constraint
        IRTestcase | IRUnreachable | IRSkip | IRBranch =>
            None,
        IRDecl(v, e) => {
            let texpr = int_expr_to_texpr(env, e);
            state.assign(man, env, v.as_str(), &texpr);
            None
        }
        IRAssn(v, e) => {
            let texpr = int_expr_to_texpr(env, e);
            state.assign(man, env, v.as_str(), &texpr);
            None
        }
        IRReturn(e) => {
            // TODO: Handle return better. How?

            None
        }
        IRCBranch(cond) => {
            let hcons = bool_expr_to_hcons(env, cond);
            let mut taken = state.clone();
            taken.meet(man, &hcons);
            state.meet(man, &hcons.not());
            Some(taken)
        }
    }
}

fn bool_expr_to_hcons(env: &Environment, expr: &Expr) -> Hcons {
    use BinOpcode::*;
    use Expr::*;

    match expr {
        IntLit(_) => panic!("IntLit is not a bool_expr. Type-checking should have caught this"),
        BoolLit(true) => Texpr::int(0).lt(Texpr::int(1)).into(),
        BoolLit(false) => Texpr::int(0).lt(Texpr::int(0)).into(),
        Var(_) => panic!("bool variables are unsupported at the moment"),
        Call(_, _) => panic!("calls are unsupported at the moment"),
        BinOp(WithLoc { elem: op, .. }, left, right) => {
            // op must be int * int -> bool
            // or bool * bool -> bool
            match op {
                Lt => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left.lt(texpr_right).into()
                }
                Le => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left.le(texpr_right).into()
                }
                Gt => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left.gt(texpr_right).into()
                }
                Ge => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left.ge(texpr_right).into()
                }
                Eq => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left._eq(texpr_right).into()
                }
                Ne => {
                    let texpr_left = int_expr_to_texpr(env, left);
                    let texpr_right = int_expr_to_texpr(env, right);
                    texpr_left._ne(texpr_right).into()
                }
                And => {
                    let hcons_left = bool_expr_to_hcons(env, left);
                    let hcons_right = bool_expr_to_hcons(env, right);
                    hcons_left.and(hcons_right)
                }
                Or => {
                    let hcons_left = bool_expr_to_hcons(env, left);
                    let hcons_right = bool_expr_to_hcons(env, right);
                    hcons_left.or(hcons_right)
                }
                _ => panic!("arithmetic operator in a bool expr"),
            }
        }
        UnOp(WithLoc { elem: op, .. }, inner) => {
            match op {
                UnOpcode::Not => {
                    let hcons_inner = bool_expr_to_hcons(env, inner);
                    hcons_inner.not()
                }
                _ => panic!("arithmetic unop in a bool expr"),
            }
        }
    }
}

fn int_expr_to_texpr(env: &Environment, expr: &Expr) -> Texpr {
    use BinOpcode::*;
    use Expr::*;

    match expr {
        IntLit(i) => Texpr::int(*i),
        Var(v) => Texpr::var(env, v.as_str()),
        c@Call(_, _) => panic!("conversion of calls to texpr not supported yet {}", c),
        BinOp(WithLoc { elem: op, .. }, left, right) => {
            Texpr::binop(
                int_binop_to_texpr_binop(op),
                int_expr_to_texpr(env, left),
                int_expr_to_texpr(env, right)
            )
        }
        UnOp(WithLoc { elem: op, .. }, inner) => {
            Texpr::unop(
                int_unop_to_texpr_unop(op),
                int_expr_to_texpr(env, inner)
            )
        }
        e =>
            panic!("int_expr_to_texpr: encountered unhandled case (probably unsupported boolean expression): {}", e),
    }
}

fn int_unop_to_texpr_unop(op: &UnOpcode) -> TexprUnop {
    use UnOpcode::*;

    match op {
        Neg => TexprUnop::Neg,
        op => panic!("not a valid texpr unop: {:?}", op),
    }
}

fn int_binop_to_texpr_binop(op: &BinOpcode) -> TexprBinop {
    use BinOpcode::*;

    match op {
        Add => TexprBinop::Add,
        Sub => TexprBinop::Sub,
        Mul => TexprBinop::Mul,
        Div => TexprBinop::Div,
        Mod => TexprBinop::Mod,
        op => panic!("not a valid texpr binop: {:?}", op),
    }
}