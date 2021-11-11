use std::collections::{HashMap, HashSet, VecDeque};

use elina::ast::{Abstract, Environment, Hcons, Interval, Manager, OptPkManager, Texpr, TexprBinop, TexprUnop};
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::Dfs;
use petgraph::visit::EdgeRef;
use petgraph::Direction::{Incoming, Outgoing};

use crate::ast::{BinOpcode, Loc, Type, Var};
use crate::ast::{LocExpr, Expr, UnOpcode, WithLoc};
use crate::ir::{IREdge, IRNode, IntraProcCFG};
use crate::ir::IRNode::IRReturn;

// TODO: to counteract bool_vars causing imprecisions, add (optional) preprocessing step
// that tries to inline all uses of bool vars. needs other static analyses first


// TODO: disconnect from the cfg's internal graph representation
/// This holds necessary information and results of abstract interpretation.
pub struct AbstractInterpretationEnvironment<'a, M: Manager> {
    pub man: M,
    pub env: Environment,
    pub edge_state_map: HashMap<EdgeIndex, Abstract>,
    // bounds in points of interest, e.g. analyze! calls
    pub saved_states: HashMap<Loc, Interval>,
    pub cfg: &'a IntraProcCFG,
}

impl<'a, M: Manager> AbstractInterpretationEnvironment<'a, M> {
    pub fn graphviz(&self) -> String {
        let edge_getter = |_, edge: EdgeReference<IREdge>| {
            let mut intervals = "".to_owned();
    
            if !self.edge_state_map[&edge.id()].is_bottom(&self.man) {
                let mut vars = self.env.keys().map(|v| v.as_str()).collect::<Vec<_>>();
                vars.sort();
                let src = self.cfg.graph.edge_endpoints(edge.id()).unwrap().0;
                if let IRReturn(_) = self.cfg.graph[src] {
                    // ignore
                } else {
                    // if we're not an outgoing edge of a return statement, don't print @RETURN@
                    // which is always index 0
                    vars.remove(0);
                }
                for v in vars {
                    intervals += &format!(
                        "{}: {:?}\\n",
                        v,
                        self.edge_state_map[&edge.id()].get_bounds(&self.man, &self.env, v)
                    );
                }
            }
    
            let abs_string = self.edge_state_map[&edge.id()].to_string(&self.man, &self.env);
    
            let color = match edge.weight() {
                IREdge::Fallthrough => "black",
                IREdge::Taken => "green",
                IREdge::NotTaken => "red",
            };
    
            format!(
                "label = \"{}\\n{}\\n{}\" color = {}",
                *edge.weight(),
                abs_string,
                intervals,
                color
            )
        };
        let node_getter = |_, _| format!("");
    
        let dot = Dot::with_attr_getters(
            &self.cfg.graph,
            &[Config::EdgeNoLabel],
            &edge_getter,
            &node_getter,
        );
        format!("{}", dot)
    }
}

// pub fn graphviz_with_states<M: Manager>(
//     cfg: &IntraProcCFG,
//     man: &M,
//     env: &Environment,
//     state_map: &HashMap<EdgeIndex, Abstract>,
// ) -> String {
//     let edge_getter = |_, edge: EdgeReference<IREdge>| {
//         let mut intervals = "".to_owned();

//         if !state_map[&edge.id()].is_bottom(man) {
//             let mut vars = env.keys().map(|v| v.as_str()).collect::<Vec<_>>();
//             vars.sort();
//             for v in vars {
//                 intervals += &format!(
//                     "{}: {:?}\\n",
//                     v,
//                     state_map[&edge.id()].get_bounds(man, env, v)
//                 );
//             }
//         }

//         let abs_string = state_map[&edge.id()].to_string(man, env);

//         let color = match edge.weight() {
//             IREdge::Fallthrough => "black",
//             IREdge::Taken => "green",
//             IREdge::NotTaken => "red",
//         };

//         format!(
//             "label = \"{}\\n{}\\n{}\" color = {}",
//             *edge.weight(),
//             abs_string,
//             intervals,
//             color
//         )
//     };
//     let node_getter = |_, _| format!("");

//     let dot = Dot::with_attr_getters(
//         &cfg.graph,
//         &[Config::EdgeNoLabel],
//         &edge_getter,
//         &node_getter,
//     );
//     format!("{}", dot)
// }

pub static RETURN_VAR: &'static str = "@RETURN@";

fn env_from_cfg(cfg: &IntraProcCFG) -> Environment {
    let graph = &cfg.graph;
    let entry = cfg.entry;

    let mut free_vars = HashSet::new();

    let mut dfs = Dfs::new(graph, entry);
    while let Some(nx) = dfs.next(graph) {
        let irn = &graph[nx];
        free_vars.extend(irn.free_vars());
    }

    let mut free_vars = free_vars
        .into_iter()
        .filter(|v| v.is_int())
        .map(|v| v.0)
        .collect::<Vec<_>>();
    free_vars.sort();
    free_vars.push(RETURN_VAR.to_string());
    Environment::new(free_vars)
}

static WIDENING_THRESHOLD: usize = 100;

pub fn run(cfg: &IntraProcCFG) -> AbstractInterpretationEnvironment<impl Manager> {
    let man = OptPkManager::default();
    let env = env_from_cfg(cfg);

    let edge_state_map = HashMap::new();
    let saved_states: HashMap<Loc, Interval> = HashMap::new();
    
    let mut res = AbstractInterpretationEnvironment {
        man: man,
        env,
        edge_state_map: edge_state_map,
        saved_states: saved_states,
        cfg
    };

    // TODO: enforce .run() better? maybe make AIE::run() private and keep ai::run() public?
    res.run();

    res
}

impl<'a, M: Manager> AbstractInterpretationEnvironment<'a, M> {
    
    /// This function returns a map from each edge to the abstract state at that edge.
    pub fn run(&mut self) {
        let entry = self.cfg.entry;
        let man = &self.man;
        let env = &self.env;

        let mut prev_state_of_nodes: HashMap<NodeIndex, Abstract> = HashMap::new();
        let mut node_encounters: HashMap<NodeIndex, usize> = HashMap::new();

        for edge in self.cfg.graph.edge_indices() {
            self.edge_state_map.insert(edge, Abstract::bottom(man, env));
        }
        for node in self.cfg.graph.node_indices() {
            prev_state_of_nodes.insert(node, Abstract::bottom(man, env));
            node_encounters.insert(node, 0);
        }

        // let entry_outs = self.cfg.graph
        //     .edges_directed(entry, Outgoing)
        //     .map(|e| e.id())
        //     .collect::<Vec<_>>();

        // for entry_out in &entry_outs {
        //     self.edge_state_map.insert(*entry_out, Abstract::top(man, env));
        // }

        prev_state_of_nodes.insert(entry, Abstract::top(man, env));

        let mut worklist = VecDeque::new();
        worklist.push_back(entry);

        while !worklist.is_empty() {
            let curr_node = worklist.pop_front().unwrap();

            let incoming_states = self.cfg.graph
                .edges_directed(curr_node, Incoming)
                .map(|e| &self.edge_state_map[&e.id()])
                .collect::<Vec<_>>();

            let prev_state = &prev_state_of_nodes[&curr_node];

            let mut curr_state = if curr_node == entry {
                Abstract::top(man, env)
            } else {
                let mut curr_state = Abstract::bottom(man, env);
                for state in &incoming_states {
                    // TODO: add join &[Abstract] to elina?
                    curr_state.join(man, *state);
                }
                curr_state
            };

            // // Check widening (of course only if we've ever actually done something
            // if prev_state == &curr_state && node_encounters[&curr_node] > 0 {
            //     // nothing to do, continue
            //     continue;
            // }
            // prev_state != curr_state
            *node_encounters.get_mut(&curr_node).unwrap() += 1;
            if node_encounters[&curr_node] > WIDENING_THRESHOLD {
                // println!(
                //     "\n--------\nWIDENING: prev{} and curr{}",
                //     prev_state.to_string(man, env),
                //     curr_state.to_string(man, env)
                // );
                curr_state = prev_state.widen_copy(man, &curr_state);
                // println!("WIDENED INTO: {}", curr_state.to_string(man, env));
            }
            prev_state_of_nodes.insert(curr_node, curr_state.clone());

            // Need to compute outgoing state
            let curr_irnode = self.cfg.graph[curr_node].clone();
            let taken_state = handle_irnode(man, env, &curr_irnode, &mut curr_state, &mut self.saved_states);

            let outgoing_edges = self.cfg.graph
                .edges_directed(curr_node, Outgoing)
                // .map(|e| e.id())
                .collect::<Vec<_>>();

            for out_edge in outgoing_edges {
                let edge_kind = *out_edge.weight();
                let out_state = match edge_kind {
                    IREdge::Fallthrough | IREdge::NotTaken => curr_state.clone(),
                    IREdge::Taken => {
                        // curr_node must be CBranch and we must have gotten a Some(taken) result state
                        taken_state.clone().unwrap()
                    }
                };

                // println!(
                //     "\n-----\nHandling Edge\nold out edge state: {}",
                //     self.edge_state_map[&out_edge.id()].to_string(man, env)
                // );
                // println!("new out_state: {}", out_state.to_string(man, env));

                if self.edge_state_map[&out_edge.id()] == out_state && node_encounters[&out_edge.target()] != 0 {
                    // we are not causing a change in succ
                    // (note that we want to visit the succ at least once, hence node_encounters != 0)
                    continue;
                }
                self.edge_state_map.insert(out_edge.id(), out_state);
                // if old_state != taken_state then add to worklist
                worklist.push_back(out_edge.target());
            }
        }

    }

}

fn handle_irnode(
    man: &impl Manager,
    env: &Environment,
    ir: &IRNode,
    state: &mut Abstract,
    saved_states: &mut HashMap<Loc, Interval>,
) -> Option<Abstract> {
    use IRNode::*;

    // TODO: in Decl/Assn cases check that we are assigning int variable, otherwise skip
    match ir {
        // "true" constraint
        IRTestcase | IRUnreachable | IRSkip | IRBranch => None,
        IRDecl(v, e) => {
            if !v.is_int() {
                // Only handling ints so far
                // TODO: adjust for arrays
                return None;
            }

            let texpr = int_expr_to_texpr(env, e);
            state.assign(man, env, v.as_str(), &texpr);
            None
        }
        IRAssn(LocExpr::Var(v), e) => {
            if v.is_bool() {
                // Not handling boolean variables
                return None;
            }

            let texpr = int_expr_to_texpr(env, e);
            state.assign(man, env, v.as_str(), &texpr);
            None
        }
        IRAssn(LocExpr::Index(_, _), _) => {
            // TODO: handle arrays in AI
            None
        }
        IRCall(name, args) => {
            // Can ignore calls for now, but they can change state, namely when we pass arrays, which are by-reference
            // TODO: Also need to handle special functions like analyze!
            if &**name == "analyze!" {
                let arg = &args[0];
                let arg_texpr = int_expr_to_texpr(env, arg);
                let bounds = state.get_bounds_texpr(man, &arg_texpr);
                saved_states.insert(args.loc, bounds);
            }
            None
        }
        IRReturn(Some(e)) => {
            // TODO: Handle return better. How?
            // TODO: make this not panic if retty not int. need to track return type of analyzed function
            let v = Var(RETURN_VAR.to_string(), Type::Int);
            handle_irnode(man, env, &IRAssn(LocExpr::Var(WithLoc::no_loc(v)), e.clone()), state, saved_states)
        }
        IRReturn(None) => {
            // unhandled
            None
        }
        IRCBranch(cond) => {
            // We don't analyze boolean variables currently, so we overapproximate
            // if cond.contains_bool_var() {
            //     let taken = state.clone();
            //     return Some(taken);
            // }
            // Handling this now via Hcons::Top

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
        // Var(_) => panic!("bool variables are unsupported at the moment"),
        Var(_) => Hcons::Top,
        // TODO: make call just go to top by default, and maybe a second run where it utilizes
        // a previous run's AI results.
        // Call(_, _) => panic!("calls are unsupported at the moment"),
        Call(_, _) => Hcons::Top,
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
        UnOp(WithLoc { elem: op, .. }, inner) => match op {
            UnOpcode::Not => {
                let hcons_inner = bool_expr_to_hcons(env, inner);
                hcons_inner.not()
            }
            _ => panic!("arithmetic unop in a bool expr"),
        },
        Index(_, _) => Hcons::Top,
        e => panic!("unsupported expr: {:?}", e),
    }
}

fn int_expr_to_texpr(env: &Environment, expr: &Expr) -> Texpr {
    use Expr::*;

    match expr {
        IntLit(i) => Texpr::int(*i),
        Var(v) => Texpr::var(env, v.as_str()),
        // c@Call(_, _) => panic!("conversion of calls to texpr not supported yet {}", c),
        Call(_, _) => Texpr::top(),
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
        Index(_, _) => Texpr::top(),
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
