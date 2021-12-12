use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

use elina::ast::{Abstract, Environment, Hcons, Interval, Manager, OptPkManager, Texpr, TexprBinop, TexprUnop};
use petgraph::Direction;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{EdgeIndex, EdgeReference, NodeIndex};
use petgraph::prelude::Dfs;
use petgraph::visit::EdgeRef;
use petgraph::Direction::{Incoming, Outgoing};

use crate::ast::{BinOpcode, Loc, Type, Var};
use crate::ast::{LocExpr, Expr, UnOpcode, WithLoc};
use crate::dfa;
use crate::ir::{IREdge, IRNode, IntraProcCFG};
use crate::ir::IRNode::IRReturn;

struct AIGraph<M: Manager>(AbstractInterpretationEnvironment<M>);

impl<M: Manager> dfa::Graph for AIGraph<M> {
    type Node = NodeIndex;
    type Edge = EdgeIndex;

    fn succs(&self, node: Self::Node) -> Vec<Self::Node> {
        self.0.cfg.graph.neighbors_directed(node, Direction::Outgoing).collect()
    }

    fn preds(&self, node: Self::Node) -> Vec<Self::Node> {
        self.0.cfg.graph.neighbors_directed(node, Direction::Incoming).collect()
    }

    fn edge_between(&self, from: Self::Node, to: Self::Node) -> Option<Self::Edge> {
        self.0.cfg.graph.edges_connecting(from, to).next().map(|e| e.id())
    }

    fn entry_nodes(&self) -> HashSet<Self::Node> {
        HashSet::from([self.0.cfg.entry])
    }
}

#[derive(Clone, PartialEq, Eq)]
struct Fact(Abstract);

impl<M: Manager> dfa::Fact<AIGraph<M>> for Fact {
    fn merge<'a>(graph: &AIGraph<M>, facts: impl IntoIterator<Item=&'a Self>) -> Self where Self: 'a {
        let mut res = Abstract::bottom(&graph.0.man, &graph.0.env);

        for fact in facts.into_iter() {
            res.join(&graph.0.man, &fact.0)
        }

        Fact(res)
    }

    fn bottom(graph: &AIGraph<M>) -> Self {
        Fact(Abstract::bottom(&graph.0.man, &graph.0.env))
    }
}



// TODO: to counteract bool_vars causing imprecisions, add (optional) preprocessing step
// that tries to inline all uses of bool vars. needs other static analyses first


// TODO: disconnect from the cfg's internal graph representation
/// This holds necessary information and results of abstract interpretation.
pub struct AbstractInterpretationEnvironment<M: Manager> {
    pub man: M,
    pub env: Environment,
    pub edge_state_map: HashMap<EdgeIndex, Abstract>,
    pub node_state_map: HashMap<NodeIndex, Abstract>,
    // bounds in points of interest, e.g. analyze! calls
    pub saved_states: HashMap<Loc, (Interval, Abstract)>,
    // states for unreachable!
    pub unreachable_states: HashMap<Loc, Abstract>,
    pub cfg: IntraProcCFG,
}

impl<M: Manager> AbstractInterpretationEnvironment<M> {
    pub fn graphviz(&self) -> String {
        let edge_getter = |_, edge: EdgeReference<IREdge>| {
            let mut intervals = "".to_owned();
    
            if !self.edge_state_map[&edge.id()].is_bottom(&self.man) {
                let mut vars = self.env.keys().map(|v| v.as_str()).collect::<Vec<_>>();
                vars.sort();
                let src = self.cfg.graph.edge_endpoints(edge.id()).unwrap().0;
                if let IRReturn(_) = self.cfg.graph[src].elem {
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

pub fn run<M: Default + Manager>(cfg: IntraProcCFG) -> AbstractInterpretationEnvironment<M> {
    let man = M::default();
    let env = env_from_cfg(&cfg);

    let mut res = AbstractInterpretationEnvironment {
        man,
        env,
        edge_state_map: HashMap::new(),
        node_state_map: HashMap::new(),
        saved_states: HashMap::new(),
        unreachable_states: HashMap::new(),
        cfg,
    };

    // TODO: enforce .run() better? maybe make AIE::run() private and keep ai::run() public?
    let res = res.run();

    res
}

impl<M: Manager> AbstractInterpretationEnvironment<M> {

    pub fn get_loc_map(&self) -> HashMap<Loc, NodeIndex> {
        let mut loc_map = HashMap::new();
        for nx in self.cfg.graph.node_indices() {
            let irn = &self.cfg.graph[nx];
            loc_map.insert(irn.loc.clone(), nx);
        }

        loc_map
    }

    /// This function returns a map from each edge to the abstract state at that edge.
    pub fn run(mut self) -> Self {
        let mut saved_states = self.saved_states.clone();
        let mut unreachable_states = self.unreachable_states.clone();
        let mut node_encounters: HashMap<NodeIndex, usize> = HashMap::new();
        for node in self.cfg.graph.node_indices() {
            node_encounters.insert(node, 0);
        }

        let mut dfa_g = AIGraph(self);

        let flow = |node: NodeIndex, fact: Fact, prev_fact: &Fact| {
            let mut curr_state = fact.0;

            *node_encounters.get_mut(&node).unwrap() += 1;
            if node_encounters[&node] > WIDENING_THRESHOLD {
                curr_state = prev_fact.0.widen_copy(&dfa_g.0.man, &curr_state);
            }

            let curr_irnode = dfa_g.0.cfg.graph[node].clone();
            let taken_state = handle_irnode(&dfa_g.0.man, &dfa_g.0.env, &curr_irnode, &mut curr_state, &mut saved_states, &mut unreachable_states);
            (curr_state, taken_state)
        };

        let get_succ_fact = |edge: EdgeIndex, (not_taken, taken): &(Abstract, Option<Abstract>)| {
            let weight = dfa_g.0.cfg.graph.edge_weight(edge).unwrap().clone();
            let out_state = match weight {
                IREdge::Fallthrough | IREdge::NotTaken => not_taken.clone(),
                IREdge::Taken => taken.clone().unwrap(),
            };

            Fact(out_state)
        };

        let (in_flows, edge_flows) = dfa::dfa(
            &dfa_g,
            flow,
            get_succ_fact,
            &Fact(Abstract::top(&dfa_g.0.man, &dfa_g.0.env))
        );

        self = dfa_g.0;
        self.node_state_map = in_flows.into_iter().map(|(k, v)| (k, v.0)).collect();
        self.saved_states = saved_states;
        self.unreachable_states = unreachable_states;
        self.edge_state_map = edge_flows.into_iter().map(|(e, fact)| {
            (e, fact.0)
        }).collect();

        self
    }

}

fn handle_irnode<M: Manager>(
    man: &M,
    env: &Environment,
    ir: &WithLoc<IRNode>,
    state: &mut Abstract,
    saved_states: &mut HashMap<Loc, (Interval, Abstract)>,
    unreachable_states: &mut HashMap<Loc, Abstract>,
) -> Option<Abstract> {
    use IRNode::*;

    // TODO: in Decl/Assn cases check that we are assigning int variable, otherwise skip
    match &**ir {
        // "true" constraint
        IRTestcase | IRSkip | IRBranch => None,
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
            if !v.is_int() {
                // Only handling ints so far
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
        IRUnreachable => {
            unreachable_states.insert(ir.loc, state.clone());
            
            None
        }
        IRCall(name, args) => {
            // TODO: Can ignore calls for now, but they can change state, namely when we pass arrays, which are by-reference
            if &**name == "analyze!" {
                let arg = &args[0];
                let arg_texpr = int_expr_to_texpr(env, arg);
                let bounds = state.get_bounds_texpr(man, &arg_texpr);
                saved_states.insert(args.loc, (bounds, state.clone()));
            }
            if &**name == "assume!" {
                let arg = &args[0];
                let assumption = bool_expr_to_hcons(env, arg);
                state.meet(man, &assumption);
            }
            None
        }
        IRReturn(Some(e)) => {
            // TODO: Handle return better. How?
            // TODO: make this not panic if retty not int. need to track return type of analyzed function
            let v = Var(RETURN_VAR.to_string(), Type::Int);
            handle_irnode(man, env, &WithLoc::new(IRAssn(LocExpr::Var(WithLoc::no_loc(v)), e.clone()), ir.loc), state, saved_states, unreachable_states)
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
