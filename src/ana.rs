use std::collections::HashMap;
use std::sync::Arc;
use ariadne::{Color, Fmt, Label, Report, Source};
use elina::ast::{Manager, OptPkManager, Abstract};
use petgraph::graph::NodeIndex;
use crate::ai::AbstractInterpretationEnvironment;
use crate::ast::*;
use crate::ir::IntraProcCFG;
use crate::se::{bound_loops, fill_model, Model, string_of_model, SymbolicExecutor};

pub struct Analyzer {
    verbose: bool,
    prog: Program,
    src_file: String,
    src_content: String,
    analyzed_fn: String,
    symex: Option<Arc<SymbolicExecutor>>,
    ai: Option<(AbstractInterpretationEnvironment<OptPkManager>, HashMap<Loc, NodeIndex>)>,
}

impl Analyzer {
    pub fn new(verbose: bool, prog: Program, src_file: String, src_content: String, analyzed_fn: impl ToString) -> Self {
        Analyzer {
            verbose,
            prog,
            src_file,
            src_content,
            analyzed_fn: analyzed_fn.to_string(),
            symex: None,
            ai: None,
        }
    }

    pub fn run_symex(&mut self) {
        let (unrolled, did_bound) = bound_loops(&self.prog);
        self.symex = Some(crate::se::run_symbolic_execution(unrolled));
    }

    pub fn run_ai(&mut self, cfg: IntraProcCFG) {
        let ai = crate::ai::run(cfg);
        let loc_map = ai.get_loc_map();
        self.ai = Some((ai, loc_map));
    }

    pub fn analyze(&self) {
        if let Some((ai, _)) = &self.ai {
            println!("{}", ai.graphviz());
        }
        self.analyze_func(self.prog.find_funcdef(&self.analyzed_fn).unwrap());
    }

    fn analyze_func(&self, f: &WithLoc<FuncDef>) {
        self.analyze_block(&f.body);
    }

    fn analyze_block(&self, b: &WithLoc<Block>) {
        for stmt in &b.elem.0 {
            self.analyze_stmt(stmt);
        }
    }

    fn analyze_stmt(&self, s: &WithLoc<Stmt>) {
        use Stmt::*;

        let src_file = &self.src_file;
        let src = &self.src_content;
        let loc = &s.loc;

        match &s.elem {
            Testcase() => {
                // Warning, recommend unreachable! directive instead
                if self.is_unreachable(&s.loc) {
                    // TODO: factor out "expression is unreachable" warning
                    Report::build(ariadne::ReportKind::Warning, src_file, loc.start)
                        .with_label(
                            Label::new(
                                (src_file, loc.range())
                            )
                                .with_message("statement is unreachable")
                                .with_color(Color::Yellow)
                        )
                        .with_note(
                            format!("if this is intentional, consider using {} instead", "unreachable!".fg(Color::Yellow))
                        )
                        .finish()
                        .print((src_file, Source::from(src.clone())))
                        .unwrap();
                    return;
                }


                // Print testcases reaching this line, if any
                if let Some(symex) = &self.symex {
                    // TODO: factor out this analyze_params stuff
                    let analyze_params = self.prog.find_funcdef(&self.analyzed_fn).unwrap().params.iter().map(|p| &p.0.elem);
                    let analyze_params_set = analyze_params.clone().cloned().collect();

                    let mut models = symex.testcases.lock().unwrap().get(loc).cloned().unwrap_or(vec![]);
                    if models.len() > 0 {
                        // There were some testcases, i.e. a proof of reachability
                        println!("-----------------------");
                        println!("{}:{}:{}: sample inputs reaching this statement:", src_file, loc.line, loc.col);
                        models.dedup();
                        for model in &mut models {
                            fill_model(model, &analyze_params_set);
                            let model_string = string_of_model(model, analyze_params.clone());
                            println!("{}", model_string);
                        }
                        println!("-----------------------");
                        return;
                    }
                }



                // Otherwise, we have no proof of unreachability or reachability, so for all we know
                // this line could be either.
                // TODO Advice about no information
                Report::build(ariadne::ReportKind::Advice, src_file, loc.start)
                    .with_label(
                        Label::new(
                            (src_file, loc.range())
                        )
                            .with_message(
                                format!(
                                    "no testcases found - statement may be reachable or unreachable",
                                )
                            )
                            .with_color(Color::Cyan)
                    )
                    .finish()
                    .print((src_file, Source::from(src.clone())))
                    .unwrap();
            }
            Call(name, args) => {
                // For built-ins like analyze!()
                // println!("Analyzing {}", name);
                if name.as_str() == "analyze!" {
                    if let Some((ai, _)) = &self.ai {
                        if let Some((bound, state)) = ai.saved_states.get(&args.loc) {
                            if bound.0 > bound.1 {
                                // Unreachable
                                Report::build(ariadne::ReportKind::Warning, src_file, loc.start)
                                    .with_label(
                                        Label::new(
                                            (src_file, loc.range())
                                        )
                                            .with_message("expression is unreachable")
                                            .with_color(Color::Yellow)
                                    )
                                    .with_note(
                                        format!("if this is intentional, consider using {} instead", "unreachable!".fg(Color::Yellow))
                                    )
                                    .finish()
                                    .print((src_file, Source::from(src.clone())))
                                    .unwrap();
                            } else {
                                Report::build(ariadne::ReportKind::Advice, src_file, loc.start)
                                    .with_label(
                                        Label::new(
                                            (src_file, loc.range())
                                        )
                                            .with_message(
                                                format!(
                                                    "expression may assume at most the values {} - state is {}",
                                                    format!("{:?}", bound).fg(Color::Cyan),
                                                    format!("{}", state.to_string(&ai.man, &ai.env)).fg(Color::Cyan),
                                                )
                                            )
                                            .with_color(Color::Cyan)
                                    )
                                    .finish()
                                    .print((src_file, Source::from(src.clone())))
                                    .unwrap();
                            }
                            return;
                        }
                    }
                }
            }
            Unreachable() => {
                // Check if it's provably unreachable, if so, good, continue!
                if self.is_unreachable(&s.loc) {
                    return;
                }

                // Otherwise, if it's provably reachable, throw error!
                if let Some(mut model) = self.is_reachable(&s.loc) {
                    let analyze_params = self.prog.find_funcdef(&self.analyzed_fn).unwrap().params.iter().map(|p| &p.0.elem);
                    let analyze_params_set = analyze_params.clone().cloned().collect();
                    fill_model(&mut model, &analyze_params_set);
                    let model_string = string_of_model(&model, analyze_params.clone());

                    Report::build(ariadne::ReportKind::Error, src_file, loc.start)
                        .with_label(
                            Label::new(
                                (src_file, loc.range())
                            )
                                .with_message(
                                    format!(
                                        "statement is reachable with the following inputs: {}",
                                        model_string.fg(Color::Red)
                                    )
                                )
                                .with_color(Color::Red)
                        )
                        .finish()
                        .print((src_file, Source::from(src.clone())))
                        .unwrap();
                    return;
                }

                // Otherwise, we have no proof, throw warning with Abstract state if that exists, perhaps
                // TODO: decide if this needs verbose? it seems like an important warning, but maybe too many false positives?
                if self.verbose || true {
                    let mut warning_message = format!("statement may be reachable");
                    if let Some((ai, _)) = &self.ai {
                        if let Some(state) = ai.unreachable_states.get(&s.loc) {
                            warning_message = format!(
                                "statement may be reachable - state is {}",
                                state.to_string(&ai.man, &ai.env).fg(Color::Cyan)
                            )
                        }
                    }
                    Report::build(ariadne::ReportKind::Warning, src_file, loc.start)
                        .with_label(
                            Label::new(
                                (src_file, loc.range())
                            )
                                .with_message(warning_message)
                                .with_color(Color::Yellow)
                        )
                        .finish()
                        .print((src_file, Source::from(src.clone())))
                        .unwrap();
                }
            }
            IfElse { cond: _cond, if_branch, else_branch } => {
                self.analyze_block(if_branch);
                self.analyze_block(else_branch);
            }
            While { cond: _cond, block } => {
                self.analyze_block(block);
            }
            _ => {}
        }
    }

    fn is_unreachable(&self, loc: &Loc) -> bool {
        // Only abstract interpretation can give unreachability proofs
        if let Some((ai, loc_map)) = &self.ai {
            let node_idx = loc_map.get(loc).unwrap();
            let state = &ai.node_state_map[node_idx];
            return state.is_bottom(&ai.man);
        }

        // No proof possible
        false
    }

    fn is_reachable(&self, loc: &Loc) -> Option<Model> {
        // Only abstract interpretation can give unreachability proofs
        if let Some(se) = &self.symex {
            return se.unreachable_paths.lock().unwrap().get(loc).cloned();
        }

        // No proof possible
        None
    }
}