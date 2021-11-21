#[macro_use]
extern crate lalrpop_util;

use std::collections::HashSet;
use std::env::args;
use std::fs::read_to_string;
use std::process::exit;
use ariadne::{Color, Fmt, Label, Report, Source};

use proggers::*;
use proggers::ana::Analyzer;
use proggers::ast::*;
use proggers::ir::IntraProcCFG;
use proggers::se::{bound_loops, fill_model, run_symbolic_execution, string_of_model};

use proggers::tc::{FuncTypeContext, TcError, TypeChecker, VariableTypeContext};

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() -> Result<(), TcError> {
    let config = parse_args();

    let src_file = &config.src_file;
    // .replace bugfix for ariadne's CRLF bug
    let src = read_to_string(src_file).expect(&format!("couldn't read file {}", src_file)).replace("\r\n", "\n");
    let mut tctx = VariableTypeContext::new();
    let mut prog: WithLoc<Program> = progge::ProgramLParser::new()
        .parse(src_file, &src, &mut tctx, &src)
        .unwrap();

    if config.print_cfg {
        let analyze = IntraProcCFG::from(&**prog.find_funcdef("analyze").unwrap());
        println!("{}", analyze.graphviz());
    }
    if config.do_tc {
        // typecheck the program
        let mut tc = TypeChecker::new(FuncTypeContext::from(&*prog), src_file, src.clone());
        let res = tc.tc_prog(&mut prog);
        if let Err(err) = res {
            eprintln!("Error while type-checking {}:", src_file);
            err.print_error_message(src_file);
            exit(1);
        } else {
            println!("Successfully type-checked \"{}\".", src_file)
        }
    }
    if config.print_ast {
        println!("{}", prog);
    }
    if config.do_analyze {

        let analyze = IntraProcCFG::from(&**prog.find_funcdef("analyze").unwrap());

        let mut analyzer = Analyzer::new(config.verbose, prog.elem.clone(), src_file.clone(), src.clone(), "analyze");
        analyzer.run_ai(analyze);
        analyzer.run_symex();
        analyzer.analyze();


        // let mut saved_states_keys = ai_env.saved_states.keys().collect::<Vec<_>>();
        //
        // saved_states_keys.sort_by_key(|l| l.start);
        // for loc in saved_states_keys {
        //     let (bound, state) = &ai_env.saved_states[loc];
        //     if bound.0 > bound.1 {
        //         // Unreachable
        //         Report::build(ariadne::ReportKind::Warning, src_file, loc.start)
        //             .with_label(
        //                 Label::new(
        //                     (src_file, loc.range())
        //                 )
        //                     .with_message("expression is unreachable")
        //                     .with_color(Color::Yellow)
        //             )
        //             .with_note(
        //                 format!("if this is intentional, consider using {} instead", "unreachable!".fg(Color::Yellow))
        //             )
        //             .finish()
        //             .print((src_file, Source::from(src.clone())))
        //             .unwrap();
        //     } else {
        //         Report::build(ariadne::ReportKind::Advice, src_file, loc.start)
        //             .with_label(
        //                 Label::new(
        //                     (src_file, loc.range())
        //                 )
        //                     .with_message(
        //                         format!(
        //                             "expression may assume at most the values {} - state is {}",
        //                             format!("{:?}", bound).fg(Color::Cyan),
        //                             format!("{}", state.to_string(&ai_env.man, &ai_env.env)).fg(Color::Cyan),
        //                         )
        //                     )
        //                     .with_color(Color::Cyan)
        //             )
        //             .finish()
        //             .print((src_file, Source::from(src.clone())))
        //             .unwrap();
        //     }
        // }

        // let mut unreachable_states_keys = ai_env.unreachable_states.keys().collect::<Vec<_>>();
        // unreachable_states_keys.sort_by_key(|l| l.start);
        // for loc in unreachable_states_keys {
        //     // TxODO: once symbolic execution is added, add possible cases that reach this statement
        //     let state = &ai_env.unreachable_states[loc];
        //     if !state.is_bottom(&ai_env.man) {
        //         Report::build(ariadne::ReportKind::Warning, src_file, loc.start)
        //             .with_label(
        //                 Label::new(
        //                     (src_file, loc.range())
        //                 )
        //                     .with_message(
        //                         format!(
        //                             "statement may be reachable - state is {}",
        //                             state.to_string(&ai_env.man, &ai_env.env).fg(Color::Cyan)
        //                         )
        //                     )
        //                     .with_color(Color::Yellow)
        //             )
        //             .finish()
        //             .print((src_file, Source::from(src.clone())))
        //             .unwrap();
        //     }
        // }


        // TxODO: combine symex + AI results -- done in analyzer
        // let (unrolled, did_bound) = bound_loops(&*prog);
        // // if did_bound is true, then any statements about unreachability are in fact guarantees.
        // // println!("{}", unrolled);
        // let mut symex = run_symbolic_execution(unrolled.clone());
        // // the symbolix variables
        // let analyze_params = unrolled.find_funcdef("analyze").unwrap().params.iter().map(|(v, _)| &v.elem);
        // let analyze_params_set = analyze_params.clone().cloned().collect();
        // Guaranteed reachable, i.e. provably incorrect
        // let mut unreachable_paths_keys = symex.unreachable_paths.keys().cloned().collect::<Vec<_>>();
        // unreachable_paths_keys.sort_by_key(|l| l.start);
        // for loc in &unreachable_paths_keys {
        //     let model = symex.unreachable_paths.get_mut(loc).unwrap();
        //     fill_model(model, &analyze_params_set);
        //     let model_string = string_of_model(model, analyze_params.clone());
        //     Report::build(ariadne::ReportKind::Error, src_file, loc.start)
        //         .with_label(
        //             Label::new(
        //                 (src_file, loc.range())
        //             )
        //                 .with_message(
        //                     format!(
        //                         "statement is reachable with the following inputs: {}",
        //                         model_string.fg(Color::Red)
        //                     )
        //                 )
        //                 .with_color(Color::Red)
        //         )
        //         .finish()
        //         .print((src_file, Source::from(src.clone())))
        //         .unwrap();
        // }

        // let mut testcases_keys = symex.testcases.keys().cloned().collect::<Vec<_>>();
        // testcases_keys.sort_by_key(|l| l.start);
        // for loc in &testcases_keys {
        //     let models = symex.testcases.get_mut(loc).unwrap();
        //     println!("-----------------------");
        //     println!("{}:{}:{}: sample inputs reaching this statement:", src_file, loc.line, loc.col);
        //     models.dedup();
        //     for model in models {
        //         fill_model(model, &analyze_params_set);
        //         let model_string = string_of_model(model, analyze_params.clone());
        //         println!("{}", model_string);
        //     }
        // }
    }
    if let Some(output) = config.compile_target {
        proggers::compiler::compile(prog.clone().elem, &output, config.verbose);
    }

    Ok(())
}

struct Config {
    src_file: String,
    print_cfg: bool,
    print_ast: bool,
    do_tc: bool,
    do_analyze: bool,
    compile_target: Option<String>,
    verbose: bool,
}

fn parse_args() -> Config {
    let args = args().collect::<Vec<_>>();
    let executable = args[0].clone();

    let mut cfg = Config {
        src_file: String::new(),
        print_cfg: false,
        print_ast: false,
        do_tc: false,
        do_analyze: false,
        compile_target: None,
        verbose: false,
    };


    let mut got_operand = false;
    for (i, arg) in args[1..].iter().enumerate() {
        // we are skipping first element, so add it back
        let i = i + 1;
        if got_operand {
            got_operand = false;
            continue;
        }
        match arg.as_str() {
            "--all" => {
                cfg.print_cfg = true;
                cfg.print_ast = true;
                cfg.do_tc = true;
                cfg.do_analyze = true;
            },
            "--cfg" => cfg.print_cfg = true,
            "--typecheck" | "-t" => cfg.do_tc = true,
            "--analyze" | "-a" => cfg.do_analyze = true,
            "--ast" => cfg.print_ast = true,
            "--verbose" | "-v" => cfg.verbose = true,
            "--output" | "-o" => {
                if i + 1 >= args.len() || args[i + 1].starts_with("-") {
                    eprintln!("{}: error: missing argument to `{}`", executable, arg);
                    exit(1);
                }
                cfg.compile_target = Some(args[i + 1].clone());
                got_operand = true;
            },
            _ => {
                if cfg.src_file.is_empty() && !arg.starts_with("-") {
                    cfg.src_file = arg.clone();
                } else {
                    eprintln!("{}: error: unrecognized argument: {}", executable, arg);
                    exit(1);
                }
            }
        };
    }

    // if no sourcefile, print usage and exit
    if cfg.src_file.is_empty() {
        eprintln!("{}: error: no source file specified", executable);
        eprintln!("usage: {} <sourcefile> [--all] [--cfg] [--typecheck] [--analyze] [--ast] [-o <compilation output>]", executable);
        exit(1);
    }

    // analyze requires typecheck
    if cfg.do_analyze && !cfg.do_tc {
        eprintln!(
            "{}: error: --analyze requires --typecheck",
            executable
        );
        exit(1);
    }

    // compilation requires typecheck
    if cfg.compile_target.is_some() && !cfg.do_tc {
        eprintln!(
            "{}: error: --output requires --typecheck",
            executable
        );
        exit(1);
    }

    cfg
}

