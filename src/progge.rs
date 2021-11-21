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

    let mut analyzer = Analyzer::new(
        config.verbose,
        prog.elem.clone(),
        src_file.clone(),
        src.clone(),
        "analyze"
    );
    let analyze = IntraProcCFG::from(&**prog.find_funcdef("analyze").unwrap());
    if config.do_analyze || config.do_ai {
        analyzer.run_ai(analyze);
    }
    if config.do_analyze || config.do_symex {
        analyzer.run_symex();
    }
    analyzer.analyze();


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
    do_ai: bool,
    do_symex: bool,
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
        do_ai: false,
        do_symex: false,
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
            "--symex" | "-s" => cfg.do_symex = true,
            "--ai" => cfg.do_ai = true,
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

    // ai requires typecheck
    if cfg.do_ai && !cfg.do_tc {
        eprintln!(
            "{}: error: --ai requires --typecheck",
            executable
        );
        exit(1);
    }

    // symex requires typecheck
    if cfg.do_symex && !cfg.do_tc {
        eprintln!(
            "{}: error: --symex requires --typecheck",
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

