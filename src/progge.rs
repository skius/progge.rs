#[macro_use]
extern crate lalrpop_util;

use std::env::args;
use std::fs::read_to_string;
use std::process::exit;

use proggers::ast::*;
use proggers::ir::IntraProcCFG;

use proggers::tc::{FuncTypeContext, TcError, TypeChecker, VariableTypeContext};

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() -> Result<(), TcError> {
    // TODO: Parsing idea. have a stack of hashmaps that store variable's types (akin to
    // de brujin indices), open a new one whenever you open a new scope. if you need to look up
    // a variable's type, you look first in the top hashmap, then go down.

    let config = parse_args();


    let src_file = &config.src_file;

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
        // typechcek the program
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
    if config.do_ai {
        let analyze = IntraProcCFG::from(&**prog.find_funcdef("analyze").unwrap());
        let ai_env = proggers::ai::run(&analyze);
        println!("{}", ai_env.graphviz());
    }

    Ok(())
}

struct Config {
    src_file: String,
    print_cfg: bool,
    print_ast: bool,
    do_tc: bool,
    do_ai: bool,

}

fn parse_args() -> Config {
    let args = args().collect::<Vec<_>>();
    let executable = args[0].clone();

    let mut cfg = Config {
        src_file: String::new(),
        print_cfg: false,
        print_ast: false,
        do_tc: false,
        do_ai: false,
    };

    for arg in args[1..].into_iter() {
        match arg.as_str() {
            "--all" => {
                cfg.print_cfg = true;
                cfg.print_ast = true;
                cfg.do_tc = true;
                cfg.do_ai = true;
            },
            "--cfg" => cfg.print_cfg = true,
            "--typecheck" | "-t" => cfg.do_tc = true,
            "--analyze" | "-a" => cfg.do_ai = true,
            "--ast" => cfg.print_ast = true,
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
        eprintln!("usage: {} <sourcefile> [--all] [--cfg] [--typecheck] [--analyze] [--ast]", executable);
        exit(1);
    }

    // analyze requires typecheck
    if cfg.do_ai && !cfg.do_tc {
        eprintln!(
            "{}: error: --analyze requires --typecheck",
            executable
        );
        exit(1);
    }

    cfg
}

