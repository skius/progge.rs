#[macro_use] extern crate lalrpop_util;

use std::fs::read_to_string;

use proggers::ast::*;
use proggers::ir::IntraProcCFG;
use proggers::tc::{FuncTypeContext, TcError, TypeChecker, VariableTypeContext};

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() -> Result<(), TcError> {
    // TODO: Parsing idea. have a stack of hashmaps that store variable's types (akin to
    // de brujin indices), open a new one whenever you open a new scope. if you need to look up
    // a variable's type, you look first in the top hashmap, then go down.

    let src = read_to_string("example.progge").unwrap();
    let mut tctx = VariableTypeContext::new();
    let prog: WithLoc<Program> = progge::ProgramLParser::new().parse("example.progge", &src, &mut tctx, &src).unwrap();

    // dbg!(&prog);

    println!("{}", prog);

    // let main: IntraProcCFG = prog[0].deref().into();
    // println!("{}", main.graphviz());

    // proggers::ai::run(&main);

    let mut tc = TypeChecker::new(FuncTypeContext::from(&*prog), "example.progge");
    let res = tc.tc_prog(&prog);
    if let Err(err) = res {
        err.print_error_message("example.progge");
    }

    // let clean = remove_unnecessary_skips(&x);
    // println!("{}", clean.graphviz());

    Ok(())
}