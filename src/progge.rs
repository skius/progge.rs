#[macro_use] extern crate lalrpop_util;

use std::fs::read_to_string;
use std::ops::Deref;
use std::str::from_utf8_unchecked;
use proggers::ast::*;
use proggers::ir::{IntraProcCFG};

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() {
    let src = read_to_string("example.progge").unwrap();
    let prog: WithLoc<Program> = progge::ProgramLParser::new().parse(&src, &src).unwrap();

    dbg!(&prog);
    proggers::ir::do_stuff();

    println!("{}", prog);

    let main: IntraProcCFG = prog[0].deref().into();
    println!("{}", main.graphviz());

    proggers::ai::run(&main);

    // let clean = remove_unnecessary_skips(&x);
    // println!("{}", clean.graphviz());
}