#[macro_use] extern crate lalrpop_util;

use std::fs::read_to_string;
use std::ops::Deref;
use std::str::from_utf8_unchecked;
use proggers::ast::*;
use proggers::ir::{IntraProcCFG};

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() {
    // TODO: Parsing idea. have a stack of hashmaps that store variable's types (akin to
    // de brujin indices), open a new one whenever you open a new scope. if you need to look up
    // a variable's type, you look first in the top hashmap, then go down.

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