#[macro_use] extern crate lalrpop_util;

use std::fs::read_to_string;
use std::str::from_utf8_unchecked;
use proggers::ast::*;

lalrpop_mod!(pub progge); // synthesized by LALRPOP

fn main() {
    let src = read_to_string("example.progge").unwrap();
    let prog: WithLoc<Program> = progge::ProgramLParser::new().parse(&src, &src).unwrap();

    dbg!(&prog);
}