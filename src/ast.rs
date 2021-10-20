// TODO: remove Loc everywhere, only add it to testcase! or where needed. Can still use later.
// TODO: or use deref maybe?

use std::fmt::Debug;
use std::ops::Deref;

#[derive(Debug, Clone)]
pub struct WithLoc<T: Debug + Clone> {
    pub elem: T,
    pub loc: Loc,
}

impl<T: Debug + Clone> Deref for WithLoc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.elem
    }
}

#[derive(Debug, Clone)]
pub struct Program(pub Vec<WithLoc<FuncDef>>);

impl Deref for Program {
    type Target = Vec<WithLoc<FuncDef>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: WithLoc<String>,
    pub params: Vec<(WithLoc<Var>, WithLoc<Type>)>,
    pub retty: WithLoc<Type>,
    pub body: WithLoc<Block>,
}

#[derive(Debug, Clone)]
pub struct Block(pub Vec<WithLoc<Stmt>>);

impl Deref for Block {
    type Target = Vec<WithLoc<Stmt>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Testcase(),
    Unreachable(),
    Return(WithLoc<Expr>),
    Decl(WithLoc<Var>, WithLoc<Expr>),
    Assn(WithLoc<Var>, WithLoc<Expr>),
    IfElse {
        cond: WithLoc<Expr>,
        if_branch: WithLoc<Block>,
        else_branch: WithLoc<Block>,
    },
    While {
        cond: WithLoc<Expr>,
        block: WithLoc<Block>,
    }
}

// TODO: how to handle Calls? they may be either Bool or Int expressions
// TODO: same for Variables...
// decided: no types in rust representation
#[derive(Debug, Clone)]
pub enum Expr {
    IntLit(i64),
    BoolLit(bool),
    Var(WithLoc<Var>),
    Call(WithLoc<String>, Vec<WithLoc<Expr>>),
    BinOp(WithLoc<BinOpcode>, Box<WithLoc<Expr>>, Box<WithLoc<Expr>>),
    UnOp(WithLoc<UnOpcode>, Box<WithLoc<Expr>>),

    // Int(WithLoc<IntExpr>),
    // Bool(WithLoc<BoolExpr>),
}

#[derive(Debug, Clone)]
pub enum BinOpcode {
    // int * int -> int
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // int * int -> bool
    Lt,
    Le,
    Gt,
    Ge,

    // bool * bool -> bool
    And,
    Or,

    // T * T -> bool
    Eq,
    Ne,
}

#[derive(Debug, Clone)]
pub enum UnOpcode {
    // int -> int
    Neg,

    // bool -> bool
    Not,
}

// #[derive(Debug, Clone)]
// pub enum IntExpr {
//     Lit(WithLoc<i64>),
//     Binop(Box<WithLoc<IntExpr>>),
// }
//
// #[derive(Debug, Clone)]
// pub enum BoolExpr {
//     Lit(bool),
//     Binop(Box<BoolExpr>),
// }

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Bool,
    Unit,
}
#[derive(Debug, Clone)]
pub struct Var(pub String);

impl Deref for Var {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

pub fn loc_from_offset(src: &str, offset: usize) -> Loc {
    let (line, col) = src[0..offset].chars().fold((1, 1), |(line, col), curr_char| {
        if curr_char == '\n' {
            (line + 1, 1)
        } else {
            (line, col + 1)
        }
    });
    Loc {
        line,
        col,
    }
}

