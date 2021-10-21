// TODO: remove Loc everywhere, only add it to testcase! or where needed. Can still use later.
// TODO: or use deref maybe?

use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter, Write};
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

impl<T: Clone + Debug + Display> Display for WithLoc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.elem, f)
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

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for fn_def in &**self {
            Display::fmt(fn_def, f)?;
            f.write_str("\n")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: WithLoc<String>,
    pub params: Vec<Param>,
    pub retty: WithLoc<Type>,
    pub body: WithLoc<Block>,
}

impl Display for FuncDef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // TODO: see if I can refactor this comma separated params creation using the helper function
        let mut params = "".to_owned();
        if let Some((v, t)) = self.params.get(0) {
            params += &format!("{}: {}", v, t);
        }
        for (v, t) in self.params.iter().skip(1) {
            params += &format!(", {}: {}", v, t);
        }

        f.write_str(&format!("fn {}({}) {{\n{}}}", self.name, params, self.body))?;


        Ok(())
    }
}

pub type Param = (WithLoc<Var>, WithLoc<Type>);

#[derive(Debug, Clone)]
pub struct Block(pub Vec<WithLoc<Stmt>>);

impl Deref for Block {
    type Target = Vec<WithLoc<Stmt>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for stmt in &**self {
            Display::fmt(stmt, f)?;
            if stmt.needs_semicolon() {
                f.write_str(";")?;
            }
            f.write_str("\n")?;
        }

        Ok(())
    }
}

// TODO: call statement for functions that return unit

#[derive(Debug, Clone)]
pub enum Stmt {
    // TODO: add optional params to testcase and unreachable, i.e. to name it?
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

impl Stmt {
    fn needs_semicolon(&self) -> bool {
        use Stmt::*;

        match self {
            IfElse { .. } | While { .. } => false,
            _ => true,
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Stmt::*;

        match self {
            Testcase() => f.write_str("testcase!"),
            Unreachable() => f.write_str("unreachable!"),
            Return(e) => f.write_str(&format!("return {}", e)),
            Decl(v, e) => f.write_str(&format!("let {} = {}", v, e)),
            Assn(v, e) => f.write_str(&format!("{} = {}", v, e)),
            IfElse { cond, if_branch, else_branch } => {
                f.write_str(&format!("if {} {{\n{}}} else {{\n{}}}", cond, if_branch, else_branch))
            },
            While { cond, block } => {
                f.write_str(&format!("while {} {{\n{}}}", cond, block))
            },
        }
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

impl Expr {
    // TODO: make free_vars a trait?
    pub fn free_vars(&self) -> HashSet<Var> {
        use Expr::*;

        match self {
            IntLit(_) | BoolLit(_) => HashSet::new(),
            Var(v) => {
                let mut fv = HashSet::new();
                fv.insert(v.elem.clone());
                fv
            },
            Call(_, args) => args
                    .into_iter()
                    .map(|arg| arg.free_vars())
                    .fold(HashSet::new(), |mut acc, fv| {
                        acc.extend(fv);
                        acc
                    }),
            BinOp(_, left, right) => {
                let mut left_fv = left.free_vars();
                let mut right_fv = right.free_vars();
                left_fv.extend(right_fv);

                left_fv
            }
            UnOp(_, inner) => inner.free_vars(),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Expr::*;

        match self {
            IntLit(i) => Display::fmt(i, f),
            BoolLit(b) => Display::fmt(b, f),
            Var(v) => Display::fmt(v, f),
            Call(name, args) => {
                f.write_str(&format!("{}({})", name, sep_string_display(args, ", ")))
            }
            BinOp(op, left, right) => {
                f.write_str(&format!("({} {} {})", left, op, right))
            }
            UnOp(op, inner) => {
                f.write_str(&format!("{}{}", op, inner))
            }
        }
    }
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
    // Actually, no, decided this is also int * int -> bool
    Eq,
    Ne,
}

impl Display for BinOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use BinOpcode::*;

        match self {
            Add => f.write_str("+"),
            Sub => f.write_str("-"),
            Mul => f.write_str("*"),
            Div => f.write_str("/"),
            Mod => f.write_str("%"),
            Lt => f.write_str("<"),
            Le => f.write_str("<="),
            Gt => f.write_str(">"),
            Ge => f.write_str(">="),
            And => f.write_str("&&"),
            Or => f.write_str("||"),
            Eq => f.write_str("=="),
            Ne => f.write_str("!="),
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnOpcode {
    // int -> int
    Neg,

    // bool -> bool
    Not,
}

impl Display for UnOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use UnOpcode::*;

        match self {
            Neg => f.write_str("-"),
            Not => f.write_str("!"),
        }
    }
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Type {
    Int,
    Bool,
    Unit,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Type::*;
        match self {
            Int => f.write_str("int"),
            Bool => f.write_str("bool"),
            Unit => f.write_str("unit"),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Var(pub String);

impl Deref for Var {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
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

pub fn sep_string_display<T: Display>(elems: &Vec<T>, sep: &str) -> String {
    let mut res = "".to_owned();
    if let Some(elem) = elems.get(0) {
        res += &format!("{}", elem);
    }
    for elem in elems.iter().skip(1) {
        res += &format!("{}{}", sep, elem);
    }

    res
}

