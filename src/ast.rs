use std::borrow::Borrow;
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

// TODO: change to loc_pre and loc_post, so we can use loc_post to say when something's missing,
// e.g. when there's a missing explicit return
#[derive(Debug, Clone)]
pub struct WithLoc<T: Debug + Clone> {
    pub elem: T,
    pub loc: Loc,
    pub typ: Type,
}

impl<T: Debug + Clone> WithLoc<T> {
    pub fn no_loc(elem: T) -> Self {
        WithLoc {
            elem,
            loc: Loc {
                line: 0,
                col: 0,
                start: 0,
                end: 0,
            },
            typ: Type::Unknown,
        }
    }

    pub fn new(elem: T, loc: Loc) -> Self {
        WithLoc { elem, loc, typ: Type::Unknown }
    }

    // different name than "set_type" to avoid clashing with self.deref().set_type()
    pub fn set_type_loc(&mut self, t: &Type) {
        self.typ = t.clone();
    }
}

impl<T: Debug + Clone> Deref for WithLoc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.elem
    }
}

impl<T: Debug + Clone> DerefMut for WithLoc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.elem
    }
}

impl<T: Debug + Clone> Borrow<T> for WithLoc<T> {
    fn borrow(&self) -> &T {
        &*self
    }
}

impl<T: Clone + Debug + Display> Display for WithLoc<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.elem, f)
    }
}

impl<T: PartialEq + Clone + Debug> PartialEq for WithLoc<T> {
    fn eq(&self, other: &Self) -> bool {
        self.elem == other.elem
    }
}

impl<T: PartialEq + Clone + Debug> Eq for WithLoc<T> {}

impl<T: Hash + Clone + Debug> Hash for WithLoc<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.elem.hash(state);
    }
}

#[derive(Debug, Clone)]
pub struct Program(pub Vec<WithLoc<FuncDef>>);

impl Program {
    pub fn find_funcdef(&self, name: &str) -> Option<&WithLoc<FuncDef>> {
        for funcdef in &self.0 {
            if funcdef.name.elem == name {
                return Some(funcdef);
            }
        }
        None
    }
}

impl Deref for Program {
    type Target = Vec<WithLoc<FuncDef>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Program {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for fn_def in &**self {
            Display::fmt(fn_def, f)?;
            f.write_str("\n\n")?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub name: WithLoc<String>,
    pub params: WithLoc<Vec<Param>>,
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

impl DerefMut for Block {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
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

#[derive(Debug, Clone)]
pub enum Stmt {
    // TODO: add optional params to testcase and unreachable, i.e. to name it?
    Testcase(),
    Unreachable(),
    Return(Option<WithLoc<Expr>>),
    Decl(WithLoc<Var>, WithLoc<Expr>),
    Assn(WithLoc<LocExpr>, WithLoc<Expr>),
    Call(WithLoc<String>, WithLoc<Vec<WithLoc<Expr>>>),
    IfElse {
        cond: WithLoc<Expr>,
        if_branch: WithLoc<Block>,
        else_branch: WithLoc<Block>,
    },
    While {
        cond: WithLoc<Expr>,
        block: WithLoc<Block>,
    },
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
            Return(Some(e)) => f.write_str(&format!("return {}", e)),
            Return(None) => f.write_str(&format!("return")),
            Decl(v, e) => f.write_str(&format!("let {} = {}", v, e)),
            Assn(v, e) => f.write_str(&format!("{} = {}", v, e)),
            Call(name, args) => {
                f.write_str(&format!("{}({})", name, sep_string_display(args, ", ")))
            }
            IfElse {
                cond,
                if_branch,
                else_branch,
            } => f.write_str(&format!(
                "if {} {{\n{}}} else {{\n{}}}",
                cond, if_branch, else_branch
            )),
            While { cond, block } => f.write_str(&format!("while {} {{\n{}}}", cond, block)),
        }
    }
}

// this represents an "lvalue", i.e. whatever can be assigned to
#[derive(Debug, Clone)]
pub enum LocExpr {
    Var(WithLoc<Var>),
    Index(WithLoc<Expr>, WithLoc<Expr>),
}

impl LocExpr {
    pub fn free_vars(&self) -> HashSet<Var> {
        use LocExpr::*;

        match self {
            Var(v) => {
                let mut fv = HashSet::new();
                fv.insert(v.elem.clone());
                fv
            }
            Index(arr, idx) => {
                let mut fv = arr.free_vars();
                fv.extend(idx.free_vars());
                fv
            }
        }
    }
}

impl Display for LocExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use LocExpr::*;

        match self {
            Var(v) => Display::fmt(v, f),
            // TODO: risky that we're leaving out () around `arr`, but works because currently arr can only be a leaf expr
            Index(arr, idx) => f.write_str(&format!("{}[{}]", arr, idx)),
        }
    }
}


#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Expr {
    IntLit(i64),
    BoolLit(bool),
    Var(WithLoc<Var>),
    Call(WithLoc<String>, WithLoc<Vec<WithLoc<Expr>>>),
    BinOp(WithLoc<BinOpcode>, Box<WithLoc<Expr>>, Box<WithLoc<Expr>>),
    UnOp(WithLoc<UnOpcode>, Box<WithLoc<Expr>>),
    Array(WithLoc<Vec<WithLoc<Expr>>>),
    DefaultArray {
        default_value: Box<WithLoc<Expr>>,
        size: Box<WithLoc<Expr>>,
    },
    Index(Box<WithLoc<Expr>>, Box<WithLoc<Expr>>),
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
            }
            Call(_, args) => {
                args.elem.iter()
                    .map(|arg| arg.free_vars())
                    .fold(HashSet::new(), |mut acc, fv| {
                        acc.extend(fv);
                        acc
                    })
            }
            BinOp(_, left, right) => {
                let mut left_fv = left.free_vars();
                let right_fv = right.free_vars();
                left_fv.extend(right_fv);

                left_fv
            }
            UnOp(_, inner) => inner.free_vars(),
            Array(elems) => elems.elem.iter().fold(HashSet::new(), |mut acc, e| {
                acc.extend(e.free_vars());
                acc
            }),
            Index(arr, idx) => {
                let mut fv = arr.free_vars();
                fv.extend(idx.free_vars());
                fv
            },
            DefaultArray { default_value, size } => {
                let mut fv = size.free_vars();
                fv.extend(default_value.free_vars());
                fv
            },
        }
    }

    pub fn contains_bool_var(&self) -> bool {
        match self {
            Expr::IntLit(_) | Expr::BoolLit(_) => false,
            Expr::Var(v) if v.is_bool() => true,
            Expr::Var(_) => false,
            Expr::Call(_, args) => args.iter().any(|arg| arg.contains_bool_var()),
            Expr::BinOp(_, left, right) => left.contains_bool_var() || right.contains_bool_var(),
            Expr::UnOp(_, inner) => inner.contains_bool_var(),
            Expr::Array(elems) => elems.iter().any(|e| e.contains_bool_var()),
            Expr::Index(arr, idx) => arr.contains_bool_var() || idx.contains_bool_var(),
            Expr::DefaultArray { default_value, size } => {
                default_value.contains_bool_var() || size.contains_bool_var()
            },
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
            BinOp(op, left, right) => f.write_str(&format!("({} {} {})", left, op, right)),
            UnOp(op, inner) => f.write_str(&format!("{}{}", op, inner)),
            Array(elems) => f.write_str(&format!("[{}]", sep_string_display(elems, ", "))),
            // TODO: risky that we're leaving out () around `arr`, but works because currently arr can only be a leaf expr
            Index(arr, idx) => f.write_str(&format!("{}[{}]", arr, idx)),
            DefaultArray { default_value, size } => {
                f.write_str(&format!("[{}; {}]", default_value, size))
            }
        }
    }
}

// #[allow(non_camel_case_types)]
// pub enum OpcodeType {
//     IntInt_Int,
//     IntInt_Bool,
//     BoolBool_Bool,
//     Bool_Bool,
//     Int_Int
// }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpcodeType<P>(pub P, pub Type)
where
    P: Debug + Clone + PartialEq + Eq;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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

impl BinOpcode {
    pub fn get_type(&self) -> OpcodeType<(Type, Type)> {
        use BinOpcode::*;
        use Type::*;

        match self {
            Add | Sub | Mul | Div | Mod => OpcodeType((Int, Int), Int),
            Lt | Le | Gt | Ge | Eq | Ne => OpcodeType((Int, Int), Bool),
            _ => OpcodeType((Bool, Bool), Bool),
        }
    }
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum UnOpcode {
    // int -> int
    Neg,

    // bool -> bool
    Not,
}

impl UnOpcode {
    pub fn get_type(&self) -> OpcodeType<Type> {
        use Type::*;
        use UnOpcode::*;

        match self {
            Neg => OpcodeType(Int, Int),
            Not => OpcodeType(Bool, Bool),
        }
    }
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

#[derive(Debug, Clone, Eq)]
pub enum Type {
    Int,
    Bool,
    Unit,
    Unknown,
    Any,
    Array(Box<WithLoc<Type>>),
}

impl Type {
    pub fn is_unknown(&self) -> bool {
        match self {
            Type::Unknown => true,
            Type::Array(t) => t.is_unknown(),
            _ => false,
        }
    }

    pub fn is_any(&self) -> bool {
        match self {
            Type::Any => true,
            _ => false,
        }
    }
}

// To ignore the "loc" part of the type
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Type::*;
        std::mem::discriminant(self).hash(state);
        match self {
            Array(t) => t.elem.hash(state),
            _ => {}
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        use Type::*;

        match (self, other) {
            (Int, Int) => true,
            (Bool, Bool) => true,
            (Unit, Unit) => true,
            (Unknown, Unknown) => true,
            (Array(t1), Array(t2)) => t1.elem == t2.elem,
            _ => false,
        }
    }
}

// impl Copy for Type {}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Type::*;
        match self {
            Int => f.write_str("int"),
            Bool => f.write_str("bool"),
            Unit => f.write_str("unit"),
            Any => f.write_str("any"),
            Array(inner) => f.write_str(&format!("[{}]", inner)),
            Unknown => f.write_str("_unknown_"),
        }
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Var(pub String, pub Type);

impl Hash for Var {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Var {
    pub fn is_bool(&self) -> bool {
        self.1 == Type::Bool
    }

    pub fn is_int(&self) -> bool {
        self.1 == Type::Int
    }

    pub fn set_type(&mut self, t: &Type) {
        self.1 = t.clone();
    }
}

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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
    pub start: usize,
    pub end: usize,
}

impl Loc {
    pub fn range(&self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

pub fn loc_from_offset(src: &str, start: usize, end: usize) -> Loc {
    let (line, col) = src[0..start]
        .chars()
        .fold((1, 1), |(line, col), curr_char| {
            if curr_char == '\n' {
                (line + 1, 1)
            } else {
                (line, col + 1)
            }
        });
    Loc { line, col, start, end }
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
