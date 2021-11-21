use egg::{*, rewrite as rw};
use crate::ast::{BinOpcode, Expr};

define_language! {
    pub enum Progge {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        // not sure why this is needed, % gets pretty-printed as "%"
        ".mod" = Mod([Id; 2]),
        // "^" = Pow([Id; 2]),
        "==" = Eq([Id; 2]),
        "!=" = Ne([Id; 2]),
        "<=" = Le([Id; 2]),
        "<" = Lt([Id; 2]),
        ">=" = Ge([Id; 2]),
        ">" = Gt([Id; 2]),
        "-" = Neg(Id),

        "&&" = And([Id; 2]),
        "||" = Or([Id; 2]),
        "!" = Not(Id),

        Num(i64),
        Bool(bool),
        Var(Symbol),

        Other(Symbol, Vec<Id>),
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    Number(i64),
    Boolean(bool),
}

impl Value {
    fn num(&self) -> i64 {
        match self {
            Value::Number(n) => *n,
            Value::Boolean(_) => panic!("called num() on bool-Value"),
        }
    }

    fn bool(&self) -> bool {
        match self {
            Value::Number(_) => panic!("called bool() on number-Value"),
            Value::Boolean(b) => *b,
        }
    }
}

#[derive(Default)]
struct ConstantFolding;
impl Analysis<Progge> for ConstantFolding {
    type Data = Option<Value>;

    fn make(egraph: &EGraph<Progge, Self>, enode: &Progge) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            Progge::Num(n) => Some(Value::Number(*n)),
            Progge::Bool(b) => Some(Value::Boolean(*b)),

            Progge::Add([a, b]) => Some(Value::Number(x(a)?.num() + x(b)?.num())),
            Progge::Sub([a, b]) => Some(Value::Number(x(a)?.num() - x(b)?.num())),
            Progge::Mul([a, b]) => Some(Value::Number(x(a)?.num() * x(b)?.num())),
            // TODO: (general) look into whether all the % uses are the same, i.e. remainder vs modulo
            // i.e. Rust's version, Z3's version and ELINA's version
            Progge::Mod([a, b]) => Some(Value::Number(x(a)?.num() % x(b)?.num())),
            Progge::Neg(a) => Some(Value::Number(-x(a)?.num())),

            Progge::Eq([a, b]) => Some(Value::Boolean(x(a)?.num() == x(b)?.num())),
            Progge::Ne([a, b]) => Some(Value::Boolean(x(a)?.num() != x(b)?.num())),
            Progge::Le([a, b]) => Some(Value::Boolean(x(a)?.num() <= x(b)?.num())),
            Progge::Lt([a, b]) => Some(Value::Boolean(x(a)?.num() < x(b)?.num())),
            Progge::Ge([a, b]) => Some(Value::Boolean(x(a)?.num() >= x(b)?.num())),
            Progge::Gt([a, b]) => Some(Value::Boolean(x(a)?.num() > x(b)?.num())),

            Progge::And([a, b]) => Some(Value::Boolean(x(a)?.bool() && x(b)?.bool())),
            Progge::Or([a, b]) => Some(Value::Boolean(x(a)?.bool() || x(b)?.bool())),
            Progge::Not(a) => Some(Value::Boolean(!x(a)?.bool())),
            _ => None,
        }
    }

    fn merge(&self, to: &mut Self::Data, from: Self::Data) -> bool {
        egg::merge_if_different(to, to.or(from))
    }

    /*
    a = 5;
    x = 10;
    return x;

    <=>
    b = 5;
    y = 10;
    return y;

    */

    fn modify(egraph: &mut EGraph<Progge, Self>, id: Id) {
        match egraph[id].data {
            Some(Value::Boolean(b)) => {
                let added = egraph.add(Progge::Bool(b));
                egraph.union(id, added);
            }
            Some(Value::Number(n)) => {
                let added = egraph.add(Progge::Num(n));
                egraph.union(id, added);
            }
            _ => {}
        }
    }
}

pub fn example() {
    let my_expr: RecExpr<Progge> = "(+ 2 (+ z 0))".parse().unwrap();

    let bests = get_bests(vec![&my_expr]);
    println!("Found bests: {}", bests.into_iter().map(|recexpr| recexpr.to_string()).collect::<Vec<_>>().join(", "));


    let dangerous_rw: RecExpr<Progge> = "(= (* 0 2) (* 0 5))".parse().unwrap();

    let bests = get_bests(vec![&dangerous_rw]);
    println!("Found bests: {}", bests.into_iter().map(|recexpr| recexpr.to_string()).collect::<Vec<_>>().join(", "));

}

pub fn get_bests(exprs: Vec<&RecExpr<Progge>>) -> Vec<RecExpr<Progge>> {
    let runner = exprs.into_iter()
        .fold(Runner::default(), |runner, expr| runner.with_expr(expr))
        .run(&rules());
    let mut extractor = Extractor::new(&runner.egraph, AstSize);

    runner.roots.iter().map(|id| extractor.find_best(*id).1).collect()
}

fn rules() -> Vec<Rewrite<Progge, ConstantFolding>> { vec![
    rw!("commute-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
    rw!("commute-mul"; "(* ?x ?y)" => "(* ?y ?x)"),
    rw!("commute-eq"; "(== ?x ?y)" => "(== ?y ?x)"),

    rw!("commute-and"; "(&& ?x ?y)" => "(&& ?y ?x)"),
    rw!("commute-or"; "(|| ?x ?y)" => "(|| ?y ?x)"),

    // rw!("intro-or"; "?x" => "(|| ?x ?y)"), // Not possible currently

    rw!("ass-and"; "(&& (&& ?x ?y) ?z)" => "(&& ?x (&& ?y ?z))"),
    rw!("ass-or"; "(|| (|| ?x ?y) ?z)" => "(|| ?x (|| ?y ?z))"),

    rw!("double-not"; "(! (! ?x))" => "?x"),

    // rw!("trans-eq"; "(&& (= ?x ?y) (= ?y ?z))" => "(= ?x ?z)"), //TODO: dangerous because we "lose" information (in the best expression)

    rw!("neg-lt"; "(! (< ?x ?y))" => "(>= ?x ?y)"),
    rw!("neg-le"; "(! (<= ?x ?y))" => "(> ?x ?y)"),
    rw!("neg-gt"; "(! (> ?x ?y))" => "(<= ?x ?y)"),
    rw!("neg-ge"; "(! (>= ?x ?y))" => "(< ?x ?y)"),
    rw!("neg-eq"; "(! (== ?x ?y))" => "(!= ?x ?y)"),
    rw!("neg-ne"; "(! (!= ?x ?y))" => "(== ?x ?y)"),


    rw!("le-and-ge"; "(&& (<= ?x ?y) (>= ?x ?y))" => "(== ?x ?y)"),
    rw!("lt-or-gt"; "(|| (< ?x ?y) (> ?x ?y))" => "(!= ?x ?y)"),

    rw!("add-0"; "(+ ?x 0)" => "?x"),
    rw!("mul-0"; "(* ?x 0)" => "0"),
    rw!("mul-1"; "(* ?x 1)" => "?x"),
    rw!("sub-self"; "(- ?x ?x)" => "0"),
    // rw!("pow-split"; "(^ ?x (+ ?y ?z))" => "(* (^ ?x ?y) (^ ?x ?z))"),
    // rw!("pow-unsplit"; "(* (^ ?x ?y) (^ ?x ?z))" => "(^ ?x (+ ?y ?z))"),
    // rw!("pow-1"; "(^ ?x 1)" => "?x"),

    rw!("eq-elim-add"; "(== (+ ?x ?y) (+ ?x ?z))" => "(== ?y ?z)"),
    rw!("eq-elim-sub"; "(== (- ?y ?x) (- ?z ?x))" => "(== ?y ?z)"),
    // TODO: might be dangerous
    rw!("eq-elim-mul"; "(== (* ?x ?y) (* ?x ?z))" => "(== ?y ?z)" if is_not_zero("?x")),
    rw!("eq-sub-1"; "(== (+ ?x ?y) ?z)" => "(== ?x (- ?z ?y))"),
    rw!("eq-sub-2"; "(== (- ?z ?y) ?x)" => "(== ?z (+ ?x ?y))"),



    // rw!("eq-elim.general"; "(= (?o ?x ?y) (?o ?x ?z))" => "(= ?y ?z)"), // Not possible currently

] }

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph<Progge, ConstantFolding>, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    let zero = Progge::Num(0);
    move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
}

pub fn sexp_of_expr(e: &Expr) -> String {
    use Expr::*;
    match e {
        IntLit(i) => format!("{}", i),
        BoolLit(b) => format!("{}", b),
        Var(v) => format!("{}", &v.elem),
        Call(name, expr) => {
            let args = expr.iter().map(|e| sexp_of_expr(e)).collect::<Vec<_>>().join(" ");
            format!("({} {})", &name.elem, args)
        }
        BinOp(op, left, right) if op.elem == BinOpcode::Mod =>  {
            format!("(.mod {} {})", sexp_of_expr(left), sexp_of_expr(right))
        }
        BinOp(op, left, right) => {
            format!("({} {} {})", op.to_string(), sexp_of_expr(left), sexp_of_expr(right))
        }
        UnOp(op, inner) => {
            format!("({} {})", op.to_string(), sexp_of_expr(inner))
        }
        Array(els) => {
            format!("([] {})", els.iter().map(|e| sexp_of_expr(e)).collect::<Vec<_>>().join(" "))
        }
        DefaultArray { size, default_value } => {
            format!("([default] {} {})", sexp_of_expr(size), sexp_of_expr(default_value))
        }
        Index(arr, idx) => {
            format!("([idx] {} {})", sexp_of_expr(arr), sexp_of_expr(idx))
        }
    }
}
