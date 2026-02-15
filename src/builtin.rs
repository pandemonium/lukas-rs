use crate::{
    ast::{
        BUILTIN_MODULE_NAME, STDLIB_MODULE_NAME,
        namer::{Symbol, TypeDefinition, TypeOrigin, TypeSymbol},
    },
    bridge::{External, Lambda1, Lambda2, PartialRawLambda2, RawLambda1},
    interpreter::{Literal, cek::Val},
    lambda1, lambda2,
    lexer::Operator,
    parser::{self, ParseInfo},
    rawlambda1,
    typer::{BaseType, ConstraintSet, Type, TypeParameter, TypeScheme},
};

fn comparison_signature() -> TypeScheme {
    let tp = TypeParameter::fresh();
    TypeScheme {
        quantifiers: vec![tp],
        underlying: Type::Arrow {
            domain: Type::Variable(tp).into(),
            codomain: Type::Arrow {
                domain: Type::Variable(tp).into(),
                codomain: Type::Base(BaseType::Bool).into(),
            }
            .into(),
        },
        // todo: Some sort of Ord constraint here? Be an interesting test!
        constraints: ConstraintSet::default(),
    }
}

fn artithmetic_signature() -> TypeScheme {
    let tp = TypeParameter::fresh();
    TypeScheme {
        quantifiers: vec![tp],
        underlying: Type::Arrow {
            domain: Type::Variable(tp).into(),
            codomain: Type::Arrow {
                domain: Type::Variable(tp).into(),
                codomain: Type::Variable(tp).into(),
            }
            .into(),
        },
        // todo: Some sort of Artih constraint here? Be an interesting test!
        constraints: ConstraintSet::default(),
    }
}

fn mk_comparison_op(op: fn(Literal, Literal) -> Option<bool>) -> impl Fn(Val, Val) -> Option<Val> {
    move |t, u| match (t, u) {
        (Val::Constant(t), Val::Constant(u)) => op(t, u).map(|r| Val::Constant(Literal::Bool(r))),

        _otherwise => None,
    }
}

fn mk_artithmetic_op(
    op: fn(Literal, Literal) -> Option<Literal>,
) -> impl Fn(Val, Val) -> Option<Val> {
    move |t, u| match (t, u) {
        (Val::Constant(t), Val::Constant(u)) => op(t, u).map(Val::Constant),

        _otherwise => None,
    }
}

pub fn import() -> Vec<Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>> {
    let builtins = parser::IdentifierPath::new(BUILTIN_MODULE_NAME);
    let stdlib = parser::IdentifierPath::new(STDLIB_MODULE_NAME);

    let eq = PartialRawLambda2 {
        name: Operator::Equals.name(),
        apply: |p, q| equals(p, q).map(|r| Val::Constant(Literal::Bool(r))),
        type_scheme: comparison_signature(),
    };

    let gte = PartialRawLambda2 {
        name: Operator::Gte.name(),
        apply: mk_comparison_op(gte),
        type_scheme: comparison_signature(),
    };

    let lte = PartialRawLambda2 {
        name: Operator::Lte.name(),
        apply: mk_comparison_op(lte),
        type_scheme: comparison_signature(),
    };

    let gt = PartialRawLambda2 {
        name: Operator::Gt.name(),
        apply: mk_comparison_op(gt),
        type_scheme: comparison_signature(),
    };

    let lt = PartialRawLambda2 {
        name: Operator::Lt.name(),
        apply: mk_comparison_op(lt),
        type_scheme: comparison_signature(),
    };

    let plus = PartialRawLambda2 {
        name: Operator::Plus.name(),
        apply: mk_artithmetic_op(plus),
        type_scheme: artithmetic_signature(),
    };

    let minus = PartialRawLambda2 {
        name: Operator::Minus.name(),
        apply: mk_artithmetic_op(minus),
        type_scheme: artithmetic_signature(),
    };

    let times = PartialRawLambda2 {
        name: Operator::Times.name(),
        apply: mk_artithmetic_op(times),
        type_scheme: artithmetic_signature(),
    };

    let divided = PartialRawLambda2 {
        name: Operator::Division.name(),
        apply: mk_artithmetic_op(divided),
        type_scheme: artithmetic_signature(),
    };

    let modulo = PartialRawLambda2 {
        name: Operator::Modulo.name(),
        apply: mk_artithmetic_op(modulo),
        type_scheme: artithmetic_signature(),
    };

    let terms = vec![
        rawlambda1!(show).into_symbol(&stdlib),
        lambda1!(print_endline).into_symbol(&stdlib),
        eq.into_symbol(&builtins),
        gte.into_symbol(&builtins),
        lte.into_symbol(&builtins),
        gt.into_symbol(&builtins),
        lt.into_symbol(&builtins),
        lambda2!(and).into_symbol(&builtins),
        lambda2!(or).into_symbol(&builtins),
        lambda2!(xor).into_symbol(&builtins),
        plus.into_symbol(&builtins),
        minus.into_symbol(&builtins),
        times.into_symbol(&builtins),
        divided.into_symbol(&builtins),
        modulo.into_symbol(&builtins),
    ];

    let types = vec![
        TypeSymbol {
            definition: TypeDefinition::Builtin(BaseType::Int),
            origin: TypeOrigin::Builtin,
            arity: 0,
        },
        TypeSymbol {
            definition: TypeDefinition::Builtin(BaseType::Text),
            origin: TypeOrigin::Builtin,
            arity: 0,
        },
        TypeSymbol {
            definition: TypeDefinition::Builtin(BaseType::Bool),
            origin: TypeOrigin::Builtin,
            arity: 0,
        },
        TypeSymbol {
            definition: TypeDefinition::Builtin(BaseType::Unit),
            origin: TypeOrigin::Builtin,
            arity: 0,
        },
    ];

    terms
        .into_iter()
        .map(Symbol::Term)
        .chain(types.into_iter().map(Symbol::Type))
        .collect()
}

pub fn show(x: Val) -> String {
    format!("{x}")
}

pub fn print_endline(x: String) {
    println!("{x}")
}

pub fn equals(p: Val, q: Val) -> Option<bool> {
    match (p, q) {
        (Val::Constant(Literal::Int(p)), Val::Constant(Literal::Int(q))) => Some(p == q),
        (Val::Constant(Literal::Bool(p)), Val::Constant(Literal::Bool(q))) => Some(p == q),
        (Val::Constant(Literal::Text(p)), Val::Constant(Literal::Text(q))) => Some(p == q),
        (Val::Constant(Literal::Unit), Val::Constant(Literal::Unit)) => Some(true),
        (Val::Product(p), Val::Product(q)) => {
            let result = p.len() == q.len()
                && p.into_iter()
                    .zip(q)
                    .map(|(p, q)| equals(p, q))
                    .all(|v| matches!(v, Some(true)));

            Some(result)
        }
        _otherwise => None,
    }
}

pub fn gte(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p >= q),
        (Literal::Text(p), Literal::Text(q)) => Some(p >= q),
        _otherwise => None,
    }
}

pub fn gt(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p > q),
        (Literal::Text(p), Literal::Text(q)) => Some(p > q),
        _otherwise => None,
    }
}

pub fn lte(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p <= q),
        (Literal::Text(p), Literal::Text(q)) => Some(p <= q),
        _otherwise => None,
    }
}

pub fn lt(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p < q),
        (Literal::Text(p), Literal::Text(q)) => Some(p < q),
        _otherwise => None,
    }
}

fn and(p: bool, q: bool) -> bool {
    p && q
}

fn or(p: bool, q: bool) -> bool {
    p || q
}

fn xor(p: bool, q: bool) -> bool {
    p ^ q
}

pub fn plus(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p + q)),
        _otherwise => None,
    }
}

pub fn minus(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p - q)),
        _otherwise => None,
    }
}

pub fn times(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p * q)),
        _otherwise => None,
    }
}

pub fn divided(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p / q)),
        _otherwise => None,
    }
}

pub fn modulo(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p % q)),
        _otherwise => None,
    }
}
