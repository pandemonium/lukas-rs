use crate::{
    ast::{
        BUILTIN_MODULE_NAME, Kind, STDLIB_MODULE_NAME,
        namer::{Access, QualifiedName, Symbol, TypeDefinition, TypeOrigin, TypeSymbol},
    },
    bridge::{Intrinsic, Lambda1, PartialRawLambda1, PartialRawLambda2, RawLambda1, RawLambda3},
    interpreter::{
        Literal,
        cek::{Val, interpret_closure},
    },
    lambda1,
    lexer::Operator,
    parser::{self, ParseInfo, Parsed},
    phase::Phase,
    rawlambda1,
    typer::{BaseType, ConstraintSet, MetaVariable, Type, TypeScheme, stdlib_text_type},
};

fn comparison_signature() -> TypeScheme {
    let tp = MetaVariable::fresh();
    TypeScheme {
        quantifiers: vec![tp.clone()],
        underlying: Type::Arrow {
            domain: Type::Variable(tp.clone()).into(),
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
    let tp = MetaVariable::fresh();
    TypeScheme {
        quantifiers: vec![tp.clone()],
        underlying: Type::Arrow {
            domain: Type::Variable(tp.clone()).into(),
            codomain: Type::Arrow {
                domain: Type::Variable(tp.clone()).into(),
                codomain: Type::Variable(tp).into(),
            }
            .into(),
        },
        // todo: Some sort of Artih constraint here? Be an interesting test!
        constraints: ConstraintSet::default(),
    }
}

// `not` is polymorphic `∀a. a -> a` -- logical complement on Bool, bitwise on Int --
// mirroring the (binary) arithmetic scheme. The operand type selects the meaning.
fn unary_signature() -> TypeScheme {
    let tp = MetaVariable::fresh();
    TypeScheme {
        quantifiers: vec![tp.clone()],
        underlying: Type::Arrow {
            domain: Type::Variable(tp.clone()).into(),
            codomain: Type::Variable(tp).into(),
        },
        constraints: ConstraintSet::default(),
    }
}

fn mk_unary_op(op: fn(Literal) -> Option<Literal>) -> impl Fn(Val) -> Option<Val> {
    move |t| match t {
        Val::Constant(t) => op(t).map(Val::Constant),
        _otherwise => None,
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

pub fn import() -> Vec<Symbol<ParseInfo, parser::IdentifierPath, <Parsed as Phase>::TermId>> {
    let builtins = parser::IdentifierPath::new(BUILTIN_MODULE_NAME);
    let stdlib = parser::IdentifierPath::new(STDLIB_MODULE_NAME);

    // Leaf equality primitive: `=` desugars to the `Eq` method `eq`, whose primitive
    // witnesses (Int/Float/Char/Bool/Text/Unit) bottom out here. `equals` compares the
    // built-in literals (and, harmlessly, products); compound `Eq` is the tuple/user
    // witnesses recursing back through `eq`, never this leaf.
    let prim_eq = PartialRawLambda2 {
        name: "prim_eq",
        apply: |p, q| equals(p, q).map(|r| Val::Constant(Literal::Bool(r))),
        type_scheme: comparison_signature(),
    };

    // Leaf comparison primitives, in the spirit of `prim_show`: polymorphic over
    // the built-in literal types, they bottom out the `Ord` witnesses for Int/Float
    // (whose `compare` is written in terms of them). The `< > <= >=` operators no
    // longer bind here -- they desugar to the polymorphic `lt/gt/lte/gte` in the
    // Prelude, which delegate to `compare`.
    let prim_gte = PartialRawLambda2 {
        name: "prim_gte",
        apply: mk_comparison_op(gte),
        type_scheme: comparison_signature(),
    };

    let prim_lte = PartialRawLambda2 {
        name: "prim_lte",
        apply: mk_comparison_op(lte),
        type_scheme: comparison_signature(),
    };

    let prim_gt = PartialRawLambda2 {
        name: "prim_gt",
        apply: mk_comparison_op(gt),
        type_scheme: comparison_signature(),
    };

    let prim_lt = PartialRawLambda2 {
        name: "prim_lt",
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

    // `and`/`or`/`xor` are overloaded exactly like the arithmetic operators: one
    // polymorphic `∀a. a -> a -> a` builtin whose meaning is chosen by the operand
    // type -- logical on `Bool`, bitwise on `Int`. The interpreter dispatches on the
    // literal it actually holds (below); the backends monomorphise on the static type.
    let conjunction = PartialRawLambda2 {
        name: Operator::And.name(),
        apply: mk_artithmetic_op(and),
        type_scheme: artithmetic_signature(),
    };

    let disjunction = PartialRawLambda2 {
        name: Operator::Or.name(),
        apply: mk_artithmetic_op(or),
        type_scheme: artithmetic_signature(),
    };

    let exclusive_or = PartialRawLambda2 {
        name: Operator::Xor.name(),
        apply: mk_artithmetic_op(xor),
        type_scheme: artithmetic_signature(),
    };

    let complement = PartialRawLambda1 {
        name: Operator::Not.name(),
        apply: mk_unary_op(not),
        type_scheme: unary_signature(),
    };

    // Unary minus. It has no operator token of its own (the lexer sees the same `-`
    // as binary subtraction); the parser desugars prefix `-e` to `negate e`.
    let negation = PartialRawLambda1 {
        name: "negate",
        apply: mk_unary_op(negate),
        type_scheme: unary_signature(),
    };

    let text_fold_right_lambda = RawLambda3 {
        name: "text_fold_right",
        apply: text_fold_right,
        type_scheme: {
            let z = MetaVariable::fresh();

            TypeScheme {
                quantifiers: vec![z.clone()],
                underlying: Type::Arrow {
                    domain: Type::Arrow {
                        domain: Type::Base(BaseType::Char).into(),
                        codomain: Type::Arrow {
                            domain: Type::Variable(z.clone()).into(),
                            codomain: Type::Variable(z.clone()).into(),
                        }
                        .into(),
                    }
                    .into(),
                    codomain: Type::Arrow {
                        domain: Type::Variable(z.clone()).into(),
                        codomain: Type::Arrow {
                            domain: stdlib_text_type().into(),
                            codomain: Type::Variable(z).into(),
                        }
                        .into(),
                    }
                    .into(),
                },
                constraints: ConstraintSet::default(),
            }
        },
    };

    let terms = vec![
        rawlambda1!(prim_show).into_symbol(&stdlib),
        lambda1!(print_endline).into_symbol(&stdlib),
        prim_gte.into_symbol(&stdlib),
        prim_lte.into_symbol(&stdlib),
        prim_gt.into_symbol(&stdlib),
        prim_lt.into_symbol(&stdlib),
        prim_eq.into_symbol(&stdlib),
        conjunction.into_symbol(&builtins),
        disjunction.into_symbol(&builtins),
        exclusive_or.into_symbol(&builtins),
        complement.into_symbol(&builtins),
        negation.into_symbol(&builtins),
        plus.into_symbol(&builtins),
        minus.into_symbol(&builtins),
        times.into_symbol(&builtins),
        divided.into_symbol(&builtins),
        modulo.into_symbol(&builtins),
        text_fold_right_lambda.into_symbol(&builtins),
    ];

    let types = vec![
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Int),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 0,
            kind: Kind::Star,
        },
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Float),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 0,
            kind: Kind::Star,
        },
        // `Text` is no longer a builtin type: it is the stdlib DU
        // `opaque Text ::= Text Bytes` (Stdlib/Text.lady). String literals and
        // interpolation elaborate to it via `stdlib_text_type()`.
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Bool),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 0,
            kind: Kind::Star,
        },
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Unit),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 0,
            kind: Kind::Star,
        },
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Char),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 0,
            kind: Kind::Star,
        },
        TypeSymbol {
            definition: TypeDefinition::BaseType(BaseType::Array),
            origin: TypeOrigin::Builtin,
            opacity: Access::Anywhere,
            arity: 1,
            kind: Kind::Arrow(Kind::Star.into(), Kind::Star.into()),
        },
    ];

    terms
        .into_iter()
        .map(Symbol::Term)
        .chain(types.into_iter().map(Symbol::Type))
        .collect()
}

pub fn text_fold_right(f: Val, z: Val, fa: Val) -> Val {
    let Val::Constant(Literal::Text(t)) = fa else {
        panic!("must be text")
    };

    let name = QualifiedName::builtin("text_fold_right");
    t.chars().into_iter().rfold(z, |zz, c| {
        interpret_closure(&name, &f, vec![Val::Constant(Literal::Char(c)), zz.clone()]).unwrap()
    })
}

pub fn prim_show(x: Val) -> String {
    format!("{x}")
}

pub fn print_endline(x: String) {
    println!("{x}")
}

pub fn equals(p: Val, q: Val) -> Option<bool> {
    match (p, q) {
        (Val::Constant(Literal::Int(p)), Val::Constant(Literal::Int(q))) => Some(p == q),
        (Val::Constant(Literal::Float(p)), Val::Constant(Literal::Float(q))) => Some(p == q),
        (Val::Constant(Literal::Bool(p)), Val::Constant(Literal::Bool(q))) => Some(p == q),
        (Val::Constant(Literal::Text(p)), Val::Constant(Literal::Text(q))) => Some(p == q),
        (Val::Constant(Literal::Unit), Val::Constant(Literal::Unit)) => Some(true),
        (Val::Constant(Literal::Char(p)), Val::Constant(Literal::Char(q))) => Some(p == q),
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
        (Literal::Float(p), Literal::Float(q)) => Some(p >= q),
        (Literal::Text(p), Literal::Text(q)) => Some(p >= q),
        (Literal::Char(p), Literal::Char(q)) => Some(p >= q),
        _otherwise => None,
    }
}

pub fn gt(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p > q),
        (Literal::Float(p), Literal::Float(q)) => Some(p > q),
        (Literal::Text(p), Literal::Text(q)) => Some(p > q),
        (Literal::Char(p), Literal::Char(q)) => Some(p > q),
        _otherwise => None,
    }
}

pub fn lte(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p <= q),
        (Literal::Float(p), Literal::Float(q)) => Some(p <= q),
        (Literal::Text(p), Literal::Text(q)) => Some(p <= q),
        (Literal::Char(p), Literal::Char(q)) => Some(p <= q),
        _otherwise => None,
    }
}

pub fn lt(p: Literal, q: Literal) -> Option<bool> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(p < q),
        (Literal::Float(p), Literal::Float(q)) => Some(p < q),
        (Literal::Text(p), Literal::Text(q)) => Some(p < q),
        (Literal::Char(p), Literal::Char(q)) => Some(p < q),
        _otherwise => None,
    }
}

// `and`/`or`/`xor` are logical on `Bool` and bitwise on `Int` -- the same operand
// overloading the arithmetic operators use (see `plus`). `None` for any other pair
// mirrors `plus` on non-numbers: an ill-typed application the type checker rejects.
pub fn and(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Bool(p), Literal::Bool(q)) => Some(Literal::Bool(p && q)),
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p & q)),
        _otherwise => None,
    }
}

pub fn or(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Bool(p), Literal::Bool(q)) => Some(Literal::Bool(p || q)),
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p | q)),
        _otherwise => None,
    }
}

pub fn xor(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Bool(p), Literal::Bool(q)) => Some(Literal::Bool(p ^ q)),
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p ^ q)),
        _otherwise => None,
    }
}

// Unary `not`: logical negation on Bool, bitwise complement on Int.
pub fn not(p: Literal) -> Option<Literal> {
    match p {
        Literal::Bool(p) => Some(Literal::Bool(!p)),
        Literal::Int(p) => Some(Literal::Int(!p)),
        _otherwise => None,
    }
}

// Unary minus: arithmetic negation on Int and Float (mirrors `plus`'s operand set).
pub fn negate(p: Literal) -> Option<Literal> {
    match p {
        Literal::Int(p) => Some(Literal::Int(-p)),
        Literal::Float(p) => Some(Literal::Float(-p)),
        _otherwise => None,
    }
}

pub fn plus(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p + q)),
        (Literal::Float(p), Literal::Float(q)) => Some(Literal::Float(p + q)),
        _otherwise => None,
    }
}

pub fn minus(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p - q)),
        (Literal::Float(p), Literal::Float(q)) => Some(Literal::Float(p - q)),
        _otherwise => None,
    }
}

pub fn times(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p * q)),
        (Literal::Float(p), Literal::Float(q)) => Some(Literal::Float(p * q)),
        _otherwise => None,
    }
}

pub fn divided(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p / q)),
        (Literal::Float(p), Literal::Float(q)) => Some(Literal::Float(p / q)),
        _otherwise => None,
    }
}

pub fn modulo(p: Literal, q: Literal) -> Option<Literal> {
    match (p, q) {
        (Literal::Int(p), Literal::Int(q)) => Some(Literal::Int(p % q)),
        (Literal::Float(p), Literal::Float(q)) => Some(Literal::Float(p % q)),
        _otherwise => None,
    }
}
