use std::marker::PhantomData;

use crate::{
    ast::{TypeSignature, namer::TermSymbol},
    bridge::{External, Lambda1, Lambda2, PartialRawLambda2, RawLambda1},
    interpreter::{Literal, Value},
    lambda1, lambda2,
    lexer::Operator,
    parser::{self, ParseInfo},
    rawlambda1,
    typer::{BaseType, Type, TypeParameter},
};

impl Value {
    fn try_into_constant(self) -> Option<Literal> {
        if let Value::Constant(literal) = self {
            Some(literal)
        } else {
            None
        }
    }
}

fn comparison_signature() -> TypeSignature<ParseInfo, parser::IdentifierPath> {
    let a = parser::Identifier::from_str("a");
    // Is this dangerous?
    let tp = TypeParameter::new(0);
    let body = {
        Type::Arrow {
            domain: Type::Variable(tp).into(),
            codomain: Type::Arrow {
                domain: Type::Variable(tp).into(),
                codomain: Type::Base(BaseType::Bool).into(),
            }
            .into(),
        }
    };
    TypeSignature {
        universal_quantifiers: vec![a.clone()],
        body: body.reify(&vec![a]),
        phase: PhantomData,
    }
}

fn artithmetic_signature() -> TypeSignature<ParseInfo, parser::IdentifierPath> {
    let a = parser::Identifier::from_str("a");
    // Is this dangerous?
    let tp = TypeParameter::new(0);
    let body = {
        Type::Arrow {
            domain: Type::Variable(tp).into(),
            codomain: Type::Arrow {
                domain: Type::Variable(tp).into(),
                codomain: Type::Variable(tp).into(),
            }
            .into(),
        }
    };
    TypeSignature {
        universal_quantifiers: vec![a.clone()],
        body: body.reify(&vec![a]),
        phase: PhantomData,
    }
}

fn mk_comparison_op(
    op: fn(Literal, Literal) -> Option<bool>,
) -> impl Fn(Value, Value) -> Option<Value> {
    move |t, u| match (t, u) {
        (Value::Constant(t), Value::Constant(u)) => {
            op(t, u).map(|r| Value::Constant(Literal::Bool(r)))
        }

        _otherwise => None,
    }
}

fn mk_artithmetic_op(
    op: fn(Literal, Literal) -> Option<Literal>,
) -> impl Fn(Value, Value) -> Option<Value> {
    move |t, u| match (t, u) {
        (Value::Constant(t), Value::Constant(u)) => op(t, u).map(|r| Value::Constant(r)),

        _otherwise => None,
    }
}

pub fn import() -> Vec<TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>> {
    let eq = PartialRawLambda2 {
        name: Operator::Equals.name(),
        apply: |p, q| equals(p, q).map(|r| Value::Constant(Literal::Bool(r))),
        signature: comparison_signature(),
    };

    let gte = PartialRawLambda2 {
        name: Operator::Gte.name(),
        apply: mk_comparison_op(gte),
        signature: comparison_signature(),
    };

    let lte = PartialRawLambda2 {
        name: Operator::Lte.name(),
        apply: mk_comparison_op(lte),
        signature: comparison_signature(),
    };

    let gt = PartialRawLambda2 {
        name: Operator::Gt.name(),
        apply: mk_comparison_op(gt),
        signature: comparison_signature(),
    };

    let lt = PartialRawLambda2 {
        name: Operator::Lt.name(),
        apply: mk_comparison_op(lt),
        signature: comparison_signature(),
    };

    let plus = PartialRawLambda2 {
        name: Operator::Plus.name(),
        apply: mk_artithmetic_op(plus),
        signature: artithmetic_signature(),
    };

    let minus = PartialRawLambda2 {
        name: Operator::Minus.name(),
        apply: mk_artithmetic_op(minus),
        signature: artithmetic_signature(),
    };

    let times = PartialRawLambda2 {
        name: Operator::Times.name(),
        apply: mk_artithmetic_op(times),
        signature: artithmetic_signature(),
    };

    let divided = PartialRawLambda2 {
        name: Operator::Division.name(),
        apply: mk_artithmetic_op(divided),
        signature: artithmetic_signature(),
    };

    let modulo = PartialRawLambda2 {
        name: Operator::Modulo.name(),
        apply: mk_artithmetic_op(modulo),
        signature: artithmetic_signature(),
    };

    vec![
        rawlambda1!(show).into_symbol(),
        lambda1!(print_endline).into_symbol(),
        eq.into_symbol(),
        gte.into_symbol(),
        lte.into_symbol(),
        gt.into_symbol(),
        lt.into_symbol(),
        lambda2!(and).into_symbol(),
        lambda2!(or).into_symbol(),
        lambda2!(xor).into_symbol(),
        plus.into_symbol(),
        minus.into_symbol(),
        times.into_symbol(),
        divided.into_symbol(),
        modulo.into_symbol(),
    ]
}

pub fn show(x: Value) -> String {
    format!("{x}")
}

pub fn print_endline(x: String) {
    println!("{x}")
}

pub fn equals(p: Value, q: Value) -> Option<bool> {
    match (p, q) {
        (Value::Constant(Literal::Int(p)), Value::Constant(Literal::Int(q))) => Some(p == q),
        (Value::Constant(Literal::Bool(p)), Value::Constant(Literal::Bool(q))) => Some(p == q),
        (Value::Constant(Literal::Text(p)), Value::Constant(Literal::Text(q))) => Some(p == q),
        (Value::Constant(Literal::Unit), Value::Constant(Literal::Unit)) => Some(true),
        (Value::Product(p), Value::Product(q)) => {
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
