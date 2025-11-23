use lukas::{
    ast::{
        Apply, Binding, CompilationUnit, Declaration, Expr, Lambda, Literal, Record, Tuple,
        ValueDeclaration, ValueDeclarator, namer::Symbols,
    },
    interpreter::Environment,
    parser::{Identifier, IdentifierPath, ParseInfo},
    typer::TypingContext,
};
use std::rc::Rc;

type A = ParseInfo;
type Id = IdentifierPath;
type Tree = Rc<Expr<A, Id>>;

fn var(name: &str) -> Tree {
    Expr::Variable(ParseInfo::default(), IdentifierPath::new(name)).into()
}

fn const_int(n: i32) -> Tree {
    Expr::Constant(ParseInfo::default(), Literal::Int(n)).into()
}

fn const_text(s: &str) -> Tree {
    Expr::Constant(ParseInfo::default(), Literal::Text(s.to_string())).into()
}

fn lambda(param: &str, body: Tree) -> Tree {
    Expr::Lambda(
        ParseInfo::default(),
        Lambda {
            parameter: IdentifierPath::new(param),
            body,
        },
    )
    .into()
}

fn apply(f: Tree, arg: Tree) -> Tree {
    Expr::Apply(
        ParseInfo::default(),
        Apply {
            function: f,
            argument: arg,
        },
    )
    .into()
}

fn let_in(binder: &str, bound: Tree, body: Tree) -> Tree {
    Expr::Let(
        ParseInfo::default(),
        Binding {
            binder: IdentifierPath::new(binder),
            bound,
            body,
        },
    )
    .into()
}

fn tuple(elements: Vec<Tree>) -> Tree {
    Expr::Tuple(ParseInfo::default(), Tuple { elements }).into()
}

fn record(fields: &[(&str, Tree)]) -> Tree {
    Expr::Record(
        ParseInfo::default(),
        Record {
            fields: fields
                .iter()
                .map(|(label, e)| (Identifier::from_str(label), Rc::clone(e)))
                .collect(),
        },
    )
    .into()
}

fn main() {
    let mut ctx = TypingContext::default();

    let tree = CompilationUnit::from_declarations(vec![Declaration::Value(
        ParseInfo::default(),
        ValueDeclaration {
            name: Identifier::from_str("start"),
            declarator: ValueDeclarator {
                type_signature: None,
                body: Expr::Lambda(
                    ParseInfo::default(),
                    Lambda {
                        parameter: IdentifierPath::new("x"),
                        body: const_int(47),
                    },
                ),
            },
        },
    )]);

    let symbols = Symbols::from(tree);
    println!("main: symbols: {symbols:?}");

    let id = lambda("x", var("x"));
    let id_binding = let_in("id", id, {
        let_in("z", apply(var("id"), const_int(1)), {
            let_in(
                "y",
                apply(var("id"), const_text("hej")),
                let_in(
                    "q",
                    record(&[
                        ("cash", const_int(427)),
                        ("name", const_text("Patrik Andersson")),
                    ]),
                    tuple(vec![var("y"), var("z"), var("q"), var("id")]),
                ),
            )
        })
    });

    let (_subs, typed_ast) = ctx.infer_type(&id_binding.resolve_names(&symbols)).unwrap();
    println!("main: type {}", typed_ast.type_info().inferred_type);

    let env = Environment::default();
    let runtime = Rc::new(typed_ast.erase_annotation()).reduce(&env).unwrap();

    println!("main: {runtime}");
}
