use lukas::{
    ast::{
        self, Apply, Binding, CompilationUnit, Declaration, Expr, Lambda, Literal, ProductElement,
        Projection, Record, Tuple, ValueDeclaration, ValueDeclarator, namer,
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

fn const_int(n: i64) -> Tree {
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

fn proj(base: Tree, field: &str) -> Tree {
    Expr::Project(
        ParseInfo::default(),
        Projection {
            base,
            select: ProductElement::Name(Identifier::from_str(field)),
        },
    )
    .into()
}

fn main() {
    let _ctx = TypingContext::default();

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
                    tuple(vec![var("y"), var("zz"), proj(var("q"), "name"), var("id")]),
                ),
            )
        })
    });

    let program = CompilationUnit::from_declarations(vec![
        Declaration::Value(
            ParseInfo::default(),
            ValueDeclaration {
                name: Identifier::from_str("zz"),
                declarator: ValueDeclarator {
                    type_signature: None,
                    body: Expr::Constant(ParseInfo::default(), Literal::Int(1)),
                },
            },
        ),
        Declaration::Value(
            ParseInfo::default(),
            ValueDeclaration {
                name: Identifier::from_str("start"),
                declarator: ValueDeclarator {
                    type_signature: None,
                    body: Expr::Lambda(
                        ParseInfo::default(),
                        Lambda {
                            parameter: IdentifierPath::new("x"),
                            body: id_binding.clone(),
                        },
                    ),
                },
            },
        ),
    ]);

    let env = Environment::typecheck_and_initialize(program).expect("initialized");
    println!("main: env: {env}");

    let return_value = env.call(
        &namer::QualifiedName::from_root_symbol(Identifier::from_str("start")),
        ast::Literal::Int(1),
    );
    println!("main: return value: {return_value}");
}
