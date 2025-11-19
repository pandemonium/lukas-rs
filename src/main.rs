use lukas::{
    ast::{
        Apply, Binding, CompilationUnit, Declaration, Expr, Lambda, Literal, ModuleDeclaration,
        ModuleDeclarator, Tuple, ValueDeclaration, ValueDeclarator, namer::Symbols,
    },
    interpreter::Environment,
    parser::{Identifier, ParseInfo},
    typer::TypingContext,
};
use std::rc::Rc;

type A = ParseInfo;
type Id = Identifier;
type Tree = Rc<Expr<A, Id>>;

fn var(name: &str) -> Tree {
    Rc::new(Expr::Variable(
        ParseInfo::default(),
        Identifier::from_str(name),
    ))
}

fn const_int(n: i32) -> Tree {
    Rc::new(Expr::Constant(ParseInfo::default(), Literal::Int(n)))
}

fn const_text(s: &str) -> Tree {
    Rc::new(Expr::Constant(
        ParseInfo::default(),
        Literal::Text(s.to_string()),
    ))
}

fn lambda(param: &str, body: Tree) -> Tree {
    Rc::new(Expr::Lambda(
        ParseInfo::default(),
        Lambda {
            parameter: Identifier::from_str(param),
            body,
        },
    ))
}

fn apply(f: Tree, arg: Tree) -> Tree {
    Rc::new(Expr::Apply(
        ParseInfo::default(),
        Apply {
            function: f,
            argument: arg,
        },
    ))
}

fn let_in(binder: &str, bound: Tree, body: Tree) -> Tree {
    Rc::new(Expr::Let(
        ParseInfo::default(),
        Binding {
            binder: Identifier::from_str(binder),
            bound,
            body,
        },
    ))
}

fn tuple(elements: Vec<Tree>) -> Tree {
    Rc::new(Expr::Tuple(ParseInfo::default(), Tuple { elements }))
}

fn main() {
    let mut ctx = TypingContext::default();

    let tree = CompilationUnit {
        root: ModuleDeclaration {
            name: Identifier::from_str("_root_"),
            declarator: ModuleDeclarator {
                contents: vec![Declaration::Value(
                    ParseInfo::default(),
                    ValueDeclaration {
                        name: Identifier::from_str("start"),
                        declarator: ValueDeclarator {
                            type_signature: None,
                            body: Expr::Lambda(
                                ParseInfo::default(),
                                Lambda {
                                    parameter: Identifier::from_str("x"),
                                    body: const_int(47),
                                },
                            ),
                        },
                    },
                )],
            },
        },
    };
    let symbols = Symbols::from(tree);
    println!("main: symbols: {symbols:?}");

    let id = lambda("x", var("x"));
    let id_binding = let_in("id", id.clone(), {
        let_in("z", apply(var("id"), const_int(1)), {
            let_in(
                "y",
                apply(var("id"), const_text("hej")),
                tuple(vec![var("y"), var("z"), var("id")]),
            )
        })
    });

    let (_subs, typed_ast) = ctx.infer_type(&id_binding.resolve_bindings()).unwrap();
    println!("main: type {}", typed_ast.type_info().inferred_type);

    let env = Environment::default();
    let runtime = Rc::new(typed_ast.erase_annotation()).reduce(&env).unwrap();

    println!("main: {runtime}");
}
