use lukas::{
    ast::{self, namer},
    interpreter::Environment,
    lexer::LexicalAnalyzer,
    parser::{Identifier, Parser},
    typer::TypingContext,
};

fn main() {
    let _ctx = TypingContext::default();

    let mut lexer = LexicalAnalyzer::default();
    let input = include_str!("../examples/4.txt");

    let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

    //    for t in tokens {
    //        println!("{t}")
    //    }

    let mut parser = Parser::from_tokens(tokens);
    let program = parser.parse_compilation_unit().unwrap();

    //    Type inferencing ought to not infer a naked anonymous record type,
    //    it must instead resolve its type constructor. How does it do this?
    //
    //    Lookup the type symbol, get it from there

    println!("Program: {program}");

    let env = Environment::typecheck_and_initialize(program).expect("initialized");
    println!("main: env: {env}");

    let return_value = env.call(
        &namer::QualifiedName::from_root_symbol(Identifier::from_str("start")),
        ast::Literal::Int(27),
    );
    println!("main: return value: {return_value}");
}
