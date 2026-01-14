use std::process::exit;

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
    let input = include_str!("../examples/8.txt");

    let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

    //    for t in tokens {
    //        println!("{t}")
    //    }

    let mut parser = Parser::from_tokens(tokens);
    let program = parser.parse_compilation_unit().unwrap();

    println!("Program: {program}");

    let env = match Environment::typecheck_and_initialize(program) {
        Ok(env) => env,
        Err(error) => {
            eprintln!("{error}");
            exit(1);
        }
    };

    let return_value = env
        .call(
            &namer::QualifiedName::from_root_symbol(Identifier::from_str("start")),
            ast::Literal::Int(427),
        )
        .expect("Expected a return value");

    println!("main: return value: {return_value}");
}
