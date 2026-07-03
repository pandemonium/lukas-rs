use clap::Parser;
use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer},
    compiler,
    parser::{self},
};

fn main() {
    lukas::trace::init();
    tracing::info!("Marmelade Compiler v420");

    let compiler = compiler::Compiler::parse();
    match compiler.compile_and_initialize() {
        Ok(program) => {
            let return_value = program
                .call(
                    &namer::QualifiedName::new(
                        // Move both Identifier types to namer or someething
                        // Path.t and Name.t
                        parser::IdentifierPath::new(ROOT_MODULE_NAME),
                        "start",
                    ),
                    ast::Literal::Int(427),
                )
                .expect("Expected a return value");

            println!("#### {return_value}");
        }

        Err(fault) => println!("$$$$ {fault}"),
    }
}
