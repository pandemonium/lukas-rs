use clap::Parser;

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer},
    compiler,
    parser::{self},
};

/// `lukas` runs a program; `--check` stops after the front end. The mode is the
/// binary's, not the compiler's: `Compiler` is the compilation's configuration and
/// stays free of what a particular command line wants done with it.
#[derive(Parser)]
struct Cli {
    #[command(flatten)]
    compiler: compiler::Compiler,

    /// Report what the front end makes of the program, without running it.
    #[arg(long)]
    check: bool,
}

fn main() {
    lukas::trace::init();
    tracing::info!("Marmelade Compiler v420");

    let Cli { compiler, check } = Cli::parse();

    // The same work an editor asks for, so a diagnostic can be reproduced from a
    // shell -- see `notes/language-server.md`.
    if check {
        match compiler.check() {
            Ok(_) => println!("ok"),
            Err(fault) => {
                println!("$$$$ {fault}");
                std::process::exit(1);
            }
        }
        return;
    }

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
