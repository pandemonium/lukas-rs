use clap::Parser;
use lukas::compiler;
use tracing::info;

fn main() {
    info!("Marmelade Compiler v420");

    let compiler = compiler::Compiler::parse();
    match compiler.compiler_main() {
        Ok(..) => (),
        Err(e) => println!("$$$$ {e}"),
    }
}
