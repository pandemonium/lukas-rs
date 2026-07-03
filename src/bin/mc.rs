use clap::Parser;
use lukas::compiler;

fn main() {
    lukas::trace::init();
    tracing::info!("Marmelade Compiler v420");

    let compiler = compiler::Compiler::parse();
    match compiler.compiler_main() {
        Ok(..) => (),
        Err(e) => println!("$$$$ {e}"),
    }
}
