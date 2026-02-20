use clap::Parser;
use lukas::compiler;
use tracing::info;

fn main() {
    info!("Marmelade Compiler v420");

    let compiler = compiler::Compiler::parse();
    compiler.compiler_main().unwrap()
}
