use std::process::exit;

use clap::Parser;
use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer},
    compiler,
    interpreter::Environment,
    parser::{self},
};

use tracing::{
    Subscriber,
    field::{Field, Visit},
    info,
};
use tracing_subscriber::{
    Registry,
    layer::{Context, Layer, SubscriberExt},
    registry::LookupSpan,
    util::SubscriberInitExt,
};

#[derive(Default)]
struct EventVisitor {
    message: Option<String>,
}

impl Visit for EventVisitor {
    fn record_str(&mut self, field: &Field, value: &str) {
        if field.name() == "message" {
            self.message = Some(value.to_owned());
        }
    }

    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        if field.name() == "message" {
            self.message = Some(format!("{value:?}"));
        }
    }
}

struct TreeLayer;

impl<S> Layer<S> for TreeLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(
        &self,
        attrs: &tracing::span::Attributes<'_>,
        id: &tracing::Id,
        ctx: Context<'_, S>,
    ) {
        let span = ctx.span(id).unwrap();
        let depth = span.scope().count() - 1;
        let name = attrs.metadata().name();

        println!("{}{}", "  ".repeat(depth), name);
    }

    fn on_event(&self, event: &tracing::Event<'_>, ctx: Context<'_, S>) {
        let depth = ctx.lookup_current().map(|s| s.scope().count()).unwrap_or(0);

        let mut visitor = EventVisitor::default();
        event.record(&mut visitor);

        if let Some(msg) = visitor.message {
            println!("{}{}", "  ".repeat(depth), msg);
        }
    }
}

fn main() {
    Registry::default().with(TreeLayer).init();
    info!("Marmelade Compiler v420");

    let compiler = compiler::Compiler::parse();
    match compiler.compile_and_initialize() {
        Ok(program) => {
            let return_value = program
                .call(
                    &namer::QualifiedName::new(
                        parser::IdentifierPath::new(&ROOT_MODULE_NAME),
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
