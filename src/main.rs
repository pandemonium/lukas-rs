use std::process::exit;

use lukas::{
    ast::{self, namer},
    interpreter::Environment,
    lexer::LexicalAnalyzer,
    parser::{Identifier, Parser},
    typer::TypingContext,
};

use tracing::{
    Subscriber,
    field::{Field, Visit},
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

    let _ctx = TypingContext::default();

    let mut lexer = LexicalAnalyzer::default();
    let input = include_str!("../examples/List.lady");

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
