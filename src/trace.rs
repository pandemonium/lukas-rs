//! Diagnostic tracing shared by both binaries.
//!
//! Debug output goes to **stderr** and is **off by default**; select it with
//! `RUST_LOG`, e.g.
//!
//! ```text
//! RUST_LOG=lukas::typer=trace  cargo run -q --bin lukas -- --source ...
//! ```
//!
//! Program output (stdout: `print_endline`, the `####` / `$$$$` / `##TC`
//! markers) stays clean, so it is no longer tangled with debug spew.
//!
//! `TreeLayer` renders the `#[instrument]` span tree as indentation (depth =
//! span nesting), which is the cheap, native equivalent of the parser's
//! hand-rolled backtrace-based indent trick.

use tracing::{
    Subscriber,
    field::{Field, Visit},
};
use tracing_subscriber::{
    Registry,
    filter::EnvFilter,
    layer::{Context, Layer, SubscriberExt},
    registry::LookupSpan,
    util::SubscriberInitExt,
};

/// Pulls the `message` out of an event so `TreeLayer` can print it. (Structured
/// fields beyond the message are not rendered yet — a deliberate follow-up.)
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

/// Indents spans and events by their nesting depth, to stderr.
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
        let depth = span.scope().count().saturating_sub(1);
        eprintln!("{}{}", "  ".repeat(depth), attrs.metadata().name());
    }

    fn on_event(&self, event: &tracing::Event<'_>, ctx: Context<'_, S>) {
        let current = ctx.lookup_current();
        let depth = current.as_ref().map(|s| s.scope().count()).unwrap_or(0);

        // The calling function is supplied by the config, taken from the nearest
        // enclosing `#[instrument]` span (whose name is the function). So log
        // statements no longer need to name themselves.
        let func = current.as_ref().map(|s| s.name()).unwrap_or("");

        let mut visitor = EventVisitor::default();
        event.record(&mut visitor);

        if let Some(msg) = visitor.message {
            let indent = "  ".repeat(depth);
            if func.is_empty() {
                eprintln!("{indent}{msg}");
            } else {
                eprintln!("{indent}{func}: {msg}");
            }
        }
    }
}

/// Install the global tracing subscriber. Call once, at startup, from each
/// binary. Controlled by `RUST_LOG`; defaults to everything off.
pub fn init() {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("off"));

    Registry::default().with(filter).with(TreeLayer).init();
}
