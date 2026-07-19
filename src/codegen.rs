use fmt::Write;
use std::{fmt, fs, io, path};

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    ast::{
        BUILTIN_MODULE_NAME, Binding, Literal, ProductElement, STDLIB_MODULE_NAME, Segment,
        namer::QualifiedName, pattern::Pattern,
    },
    closed::{self, CaptureInfo, Closed, Identifier, LexicalLevel},
    lambda_lift::{self, ChainWorker, ClosureInfo, LiftedFunction, TopLevelBinding, Worker},
    phase,
};

pub struct Codegen;

impl phase::Phase for Codegen {
    type Annotation = CaptureInfo;
    type TermId = closed::Identifier;
    type TypeId = QualifiedName;
}

type Expr = phase::Expr<Codegen>;

// Naming for the C backend. Mirrors the strategy the Scheme backend uses --
// builtin/foreign terms map to a fixed runtime name, everything else to its
// qualified surface name -- but is kept independent of `chez.rs` (which is
// Scheme-only) and always emits valid C identifiers.
fn c_name(q: &QualifiedName) -> String {
    if is_builtin(q) {
        map_builtin_name(q).to_owned()
    } else {
        surface_name(q)
    }
}

fn is_builtin(q: &QualifiedName) -> bool {
    q.module.head == BUILTIN_MODULE_NAME || q.module.head == STDLIB_MODULE_NAME
}

// Qualified name flattened to a C identifier: module path and member joined
// with `_`. The lexer restricts identifiers to alphanumerics and `_`, and
// operators reach `c_name` only as builtins (named via `map_builtin_name`), so
// the join is already a valid C identifier.
fn surface_name(q: &QualifiedName) -> String {
    let mut parts = Vec::with_capacity(2 + q.module.tail.len());
    parts.push(q.module.head.clone());
    parts.extend_from_slice(q.module.tail.as_slice());
    parts.push(q.member.as_str().to_owned());
    parts.join("_")
}

// Runtime function names for builtin/foreign primitives -- these name the C
// runtime the emitted code links against, so they must be valid C identifiers.
fn map_builtin_name(q: &QualifiedName) -> &'static str {
    match q.member.as_str() {
        "print_endline" => "builtin_print_endline",
        "prim_show" => "builtin_show",
        "=" => "builtin_eq",
        "-" => "builtin_sub",
        "+" => "builtin_add",
        "*" => "builtin_mul",
        "/" => "builtin_div",
        "%" => "builtin_mod",
        "<" => "builtin_lt",
        ">" => "builtin_gt",
        "and" => "builtin_and",
        "xor" => "builtin_xor",
        "or" => "builtin_or",
        ">=" => "builtin_ge",
        "<=" => "builtin_le",
        "text_fold_right" => "builtin_text_fold_right",
        otherwise => panic!("unmapped builtin {otherwise:?}"),
    }
}

#[derive(Debug, Default)]
pub struct CodeBuffer(String);

impl CodeBuffer {
    pub fn write_to_file(&self, path: impl AsRef<path::Path>) -> io::Result<()> {
        fs::write(path, &self.0)
    }

    /// Splice a file's contents into the buffer verbatim -- used to inline a
    /// module's foreign `.ss` implementation into the emitted Scheme.
    pub fn splice_file(&mut self, path: impl AsRef<path::Path>) -> io::Result<()> {
        let path = path.as_ref();
        let contents = fs::read_to_string(path)
            .map_err(|e| io::Error::new(e.kind(), format!("{}: {e}", path.display())))?;
        self.0.push_str(&contents);
        self.0.push('\n');
        Ok(())
    }
}

impl fmt::Write for CodeBuffer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push_str(s);
        Ok(())
    }
}

impl fmt::Display for CodeBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(buffer) = self;
        write!(f, "{buffer}")
    }
}

// If `head` names a builtin with a direct primitive form, return its C prim
// name and arity. A *saturated* application of it can be emitted as a direct
// call (`prim_add(x, y)`) instead of the allocating curried-closure `apply`
// chain. text_fold_right has no prim form and stays curried.
fn builtin_prim(head: &Expr) -> Option<(&'static str, usize)> {
    let q = match head {
        Expr::Variable(_, Identifier::Global(q)) => q.as_ref(),
        Expr::InvokeBridge(_, the) => &the.qualified_name,
        _otherwise => return None,
    };
    if !is_builtin(q) {
        return None;
    }
    Some(match q.member.as_str() {
        "+" => ("prim_add", 2),
        "-" => ("prim_sub", 2),
        "*" => ("prim_mul", 2),
        "/" => ("prim_div", 2),
        "%" => ("prim_mod", 2),
        "=" => ("prim_eq", 2),
        "<" => ("prim_lt", 2),
        ">" => ("prim_gt", 2),
        "<=" => ("prim_le", 2),
        ">=" => ("prim_ge", 2),
        "and" => ("prim_and", 2),
        "or" => ("prim_or", 2),
        "xor" => ("prim_xor", 2),
        "prim_show" => ("prim_show", 1),
        "print_endline" => ("prim_print_endline", 1),
        _otherwise => return None,
    })
}

// Fresh scrutinee temporaries for `deconstruct`. A monotonic counter keeps each
// match's binding distinct from every other (including nested matches).
static MATCH_ID: AtomicUsize = AtomicUsize::new(0);

impl lambda_lift::Program {
    // Emit a complete, self-contained C translation unit: every lifted lambda
    // becomes a `Value f(Value self, Value arg)` function, every top-level
    // definition a `Value` global initialised once in `startup`, and `main`
    // runs the program's `start` entry point. Builtin definitions are omitted --
    // the runtime (`c/runtime.c`) provides them.
    pub fn generate_code(&self, out: &mut CodeBuffer) -> fmt::Result {
        writeln!(out, "#include \"runtime.h\"")?;
        writeln!(out, "#include \"gc.h\"\n")?;

        // Forward declarations, so functions and globals can reference each
        // other (and themselves) regardless of definition order.
        for LiftedFunction { name, .. } in &self.functions {
            writeln!(out, "Value {}(Value self, Value l0);", c_name(name))?;
        }
        for Worker { name, params, .. } in &self.workers {
            let signature = vec!["Value"; *params].join(", ");
            writeln!(out, "Value {}_worker({});", c_name(name), signature)?;
        }
        for ChainWorker { head, .. } in &self.chain_workers {
            writeln!(out, "Value {}_uworker(Value self, Value *args);", c_name(head))?;
        }
        for TopLevelBinding { name, .. } in &self.globals {
            if !is_builtin(name) {
                writeln!(out, "Value {};", c_name(name))?;
            }
        }

        // Foreign globals live in the companion `<Module>.c` (defined by the
        // `FOREIGN_DECL` macro alongside a `<name>__init` builder and, for arity
        // >= 1, an uncurried `<name>_worker`). Declare them here so the emitted
        // code can reference the value, call the builder, and direct-call the
        // worker at saturated call sites.
        for name in &self.foreign {
            writeln!(out, "extern Value {0};", c_name(name))?;
            writeln!(out, "extern Value {0}__init(void);", c_name(name))?;
            if let Some(&arity) = self.arities.get(name) {
                if arity > 0 {
                    let params = vec!["Value"; arity].join(", ");
                    writeln!(out, "extern Value {0}_worker({1});", c_name(name), params)?;
                }
            }
        }
        writeln!(out)?;

        for LiftedFunction { name, code, .. } in &self.functions {
            tracing::trace!("generate_code: {name}");
            writeln!(out, "Value {}(Value self, Value l0) {{", c_name(name))?;
            writeln!(out, "  (void)self; (void)l0;")?;
            write!(out, "  return ")?;
            self.compile_expr(code, out)?;
            writeln!(out, ";\n}}\n")?;
        }

        // Uncurried workers: an N-ary function whose parameters are the flat frame
        // `l0..l{N-1}`. No `self` -- these are closure-free, so their bodies carry
        // no captures. `compile_apply` calls them directly at saturated call sites.
        for Worker { name, params, body } in &self.workers {
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(out, "Value {}_worker({}) {{", c_name(name), signature)?;
            for i in 0..*params {
                write!(out, "  (void)l{i};")?;
            }
            write!(out, "\n  return ")?;
            self.compile_expr(body, out)?;
            writeln!(out, ";\n}}\n")?;
        }

        // Chain workers: the uncurried entry a chain-head closure carries, run by
        // `apply_n` when the head is applied to exactly `arity` arguments. `self`
        // is the head closure (so `env_get(self, i)` still reads the chain's
        // captures); the flattened parameters arrive in `args[0..arity]`, which we
        // name `l0..l{arity-1}` to match the frame the flattened body expects.
        for ChainWorker { head, arity, body } in &self.chain_workers {
            writeln!(out, "Value {}_uworker(Value self, Value *args) {{", c_name(head))?;
            write!(out, "  (void)self;")?;
            for i in 0..*arity {
                write!(out, " Value l{i} = args[{i}];")?;
            }
            write!(out, "\n  return ")?;
            self.compile_expr(body, out)?;
            writeln!(out, ";\n}}\n")?;
        }

        // Globals may hold closures that name each other's code, but building a
        // closure only takes the address of a function, so initialisation order
        // is immaterial here.
        writeln!(out, "void startup(void) {{")?;
        for TopLevelBinding { name, value, .. } in &self.globals {
            if is_builtin(name) {
                continue;
            }
            write!(out, "  {} = ", c_name(name))?;
            self.compile_expr(value, out)?;
            writeln!(out, ";")?;
        }
        // Build each foreign closure from its companion-provided builder. Runs
        // after `gc_init`/`runtime_init` (see `main`), so `mk_closure` is safe.
        for name in &self.foreign {
            writeln!(out, "  {0} = {0}__init();", c_name(name))?;
        }
        writeln!(out, "}}\n")?;

        // The GC's global-root table: the address of every top-level Value the
        // collector must keep. Builtins are rooted inside the runtime, so only
        // user globals and foreign closures go here. A one-element `{0}` avoids a
        // zero-length array when the program has no top-level values of its own.
        let root_names = self
            .globals
            .iter()
            .map(|b| &b.name)
            .filter(|name| !is_builtin(name))
            .chain(self.foreign.iter())
            .collect::<Vec<_>>();
        writeln!(out, "Value *const gc_user_roots[] = {{")?;
        if root_names.is_empty() {
            writeln!(out, "  0")?;
        } else {
            for name in &root_names {
                writeln!(out, "  &{},", c_name(name))?;
            }
        }
        writeln!(out, "}};")?;
        writeln!(
            out,
            "const size_t gc_user_roots_count = {};\n",
            root_names.len()
        )?;

        writeln!(out, "int main(void) {{")?;
        writeln!(out, "  int gc_anchor;")?;
        writeln!(out, "  gc_init(&gc_anchor);")?;
        writeln!(out, "  runtime_init();")?;
        writeln!(out, "  startup();")?;
        write!(out, "  ")?;
        self.compile_expr(&self.start, out)?;
        writeln!(out, ";")?;
        writeln!(out, "  return 0;\n}}")?;
        Ok(())
    }

    // Compile an expression to a single C expression of type `Value`. Control
    // constructs stay expressions: `if` is a ternary, `let` a GCC statement
    // expression, sequencing the comma operator.
    fn compile_expr(&self, expr: &Expr, code: &mut CodeBuffer) -> fmt::Result {
        match expr {
            Expr::Variable(_, the) => write!(code, "{}", self.compile_var(the)),
            Expr::InvokeBridge(_, the) => write!(code, "{}", c_name(&the.qualified_name)),
            Expr::Constant(_, the) => write!(code, "{}", self.compile_constant(the)),
            Expr::RecursiveLambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Lambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Apply(_, the) => self.compile_apply(the, code),
            Expr::Let(_, the) => self.compile_let(the, code),
            Expr::Tuple(_, the) => self.compile_tuple(&the.elements, code),
            Expr::Record(_, the) => self.compile_record(the, code),
            Expr::Inject(_, the) => self.compile_inject(the, code),
            Expr::Project(_, the) => self.compile_projection(the, code),
            Expr::Sequence(_, the) => self.compile_sequence(the, code),
            Expr::Deconstruct(_, the) => self.compile_deconstruct(the, code),
            Expr::If(_, the) => self.compile_if(the, code),
            Expr::Interpolate(_, the) => self.compile_interpolate(&the.0, code),
            Expr::Ascription(_, the) => self.compile_expr(&the.ascribed_tree, code),
            Expr::MakeClosure(_, the) => self.compile_closure(the, code),
        }
    }

    fn compile_tuple(&self, elements: &[std::rc::Rc<Expr>], code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "mk_tuple({}", elements.len())?;
        for element in elements {
            write!(code, ", ")?;
            self.compile_expr(element, code)?;
        }
        write!(code, ")")
    }

    // A constructor value (sum type) is a `Data` object: an integer tag (the
    // constructor's ordinal within its type) followed by its arguments inline.
    // Pattern matching compares the tag with `==` (see `Coproduct` below), so the
    // tag need only be unique among its own type's constructors. Nullary
    // constructors are just a tag with no fields.
    fn compile_inject(&self, the: &phase::Injection<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        write!(
            code,
            "mk_data({}, {}",
            self.constructor_tag(&the.constructor),
            the.arguments.len()
        )?;
        for argument in &the.arguments {
            write!(code, ", ")?;
            self.compile_expr(argument, code)?;
        }
        write!(code, ")")
    }

    // The runtime tag for a constructor: its position within its sum type's
    // constructor list, recorded by `lambda_lift`. Every `Inject`/`Coproduct`
    // names a real sum-type constructor, so a miss is a compiler invariant break.
    fn constructor_tag(&self, constructor: &QualifiedName) -> u64 {
        *self
            .constructor_tags
            .get(constructor)
            .unwrap_or_else(|| panic!("no constructor tag for {constructor}"))
    }

    // A record is a positional product, exactly like a tuple: its fields are
    // held in a canonical order (sorted by name at construction) and projection
    // is already lowered to `Ordinal`, so the field labels carry no runtime
    // weight -- we just emit the values in field order.
    fn compile_record(&self, the: &phase::Record<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "mk_tuple({}", the.fields.len())?;
        for (_label, value) in &the.fields {
            write!(code, ", ")?;
            self.compile_expr(value, code)?;
        }
        write!(code, ")")
    }

    fn compile_projection(
        &self,
        the: &phase::Projection<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        match &the.select {
            ProductElement::Ordinal(i) => {
                write!(code, "proj(")?;
                self.compile_expr(&the.base, code)?;
                write!(code, ", {i})")
            }
            // Record projections are lowered to ordinals before codegen.
            ProductElement::Name(_id) => panic!("named projections are lowered to ordinals"),
        }
    }

    // `deconstruct scrutinee into <clauses>` compiles to a right-nested ternary
    // over the clauses: each clause's refutable tests (guarding its position in
    // the product/coproduct) gate a statement expression that binds its pattern
    // variables and yields the consequent. The scrutinee is evaluated once into a
    // fresh temporary. An exhausted match hits the runtime's `match_fail`.
    fn compile_deconstruct(
        &self,
        the: &phase::Deconstruct<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        let scrutinee = format!("_scrut{id}");

        write!(code, "({{ Value {scrutinee} = ")?;
        self.compile_expr(&the.scrutinee, code)?;
        write!(code, "; ")?;

        for clause in &the.match_clauses {
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            self.collect_pattern(&clause.pattern, &scrutinee, &mut tests, &mut binds);

            if tests.is_empty() {
                write!(code, "true")?;
            } else {
                write!(code, "{}", tests.join(" && "))?;
            }
            write!(code, " ? ({{ ")?;
            for (level, path) in &binds {
                write!(code, "Value l{level} = {path}; ")?;
            }
            self.compile_expr(&clause.consequent, code)?;
            write!(code, "; }}) : ")?;
        }

        write!(code, "match_fail(); }})")
    }

    // Walk a pattern against a C expression `path` for the value it matches,
    // accumulating boolean `tests` (the refutable checks) and `binds` (each
    // pattern variable's `Local` slot paired with the path that reaches it).
    fn collect_pattern(
        &self,
        pattern: &phase::Pattern<Closed>,
        path: &str,
        tests: &mut Vec<String>,
        binds: &mut Vec<(usize, String)>,
    ) {
        match pattern {
            Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => {
                binds.push((*level, path.to_owned()));
            }
            Pattern::Bind(_, other) => panic!("pattern binder must be a local: {other:?}"),

            Pattern::Literally(_, literal) => {
                tests.push(format!("val_eq({path}, {})", self.compile_constant(literal)));
            }

            Pattern::Tuple(_, the) => {
                for (index, element) in the.elements.iter().enumerate() {
                    self.collect_pattern(element, &format!("proj({path}, {index})"), tests, binds);
                }
            }

            Pattern::Struct(_, the) => {
                for (index, (_label, field)) in the.fields.iter().enumerate() {
                    self.collect_pattern(field, &format!("proj({path}, {index})"), tests, binds);
                }
            }

            // A constructor pattern: test the integer tag against the
            // constructor's ordinal, then match each argument against field `i`
            // (mirroring `compile_inject`'s layout).
            Pattern::Coproduct(_, the) => {
                let Identifier::Global(constructor) = &the.constructor else {
                    panic!("constructor pattern head must be a global: {:?}", the.constructor);
                };
                tests.push(format!("data_tag({path}) == {}", self.constructor_tag(constructor)));
                for (index, argument) in the.arguments.iter().enumerate() {
                    self.collect_pattern(
                        argument,
                        &format!("data_field({path}, {index})"),
                        tests,
                        binds,
                    );
                }
            }
        }
    }

    // Application. A saturated application of a primitive builtin lowers to a
    // direct call (`prim_add(x, y)`) -- no intermediate closures, no allocation,
    // no indirection. Everything else is the uniform `apply(closure, argument)`;
    // since a builtin's value is still a curried closure, partial application
    // and higher-order use fall through to this path unchanged.
    fn compile_apply(&self, the: &phase::Apply<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        // Flatten the application spine into (head, args-in-order).
        let mut args: Vec<&Expr> = vec![&the.argument];
        let mut head: &Expr = &the.function;
        while let Expr::Apply(_, inner) = head {
            args.push(&inner.argument);
            head = &inner.function;
        }
        args.reverse();

        if let Some((prim, arity)) = builtin_prim(head) {
            if arity == args.len() {
                write!(code, "{prim}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(code, ", ")?;
                    }
                    self.compile_expr(arg, code)?;
                }
                return write!(code, ")");
            }
        }

        // A *saturated* application of a known-arity function (currently the
        // foreign functions) lowers to a direct call to its uncurried worker --
        // no intermediate closures, no allocation. Under- or over-saturated calls
        // fall through to the curried `apply` path below.
        if let Expr::Variable(_, Identifier::Global(qualified_name)) = head {
            if self.arities.get(qualified_name.as_ref()) == Some(&args.len()) {
                write!(code, "{}_worker(", c_name(qualified_name.as_ref()))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(code, ", ")?;
                    }
                    self.compile_expr(arg, code)?;
                }
                return write!(code, ")");
            }
        }

        // Generic path. A multi-argument application of an unknown head (a curried
        // function *value*, e.g. a parameter passed to a higher-order function)
        // goes through `apply_n`, which dispatches straight to the head's
        // uncurried worker when it carries one and is saturated -- skipping the
        // intermediate currying-stage closures -- and otherwise falls back to
        // applying one argument at a time. A single-argument application has no
        // stage to skip, so it stays the leaner `apply`.
        if args.len() >= 2 {
            write!(code, "apply_n(")?;
            self.compile_expr(head, code)?;
            write!(code, ", {}, (Value[]){{", args.len())?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(code, ", ")?;
                }
                self.compile_expr(arg, code)?;
            }
            return write!(code, "}})");
        }

        write!(code, "apply(")?;
        self.compile_expr(&the.function, code)?;
        write!(code, ", ")?;
        self.compile_expr(&the.argument, code)?;
        write!(code, ")")
    }

    // A closure value: the lifted function's code paired with a freshly built
    // environment tuple of its captured values. When the closure is the head of a
    // non-recursive curried chain, it also carries its uncurried worker and arity
    // (via `mk_closure_n`), so a saturated `apply_n` runs the chain in one flat
    // frame instead of allocating a currying closure per stage.
    fn compile_closure(&self, the: &ClosureInfo, code: &mut CodeBuffer) -> fmt::Result {
        // The captured values live inline in the closure (a "flat" closure), so
        // emit them directly as arguments to `mk_closure`/`mk_closure_n` -- one
        // heap object, no separate environment tuple. The closure-conversion pass
        // always builds the environment as a tuple, whose elements are exactly the
        // captures in slot order.
        let Expr::Tuple(_, env) = the.environment.as_ref() else {
            panic!("closure environment is always a tuple");
        };
        let name = c_name(&the.lifted_name);
        if let Some(&arity) = self.chain_heads.get(&the.lifted_name) {
            write!(
                code,
                "mk_closure_n({name}, {name}_uworker, {arity}, {}",
                env.elements.len()
            )?;
        } else {
            write!(code, "mk_closure({name}, {}", env.elements.len())?;
        }
        for element in &env.elements {
            write!(code, ", ")?;
            self.compile_expr(element, code)?;
        }
        write!(code, ")")
    }

    // String interpolation concatenates its segments: literal text verbatim,
    // embedded expressions rendered through `prim_show` (matching the Scheme
    // backend's `string-append` + `show`).
    fn compile_interpolate(
        &self,
        segments: &[Segment<CaptureInfo, Identifier>],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(code, "prim_str_concat({}", segments.len())?;
        for segment in segments {
            write!(code, ", ")?;
            match segment {
                Segment::Literal(_, literal) => write!(code, "{}", self.compile_constant(literal))?,
                Segment::Expression(expr) => {
                    write!(code, "prim_show(")?;
                    self.compile_expr(expr, code)?;
                    write!(code, ")")?;
                }
            }
        }
        write!(code, ")")
    }

    fn compile_sequence(
        &self,
        the: &phase::Sequence<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(code, "(")?;
        self.compile_expr(&the.this, code)?;
        write!(code, ", ")?;
        self.compile_expr(&the.and_then, code)?;
        write!(code, ")")
    }

    fn compile_if(&self, the: &phase::IfThenElse<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "(as_bool(")?;
        self.compile_expr(&the.predicate, code)?;
        write!(code, ") ? ")?;
        self.compile_expr(&the.consequent, code)?;
        write!(code, " : ")?;
        self.compile_expr(&the.alternate, code)?;
        write!(code, ")")
    }

    fn compile_var(&self, var: &Identifier) -> String {
        match var {
            Identifier::Local(LexicalLevel(level)) => format!("l{level}"),
            Identifier::Captured(capture) => format!("env_get(self, {})", capture.index()),
            Identifier::SelfRef => "self".to_owned(),
            Identifier::Global(qualified_name) => c_name(qualified_name),
        }
    }

    fn compile_constant(&self, the: &Literal) -> String {
        match the {
            Literal::Int(x) => format!("VInt({x})"),
            Literal::Text(x) => format!("VText(\"{x}\")"),
            Literal::Bool(x) => format!("VBool({x})"),
            Literal::Unit => "VUnit()".to_owned(),
            Literal::Char(x) => format!("VChar('{x}')"),
        }
    }

    // `let l = bound in body` is a GCC statement expression: bind a local, then
    // yield the body's value. Only `Local` binders occur here (see closed.rs).
    fn compile_let(
        &self,
        Binding {
            binder,
            bound,
            body,
            ..
        }: &phase::Binding<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let Identifier::Local(LexicalLevel(level)) = binder else {
            panic!("let binder is always a local: {binder:?}");
        };
        write!(code, "({{ Value l{level} = ")?;
        self.compile_expr(bound, code)?;
        write!(code, "; ")?;
        self.compile_expr(body, code)?;
        write!(code, "; }})")
    }
}
