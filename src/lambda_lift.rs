use std::{
    collections::HashMap,
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::{
        Apply, Literal,
        namer::{QualifiedName, Symbol, SymbolName},
        pattern::MatchClause,
    },
    closed::{self, CaptureInfo, Closed, Expr, Identifier, LexicalLevel},
    parser::{self, IdentifierPath},
    phase,
    typer::TypeInfo,
};

impl closed::SymbolTable {
    // `order` is the dependency-resolvable order of the symbols (computed on the
    // pre-closure table, where the dependency matrix lives). Globals are emitted
    // in it so that a top-level definition whose value is *eagerly* evaluated
    // (e.g. `reverse := fold_left (flip Cons) Nil`) is initialised only after the
    // globals it reads -- the same static-init order the interpreter uses.
    pub fn lambda_lift(mut self, order: &[SymbolName]) -> Program {
        // Two distinct outputs: `functions` are the hoisted anonymous lambdas
        // (code taking env + parameter), while `globals` are the top-level
        // definitions themselves (each a value expression -- typically a
        // `MakeClosure` -- evaluated once). Codegen emits the former as C
        // functions and the latter as initialized C globals; the distinction is
        // erased if both share one list, so keep them apart.
        let mut functions = Vec::default();
        let mut globals = Vec::default();

        // `in_resolvable_order` (whence `order` comes) lists every symbol, so we
        // just walk it and pull each out -- the same idiom the interpreter and
        // the Chez backend use. Names in `order` with no term symbol here
        // (constraint methods, foreign terms) simply aren't found.
        for name in order {
            let Some(Symbol::Term(term)) = self.symbols.remove(name) else {
                continue;
            };
            let SymbolName::Term(name) = name.clone() else {
                continue;
            };
            let mut crane = Crane::new(term.name.clone());
            let type_info = term.body.annotation().type_info.clone();
            let lifted = crane.lift_lambdas(term.body);
            functions.extend(lifted.functions);
            globals.push(TopLevelBinding {
                name,
                value: lifted.body,
                type_info,
            });
        }

        // Foreign terms have no body to lift, so they never enter `globals`
        // above (their symbol isn't a `Term` with an expression). Carry their
        // names through so codegen can declare, initialise, and root the C
        // globals that the companion `<Module>.c` file defines.
        let foreign = self
            .foreign_terms
            .iter()
            .map(|ext| ext.name.clone())
            .collect();

        // Known-arity table for direct (uncurried) saturated calls. Foreign
        // functions have their arity in the declared type's arrow count; a
        // saturated application of one lowers to a direct `<name>_worker(args)`
        // instead of the allocating curried `apply` chain (see codegen).
        let mut arities: HashMap<QualifiedName, usize> = self
            .foreign_terms
            .iter()
            .map(|ext| (ext.name.clone(), ext.type_signature.body.arrow_arity()))
            .collect();

        // Uncurried workers for top-level user functions (records their arity in
        // `arities` too, so codegen direct-calls them like the foreign ones).
        let workers = synthesize_workers(&functions, &globals, &mut arities);

        Program {
            functions,
            globals,
            foreign,
            arities,
            workers,
            start: Expr::Apply(
                CaptureInfo::dummy(),
                Apply {
                    function: Expr::Variable(
                        CaptureInfo::dummy(),
                        Identifier::Global(
                            QualifiedName::from_root_symbol(parser::Identifier::from_str("start"))
                                .into(),
                        ),
                    )
                    .into(),
                    argument: Expr::Constant(CaptureInfo::dummy(), Literal::Unit).into(),
                },
            ),
        }
    }
}

// True for the environment of a top-level function's closure -- an empty tuple,
// meaning the function captures nothing (all its inner-stage captures are then
// its own threaded parameters, which is what makes the flat remap sound).
fn is_empty_env(env: &Expr) -> bool {
    matches!(env, Expr::Tuple(_, tuple) if tuple.elements.is_empty())
}

// Peel any type ascriptions off a top-level binding's value; they are erased at
// codegen and merely wrap the closure a function definition evaluates to.
fn strip_ascription(mut expr: &Expr) -> &Expr {
    while let Expr::Ascription(_, ascription) = expr {
        expr = &ascription.ascribed_tree;
    }
    expr
}

// How the self-value is spelled in the *current* curry stage's frame as we
// descend the chain. A recursive top-level function threads its own closure
// inward as a capture whose ultimate source is `SelfRef`: at the recursive origin
// (the outermost lifted stage) it is `SelfRef`; every stage below re-captures it,
// so there it is `Captured(k)`. Following it inward tells us which of the
// innermost captures is the self-reference.
enum SelfMarker {
    Origin,
    Capture(usize),
}

// Position, within one stage's environment tuple, of the element that forwards
// the self-value to the next (inner) stage -- i.e. the inner stage's self-capture
// index. `None` if this stage does not forward self inward (the function then
// does not recurse through to that stage).
fn forwarded_self(stage_env: &Expr, marker: &SelfMarker) -> Option<usize> {
    let Expr::Tuple(_, tuple) = stage_env else {
        return None;
    };
    tuple.elements.iter().position(|element| {
        match (marker, element.as_ref()) {
            (SelfMarker::Origin, Expr::Variable(_, Identifier::SelfRef)) => true,
            (SelfMarker::Capture(k), Expr::Variable(_, Identifier::Captured(c))) => c.index() == *k,
            _ => false,
        }
    })
}

// The remap that flattens the innermost stage's frame into the N-ary worker
// frame. `targets[c]` is where capture index `c` lands: an argument-order local
// for a captured outer parameter, or -- for the self-capture of a recursive
// function -- the function's own `Global`, so a *saturated* self-call lowers to a
// direct `<name>_worker(..)` (via `compile_apply`) while a self-value use falls
// back to the curried global closure. `shift` (= N-1) pushes the stage's own
// parameter and inner binders above the N flattened parameters.
struct FrameRemap<'a> {
    targets: &'a [Identifier],
    shift: usize,
    name: &'a QualifiedName,
}

impl FrameRemap<'_> {
    fn fix_id(&self, id: Identifier) -> Identifier {
        match id {
            Identifier::Captured(c) => self.targets[c.index()].clone(),
            Identifier::Local(LexicalLevel(level)) => {
                Identifier::Local(LexicalLevel(level + self.shift))
            }
            // A bare `SelfRef` refers to this same function; map it to the global
            // too. (In practice the self-value always reaches the innermost frame
            // as a capture, never as a bare `SelfRef`, for arity >= 2 -- but this
            // keeps a stray one from leaking into a worker that has no `self`.)
            Identifier::SelfRef => Identifier::Global(Box::new(self.name.clone())),
            other => other,
        }
    }

    // Flatten the frame. `Expr::map` does not descend into `MakeClosure`
    // environments, so we remap those explicitly (recursively) -- otherwise a
    // nested closure built inside the body would still read its captures via
    // `env_get(self, ..)`, referencing a `self` the worker doesn't have.
    fn flatten(&self, body: Expr) -> Expr {
        body.map(&mut |e| match e {
            Expr::Variable(a, id) => Expr::Variable(a, self.fix_id(id)),
            Expr::Let(a, mut binding) => {
                binding.binder = self.fix_id(binding.binder);
                Expr::Let(a, binding)
            }
            Expr::Deconstruct(a, mut deconstruct) => {
                deconstruct.match_clauses = deconstruct
                    .match_clauses
                    .into_iter()
                    .map(|clause| MatchClause {
                        pattern: clause.pattern.map_id(&|id| self.fix_id(id)),
                        consequent: clause.consequent,
                    })
                    .collect();
                Expr::Deconstruct(a, deconstruct)
            }
            Expr::MakeClosure(a, mut info) => {
                info.environment = Box::new(self.flatten((*info.environment).clone()));
                Expr::MakeClosure(a, info)
            }
            other => other,
        })
    }
}

// Build an uncurried worker for each top-level function that is a closure-free
// curried chain of arity >= 2, whether or not it recurses. Follows the chain of
// curry-stage `MakeClosure`s to the innermost lifted function -- tracking the
// self-value inward -- then flattens its frame. A recursive self-call becomes a
// direct worker call; a self-value use stays the curried global closure.
fn synthesize_workers(
    functions: &[LiftedFunction],
    globals: &[TopLevelBinding],
    arities: &mut HashMap<QualifiedName, usize>,
) -> Vec<Worker> {
    let fn_index: HashMap<&QualifiedName, usize> = functions
        .iter()
        .enumerate()
        .map(|(i, f)| (&f.name, i))
        .collect();

    let mut workers = Vec::new();
    for binding in globals {
        let Expr::MakeClosure(_, stage0) = strip_ascription(&binding.value) else {
            continue;
        };
        // Top-level functions are all wrapped in `RecursiveLambda` (their own name
        // is in scope in the body), so `stage0.is_recursive` is not a reliable
        // "actually recurses" signal -- we discover real recursion below by
        // tracking the self-value down the chain. Only the empty environment
        // (closure-free) matters here.
        if !is_empty_env(&stage0.environment) {
            continue;
        }

        // Walk the curry-stage chain to the innermost lifted function, following
        // the self-value inward so we learn which innermost capture is the
        // self-reference (`self_capture`), if the function recurses.
        let mut current = &stage0.lifted_name;
        let mut arity = 1usize;
        let mut marker = Some(SelfMarker::Origin);
        let mut self_capture: Option<usize> = None;
        while let Some(&idx) = fn_index.get(current) {
            match &functions[idx].code {
                Expr::MakeClosure(_, stage)
                    if !stage.is_recursive && fn_index.contains_key(&stage.lifted_name) =>
                {
                    self_capture = marker
                        .as_ref()
                        .and_then(|m| forwarded_self(&stage.environment, m));
                    marker = self_capture.map(SelfMarker::Capture);
                    current = &stage.lifted_name;
                    arity += 1;
                }
                _ => break,
            }
        }
        if arity < 2 {
            continue;
        }

        let inner = &functions[fn_index[current]];
        let levels = inner
            .capture_info
            .layout
            .as_ref()
            .map(closed::CaptureLayout::captured_levels)
            .unwrap_or(&[]);

        // Setting the self-capture aside, the innermost stage must capture exactly
        // the N-1 outer parameters -- no unused parameters, no genuine free
        // variables -- or the flat remap would be unsound; leave those curried.
        let params: Vec<usize> = (0..levels.len())
            .filter(|i| Some(*i) != self_capture)
            .collect();
        if params.len() != arity - 1 {
            continue;
        }

        // Argument order is ascending lexical level (the outermost parameter is
        // bound first), so sort the parameter captures to recover each one's slot.
        let mut ordered = params;
        ordered.sort_by_key(|&i| levels[i].0);
        let mut targets = vec![Identifier::SelfRef; levels.len()];
        for (slot, &i) in ordered.iter().enumerate() {
            targets[i] = Identifier::Local(LexicalLevel(slot));
        }
        if let Some(self_index) = self_capture {
            targets[self_index] = Identifier::Global(Box::new(binding.name.clone()));
        }

        let remap = FrameRemap {
            targets: &targets,
            shift: arity - 1,
            name: &binding.name,
        };
        let body = remap.flatten(inner.code.clone());
        arities.insert(binding.name.clone(), arity);
        workers.push(Worker {
            name: binding.name.clone(),
            params: arity,
            body,
        });
    }
    workers
}

#[derive(Debug)]
struct Crane {
    target_module: IdentifierPath,
    lifted: Vec<LiftedFunction>,
}

struct Lifting {
    functions: Vec<LiftedFunction>,
    body: Expr,
}

static FRESH_LAMBDA_ID: AtomicU32 = AtomicU32::new(0);

impl Crane {
    fn new(name: QualifiedName) -> Self {
        Self {
            target_module: name.module().clone(),
            lifted: Vec::default(),
        }
    }

    fn fresh_name(&self) -> QualifiedName {
        QualifiedName::new(
            self.target_module.clone(),
            &format!("lambda_{}", FRESH_LAMBDA_ID.fetch_add(1, Ordering::Relaxed)),
        )
    }

    fn lift_lambdas(&mut self, body: Expr) -> Lifting {
        let mut functions = Vec::default();
        let body = body.map(&mut |e| match e {
            Expr::Lambda(capture_info, lambda) => {
                let name = self.fresh_name();

                tracing::trace!(
                    "lift_lambdas: {name} has type {}",
                    capture_info.type_info.inferred_type
                );

                functions.push(LiftedFunction::from_lambda(
                    capture_info.clone(),
                    name.clone(),
                    lambda,
                ));

                Expr::MakeClosure(
                    capture_info.clone(),
                    ClosureInfo {
                        environment: capture_info.make_environment_tuple().into(),
                        lifted_name: name,
                        is_recursive: false,
                    },
                )
            }

            Expr::RecursiveLambda(capture_info, self_ref) => {
                let lambda_name = self.fresh_name();

                tracing::trace!(
                    "lift_lambdas: rec {lambda_name} has type {}",
                    capture_info.type_info.inferred_type
                );

                // Self-references stay `Identifier::SelfRef` in the body; codegen
                // resolves them against this lifted function (recursive call, or a
                // reconstructed closure over the env parameter). Free variables are
                // already explicit as `Captured`, so the body needs no rewriting --
                // lifting is now pure hoisting.
                functions.push(LiftedFunction::from_lambda(
                    capture_info.clone(),
                    lambda_name.clone(),
                    self_ref.lambda,
                ));

                Expr::MakeClosure(
                    capture_info.clone(),
                    ClosureInfo {
                        environment: capture_info.make_environment_tuple().into(),
                        lifted_name: lambda_name,
                        is_recursive: true,
                    },
                )
            }

            otherwise => otherwise,
        });

        Lifting { functions, body }
    }
}

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub environment: Box<Expr>,
    pub lifted_name: QualifiedName,
    pub is_recursive: bool,
}

#[derive(Debug, Clone)]
pub struct Program {
    /// Hoisted anonymous lambdas -- each is code taking an environment and a
    /// parameter, emitted as a C function.
    pub functions: Vec<LiftedFunction>,
    /// Top-level definitions -- each a value expression evaluated once, emitted
    /// as an initialized C global.
    pub globals: Vec<TopLevelBinding>,
    /// Foreign functions: names only, no body. Their curried closures are built
    /// by a companion `<Module>.c` (via the `FOREIGN_DECL` macro); codegen emits
    /// the matching `extern` global, its `startup` initialiser, and its GC root.
    pub foreign: Vec<QualifiedName>,
    /// Known-arity functions, for direct saturated calls (`<name>_worker(args)`
    /// instead of the curried `apply` chain) -- the foreign functions plus the
    /// top-level user functions that have a `workers` entry.
    pub arities: HashMap<QualifiedName, usize>,
    /// Uncurried workers for the user functions in `arities`.
    pub workers: Vec<Worker>,
    pub start: Expr,
}

/// A top-level definition (`name := value`). For a function definition `value`
/// is a `MakeClosure` over one of the lifted `functions`; for a data definition
/// it is a constant or other value expression.
#[derive(Debug, Clone)]
pub struct TopLevelBinding {
    pub name: QualifiedName,
    pub value: Expr,
    pub type_info: TypeInfo,
}

#[derive(Debug, Clone)]
pub struct LiftedFunction {
    pub name: QualifiedName,
    pub code: Expr,
    pub capture_info: CaptureInfo,
}

/// An uncurried N-ary "worker" for a top-level, closure-free function of arity
/// `params` >= 2 (recursive or not). Its `body` references the parameters as the
/// flat frame `Local(0..params-1)` (in argument order) and inner binders from
/// `Local(params)`; a recursive self-call appears as a saturated application of
/// the function's own `Global`. Codegen emits `Value <name>_worker(Value l0, ..,
/// Value l{params-1})` and `compile_apply` direct-calls it at saturated call
/// sites (including the self-call), skipping the curried `apply` chain. The
/// curried closure (the global binding) is kept for partial application, for
/// higher-order use, and for self-*value* references within the body.
#[derive(Debug, Clone)]
pub struct Worker {
    pub name: QualifiedName,
    pub params: usize,
    pub body: Expr,
}

impl LiftedFunction {
    fn from_lambda(
        capture_info: CaptureInfo,
        name: QualifiedName,
        lambda: phase::Lambda<Closed>,
    ) -> Self {
        Self {
            name,
            code: Rc::unwrap_or_clone(lambda.body),
            capture_info,
        }
    }
}

impl fmt::Display for ClosureInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            environment,
            lifted_name,
            is_recursive,
        } = self;
        write!(
            f,
            "ClosureInfo: {} {lifted_name} [{}] ",
            *environment,
            if *is_recursive { "rec" } else { "" }
        )
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            functions,
            globals,
            foreign,
            arities: _,
            workers: _,
            start,
        } = self;

        for function in functions {
            writeln!(f, "{function}")?;
        }

        for global in globals {
            writeln!(f, "{global}")?;
        }

        for name in foreign {
            writeln!(f, "foreign {name}")?;
        }

        writeln!(f, "start: {start}")
    }
}

impl fmt::Display for TopLevelBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            value,
            type_info,
        } = self;
        write!(f, "global {name}::{} = {value}", type_info.inferred_type)
    }
}

impl fmt::Display for LiftedFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            code,
            capture_info,
        } = self;
        let ty = &capture_info.type_info.inferred_type;
        write!(f, "lifted => {name}::{ty} --- {code}")
    }
}
