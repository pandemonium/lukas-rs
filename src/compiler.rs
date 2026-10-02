use std::{fmt, fs, io, path::PathBuf, rc::Rc};

use clap::Parser;
use thiserror::Error;

use crate::{
    ast::{
        self, ROOT_MODULE_NAME,
        namer::{self, NameError},
    },
    chez,
    codegen::{CEntryPoint, CodeBuffer},
    interpreter::{
        self, Environment, Literal, RuntimeError,
        cek::{Env, Globals, Val},
    },
    lexer::LexicalAnalyzer,
    parser::{self, ParseError, ParseInfo, Parsed},
    phase, requirements, source_map,
    typer::{Elaborated, TypeError, TypeErrors, Types},
};

pub type CompilationUnit = ast::CompilationUnit<ParseInfo>;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("parse error in {}: {error}", .path.display())]
    ParseError { path: PathBuf, error: ParseError },

    /// A file with more than one syntax error in it. The parser resynchronises on
    /// the next declaration, so one broken line no longer hides the next.
    #[error("parse error in {}: {}", .path.display(), first(errors))]
    ParseErrors {
        path: PathBuf,
        errors: Vec<ParseError>,
    },

    #[error("name error: {0}")]
    NameError(#[from] Located<NameError>),

    /// Name resolution ran over every declaration and found several. Declarations
    /// are independent, so one unresolved name does not hide the next.
    #[error("name error: {}", first_name_error(.0))]
    NameErrors(Vec<Located<NameError>>),

    #[error("type error: {0}")]
    TypeError(#[from] Located<TypeError>),

    /// Elaboration ran to the end and found several. Terms are typed independently,
    /// so one failing does not hide the next.
    #[error("type error: {0}")]
    TypeErrors(#[from] TypeErrors),

    #[error("interpretation error: {0}")]
    InterpretationError(#[from] RuntimeError),

    #[error("I/O error: {0}")]
    IO(#[from] io::Error),

    #[error("code generation error: {0}")]
    Chez(#[from] chez::ChezError),

    #[error(
        "the root module (Root.lady) must define an entry point `start` \
         (e.g. `start := λ_. ...`), but none was found"
    )]
    MissingStart,

    #[error("unsatisfied dependencies -- a name is referenced but never defined:\n{0}")]
    UnsatisfiedDependencies(String),

    #[error("cannot load module `{name}`: no source file found at {}", .path.display())]
    MissingModule { name: String, path: PathBuf },

    #[error("the {profile:?} execution profile is not supported by the {backend:?} backend")]
    UnsupportedExecutionProfile {
        backend: Backend,
        profile: ExecutionProfile,
    },

    #[error("requirements cannot be satisfied for {platform}:\n{report}")]
    UnsatisfiedRequirements {
        platform: requirements::Platform,
        report: String,
    },

    #[error("cannot load capability model `{path}`: {message}", path = .path.display())]
    CapabilityModel { path: PathBuf, message: String },
}

/// Format the unresolved edges of a dependency graph into an error naming which
/// symbol depends on which undefined name.
fn bad_dependencies(deps: &namer::DependencyMatrix<namer::SymbolName>) -> CompilationError {
    let report = deps
        .unsatisfied()
        .iter()
        .map(|(from, dep)| format!("  `{from}` depends on `{dep}`, which is not defined"))
        .collect::<Vec<_>>()
        .join("\n");
    CompilationError::UnsatisfiedDependencies(report)
}

#[derive(Debug, Error)]
pub struct Located<E>
where
    E: fmt::Debug,
{
    pub parse_info: ParseInfo,
    pub error: Box<E>,
}

/// The error a terminal shows when a file has several: the first, plus a count.
fn first(errors: &[ParseError]) -> String {
    match errors.split_first() {
        Some((first, [])) => first.to_string(),
        Some((first, rest)) => format!("{first}\n(and {} more)", rest.len()),
        None => "parse error".to_owned(),
    }
}

/// What a list of name errors says when only one line is available for it.
fn first_name_error(errors: &[Located<NameError>]) -> String {
    match errors.split_first() {
        Some((first, [])) => first.to_string(),
        Some((first, rest)) => format!("{first}\n(and {} more)", rest.len()),
        None => "no name errors".to_owned(),
    }
}

pub trait LocatedError
where
    Self: Sized + fmt::Debug,
{
    fn at(self, pi: ParseInfo) -> Located<Self> {
        Located {
            parse_info: pi,
            error: self.into(),
        }
    }
}

impl<T> LocatedError for T where T: fmt::Debug {}

pub type Compilation<A = CompilationUnit> = Result<A, CompilationError>;

/// Which on-disk artifact a module name resolves to. Both are located with the
/// same source-then-`--library` search; they differ only in file extension.
#[derive(Clone, Copy, Debug)]
pub enum Artifact {
    /// The Marmelade source module: `<Name>.lady`.
    Module,
    /// A backend-provided implementation of a module's foreign functions: `<Name>.ss`.
    Foreign,
}

impl Artifact {
    const fn extension(self) -> &'static str {
        match self {
            Self::Module => "lady",
            Self::Foreign => "ss",
        }
    }
}

/// Which code generator `mc` runs, and therefore what language it emits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum Backend {
    /// Emit Chez Scheme source (the default).
    #[default]
    Scheme,
    /// Emit C source. The execution profile determines the downstream environment.
    Native,
}

/// The environment the generated program is intended to execute in.
///
/// This is deliberately independent of [`Backend`]: the native backend emits C,
/// which can later be compiled for more than one execution environment. `Host`
/// preserves the process-oriented runtime and entry point used before profiles
/// were introduced.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum ExecutionProfile {
    #[default]
    Host,
    #[value(name = "native-macos")]
    NativeMacOS,
    #[value(name = "native-linux")]
    NativeLinux,
    #[value(name = "native-windows")]
    NativeWindows,
    #[value(name = "wasm-node")]
    WasmNode,
    /// Run as a WebAssembly module loaded by a browser. `browser` remains an
    /// accepted compatibility spelling for the original two-profile interface.
    #[value(name = "wasm-browser", alias = "browser")]
    WasmBrowser,
}

impl ExecutionProfile {
    pub const fn platform(self) -> requirements::Platform {
        match self {
            Self::Host => requirements::Platform::current_native(),
            Self::NativeMacOS => requirements::Platform::NativeMacOS,
            Self::NativeLinux => requirements::Platform::NativeLinux,
            Self::NativeWindows => requirements::Platform::NativeWindows,
            Self::WasmNode => requirements::Platform::WasmNode,
            Self::WasmBrowser => requirements::Platform::WasmBrowser,
        }
    }

    pub const fn entry_point(self) -> CEntryPoint {
        match self {
            Self::Host | Self::NativeMacOS | Self::NativeLinux | Self::NativeWindows => {
                CEntryPoint::Process
            }
            Self::WasmNode | Self::WasmBrowser => CEntryPoint::Wasm,
        }
    }
}

#[derive(Clone, Debug, Parser)]
pub struct Compiler {
    #[arg(long = "library")]
    pub library_path: PathBuf,

    #[arg(long = "source")]
    pub source_path: PathBuf,

    #[arg(long = "backend", value_enum, default_value_t = Backend::Scheme)]
    pub backend: Backend,

    /// Select the generated program's execution environment independently of its backend.
    #[arg(
        long = "profile",
        value_enum,
        default_value_t = ExecutionProfile::Host
    )]
    pub profile: ExecutionProfile,

    /// Provider graph used by the native backend. Defaults to
    /// `<library>/capabilities.conf`.
    #[arg(long = "capabilities")]
    pub capability_config: Option<PathBuf>,

    /// Write the concrete providers, C defines, and provider-owned sources chosen
    /// for this build. The native build driver consumes this plan.
    #[arg(long = "provider-plan")]
    pub provider_plan: Option<PathBuf>,

    /// Write inferred requirements for every symbol that has any.
    #[arg(long = "requirements-report")]
    pub requirements_report: Option<PathBuf>,

    /// Where to write the emitted source; prints to stdout if omitted.
    #[arg(long = "output", short = 'o')]
    pub output_file: Option<PathBuf>,
}

#[cfg(test)]
mod configuration_tests {
    use super::*;

    #[test]
    fn command_line_defaults_preserve_the_existing_host_configuration() {
        let compiler = Compiler::try_parse_from([
            "mc",
            "--library",
            "ladies/stdlib",
            "--source",
            "ladies/examples/01_literals_and_operators",
        ])
        .expect("the existing command line should remain valid");

        assert_eq!(compiler.backend, Backend::Scheme);
        assert_eq!(compiler.profile, ExecutionProfile::Host);
    }

    #[test]
    fn backend_and_execution_profile_are_independent_arguments() {
        let compiler = Compiler::try_parse_from([
            "mc",
            "--library",
            "ladies/stdlib",
            "--source",
            "ladies/examples/01_literals_and_operators",
            "--backend",
            "native",
            "--profile",
            "host",
        ])
        .expect("backend and execution profile should parse together");

        assert_eq!(compiler.backend, Backend::Native);
        assert_eq!(compiler.profile, ExecutionProfile::Host);
    }

    #[test]
    fn browser_execution_profile_is_available_to_the_native_backend() {
        let compiler = Compiler::try_parse_from([
            "mc",
            "--library",
            "ladies/stdlib",
            "--source",
            "ladies/examples/01_literals_and_operators",
            "--backend",
            "native",
            "--profile",
            "browser",
        ])
        .expect("the browser execution profile should parse");

        assert_eq!(compiler.backend, Backend::Native);
        assert_eq!(compiler.profile, ExecutionProfile::WasmBrowser);
    }

    #[test]
    fn every_explicit_native_target_profile_parses() {
        for (spelling, expected) in [
            ("native-macos", ExecutionProfile::NativeMacOS),
            ("native-linux", ExecutionProfile::NativeLinux),
            ("native-windows", ExecutionProfile::NativeWindows),
            ("wasm-node", ExecutionProfile::WasmNode),
            ("wasm-browser", ExecutionProfile::WasmBrowser),
        ] {
            let compiler = Compiler::try_parse_from([
                "mc",
                "--library",
                "ladies/stdlib",
                "--source",
                "ladies/examples/01_literals_and_operators",
                "--backend",
                "native",
                "--profile",
                spelling,
            ])
            .unwrap_or_else(|error| panic!("profile {spelling} did not parse: {error}"));

            assert_eq!(compiler.profile, expected);
        }
    }
}

impl Compiler {
    pub fn parse_compilation_unit(&self) -> Compilation {
        let module_name = parser::Identifier::from_str(ROOT_MODULE_NAME);
        let mut root_module = self.load_module(&module_name)?;

        // The primordial `Prelude` (Text/Bytes/Buffer/IO + core ADTs) is loaded and opened
        // as a GLOBAL base import by the namer (`import_compilation_unit`), so it is in
        // scope in every file -- not only `Root`. Programs never write `use Prelude`.

        // Every Root.lady must define `start`, the program entry point. Check it
        // here so a missing (or, thanks to a parse desync, dropped) `start` is a
        // clear compile error rather than a `NoSuchSymbol` crash at run time.
        let has_start = matches!(
            &root_module.declarator,
            ast::ModuleDeclarator::Inline(decls) if decls.iter().any(|d| matches!(
                d, ast::Declaration::Value(_, v) if v.name.as_str() == "start"
            ))
        );
        if !has_start {
            Err(CompilationError::MissingStart)?;
        }

        Ok(CompilationUnit {
            root_module,
            compiler: self.clone(),
        })
    }

    pub fn compile_and_initialize(&self) -> Compilation<interpreter::Environment> {
        let program =
            crate::profile::time("pipeline: parse root", || self.parse_compilation_unit())?;
        crate::profile::time("pipeline: typecheck + initialize", || {
            self.typecheck_and_initialize(program)
        })
    }

    pub fn compiler_main(&self) -> Compilation<()> {
        let program =
            crate::profile::time("pipeline: parse root", || self.parse_compilation_unit())?;
        crate::profile::time("pipeline: typecheck + codegen", || {
            self.typecheck_and_compile(program)
        })
    }

    pub fn typecheck_and_initialize(&self, program: CompilationUnit) -> Compilation<Environment> {
        let symbols = crate::profile::time("front end: import modules", || {
            phase::SymbolTable::<Parsed>::import_compilation_unit(program)
        })?;
        let symbols = crate::profile::time("front end: desugar", || symbols.desugar());
        let resolved_symbols =
            crate::profile::time("front end: resolve names", || symbols.resolve_names())
                .map_err(CompilationError::NameErrors)?;

        let dependencies = crate::profile::time("front end: dependency graph", || {
            resolved_symbols.dependency_matrix()
        });

        if dependencies.are_sound() {
            // Shared, live globals: `clone()` shares the underlying map, so a
            // closure captured for an earlier symbol sees symbols defined later
            // (mutually recursive dictionaries / lifted methods).
            let globals = Globals::default();

            let compilation_unit = crate::profile::time("type checker: total", || {
                resolved_symbols.elaborate_compilation_unit()
            })?;

            // The interpreter has no foreign/byte backend (foreigns are provided by the C /
            // Scheme companions). Bind each `foreign` term to a placeholder so a program that
            // merely LOADS the always-imported primordial Prelude -- string literals, module
            // mounting, pure computation -- initialises and runs. A program that actually
            // APPLIES a foreign (real byte work) is a C-backend concern and would error here.
            for foreign in &compilation_unit.foreign_terms {
                globals.define(foreign.name.clone(), Val::Constant(Literal::Unit));
            }

            let deps = compilation_unit.dependency_matrix();
            let evaluation_order = deps.in_resolvable_order();

            for symbol in compilation_unit.terms(evaluation_order.iter()) {
                let value = Rc::new(symbol.body.erase_annotation())
                    .interpret(Env::from_globals(globals.clone()))
                    .unwrap_or_else(|error| {
                        panic!("static initialization of {} failed: {error:?}", symbol.name)
                    });

                globals.define(symbol.name.clone(), value);
            }

            Ok(Env::from_globals(globals))
        } else {
            // Err(CompilationError::Dependencies...)
            Err(bad_dependencies(&dependencies))
        }
    }

    /// The whole front end and nothing else: parse the program, resolve its names,
    /// type-check it. This is what an editor asks for -- there is nothing to emit
    /// when the question is only "is this program well-formed, and if not, where?"
    pub fn check(&self) -> Compilation<phase::SymbolTable<Types>> {
        let program =
            crate::profile::time("pipeline: parse root", || self.parse_compilation_unit())?;
        self.check_compilation_unit(program)
    }

    /// `check` for an already-parsed unit. `typecheck_and_compile` runs this and then
    /// a back end, so what an editor checks and what the compiler compiles cannot
    /// drift apart.
    pub fn check_compilation_unit(
        &self,
        program: CompilationUnit,
    ) -> Compilation<phase::SymbolTable<Types>> {
        self.check_reusing(program, &Elaborated::default())
            .map(|(symbols, _)| symbols)
    }

    /// `check_compilation_unit`, reusing what a previous check of this program
    /// worked out. `warm` carries a digest of the source text every declaration
    /// was elaborated from, so this check decides for itself what is still true --
    /// which after a keystroke is everything but one declaration and its readers.
    /// Returns what the next check can reuse in turn.
    pub fn check_reusing(
        &self,
        program: CompilationUnit,
        warm: &Elaborated,
    ) -> Compilation<(phase::SymbolTable<Types>, Elaborated)> {
        let symbols = crate::profile::time("front end: import modules", || {
            namer::SymbolTable::import_compilation_unit(program)
        })?;
        let symbols = crate::profile::time("front end: desugar", || symbols.desugar());
        let resolved_symbols =
            crate::profile::time("front end: resolve names", || symbols.resolve_names())
                .map_err(CompilationError::NameErrors)?;

        let dependencies = crate::profile::time("front end: dependency graph", || {
            resolved_symbols.dependency_matrix()
        });

        if !dependencies.are_sound() {
            return Err(bad_dependencies(&dependencies));
        }

        let (symbols, reusable) = crate::profile::time("type checker: total", || {
            resolved_symbols.elaborate_compilation_unit_reusing(warm)
        })?;

        Ok((symbols, reusable))
    }

    /// An editor check which types through unresolved term names as `???` while
    /// returning their diagnostics. This supplies inferred types for hover and code
    /// actions without making unresolved names valid in ordinary compilation.
    pub fn check_reusing_unknown_terms(
        &self,
        program: CompilationUnit,
        warm: &Elaborated,
    ) -> Compilation<(
        phase::SymbolTable<Types>,
        Elaborated,
        Vec<Located<NameError>>,
    )> {
        let symbols = crate::profile::time("front end: import modules", || {
            namer::SymbolTable::import_compilation_unit(program)
        })?;
        let symbols = crate::profile::time("front end: desugar", || symbols.desugar());
        let (resolved_symbols, name_errors) =
            crate::profile::time("front end: resolve names", || {
                symbols.resolve_names_recovering_unknown_terms()
            })
            .map_err(CompilationError::NameErrors)?;

        let dependencies = crate::profile::time("front end: dependency graph", || {
            resolved_symbols.dependency_matrix()
        });
        if !dependencies.are_sound() {
            return Err(bad_dependencies(&dependencies));
        }

        let (symbols, reusable) = crate::profile::time("type checker: total", || {
            resolved_symbols.elaborate_compilation_unit_reusing(warm)
        })?;
        Ok((symbols, reusable, name_errors))
    }

    pub fn typecheck_and_compile(&self, program: CompilationUnit) -> Compilation<()> {
        let program = self.check_compilation_unit(program)?;
        // Chez retains its existing foreign-link model. Capability providers are
        // native-backend build inputs and deliberately do not constrain Scheme.
        if self.backend == Backend::Native {
            self.validate_requirements(&program)?;
        }
        // Lower the surface panic while its source annotation is intact. This is a
        // front-end-to-back-end boundary operation: every emitter must receive the
        // same explicit diagnostic arguments, rather than relying on a particular
        // back end to recover them after its own transformations.
        let program =
            crate::profile::time("codegen: panic sites", || program.materialize_panic_sites());

        {
            if std::env::var("DUMP_C").is_ok() {
                // Dependency-resolvable order lives on the pre-closure table;
                // lambda_lift emits globals in it so eager top-level values are
                // initialised after the globals they read.
                let order = program
                    .dependency_matrix()
                    .in_resolvable_order()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                let lifted = program
                    .clone()
                    .simplify()
                    .closure_conversion()
                    .lambda_lift(&order);
                eprintln!("======== LAMBDA-LIFT IR ========\n{lifted}");
                let mut c = CodeBuffer::default();
                let _ = lifted.generate_code_for(&mut c, self.profile.entry_point());
                eprintln!("======== GENERATED C ========\n{c}");
                return Ok(());
            }

            let mut code = CodeBuffer::default();
            match (self.backend, self.profile) {
                (Backend::Scheme, ExecutionProfile::Host) => {
                    // Each module that declares foreign functions gets its `<Module>.ss`
                    // implementation resolved (source-dir first, then --library) and spliced
                    // into the emitted Scheme.
                    let mut foreign_files = Vec::new();
                    let mut seen = std::collections::HashSet::new();
                    for foreign in &program.foreign_terms {
                        let module = &foreign.name.module;
                        if seen.insert(module.clone()) {
                            // A companion foreign file is named by the module's
                            // fully-qualified name: `Root.Stdlib` -> `Root.Stdlib.ss`,
                            // `Root` -> `Root.ss`. This is unambiguous (no collision
                            // between same-named nested modules).
                            foreign_files
                                .push(self.get_source_path(&module.to_string(), Artifact::Foreign));
                        }
                    }
                    crate::profile::time("codegen: emit Scheme", || {
                        program.emit_scheme_code(&mut code, &foreign_files)
                    })?;
                }
                (Backend::Scheme, profile) => {
                    return Err(CompilationError::UnsupportedExecutionProfile {
                        backend: self.backend,
                        profile,
                    });
                }
                (Backend::Native, profile) => {
                    // C has no closures: convert them away and lambda-lift before
                    // emitting. Dependency-resolvable order lives on the pre-closure
                    // table, so eager top-level values initialise after what they read.
                    let program =
                        crate::profile::time("codegen: specialize", || program.specialize());
                    let order = program
                        .dependency_matrix()
                        .in_resolvable_order()
                        .into_iter()
                        .cloned()
                        .collect::<Vec<_>>();
                    // The first pass exposes `unsafe_run_IO` as a force marker. Force-local
                    // worker/wrapper conversion then opens the concrete computation beneath that
                    // marker without changing any top-level IO value, and the second pass removes
                    // the now-adjacent beta/case plumbing. Set `MARM_DEFOREST_IO=0` to retain the
                    // boxed path for diagnosis and A/B measurements.
                    let program = crate::profile::time("codegen: simplify", || program.simplify());
                    let program = if crate::simplify::deforest_io_on() {
                        program.deforest_io().simplify()
                    } else {
                        program
                    };
                    let program = crate::profile::time("codegen: closure conversion", || {
                        program.closure_conversion()
                    });
                    let lifted = crate::profile::time("codegen: lambda lift", || {
                        program.lambda_lift(&order)
                    });
                    crate::profile::time("codegen: emit C", || {
                        lifted.generate_code_for(&mut code, profile.entry_point())
                    })
                    .map_err(io::Error::other)?;
                }
            }

            if let Some(target) = &self.output_file {
                code.write_to_file(target)?;
            } else {
                println!("{}", code);
            }

            Ok(())
        }
    }

    fn validate_requirements(&self, program: &phase::SymbolTable<Types>) -> Compilation<()> {
        let platform = self.profile.platform();
        let model_path = self
            .capability_config
            .clone()
            .unwrap_or_else(|| self.library_path.join("capabilities.conf"));
        let model = requirements::CapabilityModel::load(&model_path).map_err(|error| {
            CompilationError::CapabilityModel {
                path: model_path,
                message: error.to_string(),
            }
        })?;
        let analysis = requirements::infer(program, requirements::root_entry());
        if let Some(path) = &self.requirements_report {
            analysis.write_report(path)?;
        }
        let required = analysis
            .entry_traces
            .iter()
            .map(|trace| trace.requirement.clone())
            .collect::<Vec<_>>();
        let resolution = model.resolve(required, platform);

        if !resolution.is_satisfied() {
            let report = analysis
                .entry_traces
                .iter()
                .filter_map(|trace| {
                    let failure = model
                        .resolve([trace.requirement.clone()], platform)
                        .unsatisfied
                        .into_iter()
                        .next()?;
                    let path = trace
                        .path
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" -> ");
                    Some(format!("  {failure}\n    required through {path}"))
                })
                .collect::<Vec<_>>()
                .join("\n");
            return Err(CompilationError::UnsatisfiedRequirements { platform, report });
        }

        if let Some(path) = &self.provider_plan {
            resolution.write_plan(path)?;
        }
        Ok(())
    }

    pub fn load_module_declarations(
        &self,
        module: &parser::Identifier,
    ) -> Compilation<Vec<ast::Declaration<ParseInfo>>> {
        let source_path = self.get_source_path(module.as_str(), Artifact::Module);
        load_and_parse_module(source_path)
    }

    pub fn load_top_level_module(
        &self,
        name: &str,
    ) -> Compilation<(Vec<ast::Declaration<ParseInfo>>, PathBuf)> {
        let file = self.get_source_path(name, Artifact::Module);
        if fs::exists(&file).unwrap_or(false) {
            let children_dir = file
                .parent()
                .map(|dir| dir.join(name))
                .unwrap_or_else(|| PathBuf::from(name));
            Ok((load_and_parse_module(file)?, children_dir))
        } else {
            Err(CompilationError::MissingModule {
                name: name.to_owned(),
                path: file,
            })
        }
    }

    pub fn load_nested_module(
        &self,
        dir: &std::path::Path,
        name: &str,
    ) -> Compilation<(Vec<ast::Declaration<ParseInfo>>, PathBuf)> {
        let file = dir.join(format!("{}.{}", name, Artifact::Module.extension()));
        if fs::exists(&file).unwrap_or(false) {
            let children_dir = dir.join(name);
            Ok((load_and_parse_module(file)?, children_dir))
        } else {
            Err(CompilationError::MissingModule {
                name: name.to_owned(),
                path: file,
            })
        }
    }

    pub fn load_module(
        &self,
        module: &parser::Identifier,
    ) -> Compilation<ast::ModuleDeclaration<ParseInfo>> {
        Ok(ast::ModuleDeclaration {
            name: module.clone(),
            declarator: ast::ModuleDeclarator::Inline(self.load_module_declarations(module)?),
        })
    }

    fn get_source_path(&self, name: &str, artifact: Artifact) -> PathBuf {
        let file = PathBuf::from(format!("{}.{}", name, artifact.extension()));
        let file_path = self.source_path.join(&file);
        if fs::exists(&file_path).unwrap() {
            file_path
        } else {
            self.library_path.join(file)
        }
    }
}

fn load_and_parse_module(source_path: PathBuf) -> Compilation<Vec<ast::Declaration<ParseInfo>>> {
    // Through the source map, so an editor's unsaved buffer stands in for the file.
    let source_text = crate::profile::time_if_slow(
        format!("module read: {}", source_path.display()),
        10.0,
        || source_map::read(&source_path),
    )?;
    let source = source_text.chars().collect::<Vec<_>>();

    // Every `ParseInfo` built while parsing this module is stamped with `file`, so
    // name/type errors raised long after all modules are merged can still name their
    // source -- and quote it (see `source_map`). Parse errors, raised here, get the
    // path attached directly below.
    let file = source_map::register(&source_path, &source_text);
    let attach = |error| CompilationError::ParseError {
        path: source_path.clone(),
        error,
    };

    source_map::with_current(file, || {
        let mut lexer = LexicalAnalyzer::default();
        let tokens = crate::profile::time_if_slow(
            format!("module lex: {}", source_path.display()),
            10.0,
            || lexer.tokenize(&source),
        );

        let mut parser = parser::Parser::from_tokens(tokens);

        let (declarations, errors) = crate::profile::time_if_slow(
            format!("module parse: {}", source_path.display()),
            10.0,
            || parser.parse_declaration_list_recovering(),
        );

        if !errors.is_empty() {
            return Err(CompilationError::ParseErrors {
                path: source_path.clone(),
                errors,
            });
        }

        // A fully-parsed module leaves only the `End` sentinel. Any other leftover
        // token means the declaration loop desynced (usually an unexpected layout
        // indent/dedent) and silently abandoned the rest of the file. Report it
        // instead of dropping it -- otherwise the failure only surfaces much later
        // as a missing `start` at run time.
        if let Some(token) = parser.remains().iter().find(|t| !t.is_end()) {
            return Err(attach(parser::ParseError::UnconsumedInput {
                found: token.kind.clone(),
                position: *token.location(),
            }));
        }

        Ok(declarations)
    })
}
