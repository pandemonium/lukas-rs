use std::{fmt, fs, io, path::PathBuf, rc::Rc};

use clap::Parser;
use thiserror::Error;

use crate::{
    ast::{
        self, ROOT_MODULE_NAME,
        namer::{self, NameError},
    },
    chez,
    codegen::CodeBuffer,
    interpreter::{
        self, Environment, RuntimeError,
        cek::{Env, Globals},
    },
    lexer::LexicalAnalyzer,
    parser::{self, ParseError, ParseInfo, Parsed},
    phase,
    typer::TypeError,
};

pub type CompilationUnit = ast::CompilationUnit<ParseInfo>;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("parse error: {0}")]
    ParseError(#[from] ParseError),

    #[error("name error: {0}")]
    NameError(#[from] Located<NameError>),

    #[error("type error: {0}")]
    TypeError(#[from] Located<TypeError>),

    #[error("interpretation error: {0}")]
    InterpretationError(#[from] RuntimeError),

    #[error("I/O error: {0}")]
    IO(#[from] io::Error),

    #[error("Error generating code")]
    Chez(#[from] chez::ChezError),

    #[error(
        "the root module (Root.lady) must define an entry point `start` \
         (e.g. `start := λ_. ...`), but none was found"
    )]
    MissingStart,
}

#[derive(Debug, Error)]
pub struct Located<E>
where
    E: fmt::Debug,
{
    pub parse_info: ParseInfo,
    pub error: Box<E>,
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

#[derive(Clone, Debug, Parser)]
pub struct Compiler {
    #[arg(long = "library")]
    pub library_path: PathBuf,

    #[arg(long = "source")]
    pub source_path: PathBuf,

    #[arg(long = "scheme")]
    pub scheme_file: Option<PathBuf>,
}

impl Compiler {
    pub fn parse_compilation_unit(&self) -> Compilation {
        let module_name = parser::Identifier::from_str(ROOT_MODULE_NAME);
        let root_module = self.load_module(&module_name)?;

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
        let program = self.parse_compilation_unit()?;
        self.typecheck_and_initialize(program)
    }

    pub fn compiler_main(&self) -> Compilation<()> {
        let program = self.parse_compilation_unit()?;
        self.typecheck_and_compile(program)
    }

    pub fn typecheck_and_initialize(&self, program: CompilationUnit) -> Compilation<Environment> {
        let symbols = phase::SymbolTable::<Parsed>::import_compilation_unit(program)?;
        let resolved_symbols = symbols.desugar().resolve_names()?;

        let dependencies = resolved_symbols.dependency_matrix();

        if dependencies.are_sound() {
            // Shared, live globals: `clone()` shares the underlying map, so a
            // closure captured for an earlier symbol sees symbols defined later
            // (mutually recursive dictionaries / lifted methods).
            let globals = Globals::default();

            let compilation_unit = resolved_symbols.elaborate_compilation_unit()?;
            let deps = compilation_unit.dependency_matrix();
            let evaluation_order = deps.in_resolvable_order();

            for symbol in compilation_unit.terms(evaluation_order.iter()) {
                let value = Rc::new(symbol.body.erase_annotation())
                    .interpret(Env::from_globals(globals.clone()))
                    .expect("successful static init");

                globals.define(symbol.name.clone(), value);
            }

            Ok(Env::from_globals(globals))
        } else {
            // Err(CompilationError::Dependencies...)
            panic!("Bad dependencies")
        }
    }

    pub fn typecheck_and_compile(&self, program: CompilationUnit) -> Compilation<()> {
        let symbols = namer::SymbolTable::import_compilation_unit(program)?;
        let resolved_symbols = symbols.desugar().resolve_names()?;

        let dependencies = resolved_symbols.dependency_matrix();

        if dependencies.are_sound() {
            //            let program = compilation
            //                .elaborate_compilation_unit()?
            //                .closure_conversion()
            //                .lambda_lift();

            let program = resolved_symbols.elaborate_compilation_unit()?;

            let mut code = CodeBuffer::default();
            program.emit_scheme_code(&mut code)?;

            if let Some(target) = &self.scheme_file {
                code.write_to_file(target)?;
            } else {
                println!("{}", code);
            }

            Ok(())
        } else {
            panic!("Bad dependencies")
        }
    }

    pub fn load_module_declarations(
        &self,
        module: &parser::Identifier,
    ) -> Compilation<Vec<ast::Declaration<ParseInfo>>> {
        let source_path = self.get_source_path(module);
        load_and_parse_module(source_path)
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

    fn get_source_path(&self, module: &parser::Identifier) -> PathBuf {
        let name = PathBuf::from(format!("{}.lady", module.as_str()));
        let file_path = self.source_path.join(&name);
        if fs::exists(&file_path).unwrap() {
            file_path
        } else {
            self.library_path.join(name)
        }
    }
}

fn load_and_parse_module(source_path: PathBuf) -> Compilation<Vec<ast::Declaration<ParseInfo>>> {
    let source = fs::read_to_string(&source_path)?
        .chars()
        .collect::<Vec<_>>();

    let mut lexer = LexicalAnalyzer::default();
    let tokens = lexer.tokenize(&source);

    let mut parser = parser::Parser::from_tokens(tokens);

    let declarations = parser.parse_declaration_list()?;

    // A fully-parsed module leaves only the `End` sentinel. Any other leftover
    // token means the declaration loop desynced (usually an unexpected layout
    // indent/dedent) and silently abandoned the rest of the file. Report it
    // instead of dropping it -- otherwise the failure only surfaces much later
    // as a missing `start` at run time.
    if let Some(token) = parser.remains().iter().find(|t| !t.is_end()) {
        Err(parser::ParseError::UnconsumedInput {
            found: token.kind.clone(),
            position: *token.location(),
        })?;
    }

    Ok(declarations)
}
