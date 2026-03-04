use std::{fmt, fs, io, path::PathBuf, rc::Rc};

use clap::Parser;
use thiserror::Error;

use crate::{
    ast::{
        self, ROOT_MODULE_NAME,
        namer::{self, NameError},
    },
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
}

impl Compiler {
    pub fn parse_compilation_unit(&self) -> Compilation {
        let module_name = parser::Identifier::from_str(ROOT_MODULE_NAME);
        Ok(CompilationUnit {
            root_module: self.load_module(&module_name)?,
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
        let evaluation_order = dependencies.in_resolvable_order();

        if dependencies.are_sound() {
            let mut globals = Globals::default();

            for symbol in resolved_symbols
                .elaborate_compilation_unit(evaluation_order.iter())?
                // Should compute a new evaluation_order before .terms
                // -- one that takes witness premises into account
                .terms(evaluation_order.iter())
            {
                let value = Rc::new(symbol.body.erase_annotation())
                    .interpret(Env::from_globals(globals.clone()))
                    //.reduce(&Env::from_globals(globals.clone()))
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
        let symbols = symbols.desugar_expressions();

        let compilation = symbols.resolve_names()?;

        let dependencies = compilation.dependency_matrix();
        let evaluation_order = dependencies.in_resolvable_order();

        if dependencies.are_sound() {
            let program = compilation
                .elaborate_compilation_unit(evaluation_order.iter())?
                .closure_conversion()
                .lambda_lift();

            //            println!("program {program:?}");
            let mut code = CodeBuffer::default();

            program.generate_code(&mut code).unwrap();
            //println!("/* generated_code.c */\n{}", code);

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

    println!(
        "load_and_parse_module: {source_path:?} last known location {}",
        parser.remains()[0].location()
    );

    Ok(declarations)
}
