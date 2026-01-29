use std::{fmt, fs, io, path::PathBuf, rc::Rc};

use clap::Parser;
use thiserror::Error;

use crate::{
    ast::{
        self, ROOT_MODULE_NAME,
        namer::{self, NameError},
    },
    interpreter::{self, Environment, RuntimeError},
    lexer::LexicalAnalyzer,
    parser::{self, ParseError, ParseInfo},
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
    pub error: E,
}

pub trait LocatedError
where
    Self: Sized + fmt::Debug,
{
    fn at(self, pi: ParseInfo) -> Located<Self> {
        Located {
            parse_info: pi,
            error: self,
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

    pub fn typecheck_and_initialize(&self, program: CompilationUnit) -> Compilation<Environment> {
        let mut environment = Environment::default();
        let mut symbols = namer::SymbolTable::import_compilation_unit(program)?;
        symbols.lower_tuples();

        let compilation = symbols.rename_symbols()?;

        let dependencies = compilation.dependency_matrix();
        let evaluation_order = dependencies.in_resolvable_order();

        if dependencies.are_sound() {
            for symbol in compilation
                .compute_types(evaluation_order.iter())?
                .terms(evaluation_order.iter())
            {
                let value = Rc::new(symbol.body().erase_annotation())
                    .reduce(&environment)
                    .expect("successful static init");
                environment.define_global(&symbol.name, value);
            }
        } else {
            panic!("Bad dependencies")
        }

        Ok(environment)
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
    println!("load_and_parse_module: {:?}", source_path);
    let source = fs::read_to_string(source_path)?.chars().collect::<Vec<_>>();

    let mut lexer = LexicalAnalyzer::default();
    let tokens = lexer.tokenize(&source);

    let mut parser = parser::Parser::from_tokens(tokens);

    Ok(parser.parse_declaration_list()?)
}
