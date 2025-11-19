use std::{collections::HashMap, fmt, rc::Rc};

use crate::{
    ast::{self, CompilationUnit, TypeSignature},
    parser::{self, ParseInfo},
};

pub type Expr = ast::Expr<ParseInfo, Identifier>;
pub type SelfReferential = ast::SelfReferential<ParseInfo, Identifier>;
pub type Lambda = ast::Lambda<ParseInfo, Identifier>;
pub type Apply = ast::Apply<ParseInfo, Identifier>;
pub type Binding = ast::Binding<ParseInfo, Identifier>;
pub type Tuple = ast::Tuple<ParseInfo, Identifier>;
pub type Projection = ast::Projection<ParseInfo, Identifier>;

#[derive(Debug, Clone)]
pub enum Identifier {
    Bound(usize),

    // Should this not be some sort of access path?
    // The program can have imports and aliasing going on and
    // these must all be
    Free(parser::Identifier),
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound(ix) => write!(f, "#{ix}"),
            Self::Free(identifier) => write!(f, "{identifier}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Symbols<A, Id> {
    table: HashMap<parser::Identifier, Symbol<A, Id>>,
}

impl<A, Id> Default for Symbols<A, Id> {
    fn default() -> Self {
        Self {
            table: HashMap::default(),
        }
    }
}

impl<A> Symbols<A, parser::Identifier> {
    // resolve_path
    // resolve_projection

    pub fn lookup(&self, id: &parser::Identifier) -> Option<&Symbol<A, parser::Identifier>> {
        self.table.get(id)
    }

    pub fn from(compilation: CompilationUnit<A>) -> Self {
        Self::from_module(compilation.root)
    }

    pub fn from_module(module: ast::ModuleDeclaration<A>) -> Symbols<A, parser::Identifier> {
        let mut the = Self::default();
        let Self { table, .. } = &mut the;

        for decl in module.declarator.contents {
            match decl {
                ast::Declaration::Value(_, decl) => {
                    let _ = table.insert(
                        decl.name.clone(),
                        Symbol::Value(ValueSymbol {
                            name: decl.name,
                            type_signature: decl.declarator.type_signature,
                            body: decl.declarator.body,
                        }),
                    );
                    ()
                }
                ast::Declaration::Module(_, decl) => {
                    let _ = table.insert(
                        decl.name.clone(),
                        Symbol::Module(ModuleSymbol {
                            name: decl.name.clone(),
                            contents: Self::from_module(decl),
                        }),
                    );
                    ()
                }
                ast::Declaration::Type(_, decl) => {
                    let _ = table.insert(
                        decl.name.clone(),
                        match decl.declarator {
                            ast::TypeDeclarator::Record(_, record) => {
                                Symbol::Struct(StructSymbol {
                                    name: decl.name,
                                    fields: record.fields.into_iter().map(|f| f.name).collect(),
                                })
                            }
                        },
                    );
                    ()
                }
            }
        }

        the
    }
}

#[derive(Debug, Clone)]
pub enum Symbol<A, Id> {
    Value(ValueSymbol<A, Id>),
    Module(ModuleSymbol<A, Id>),
    // These are both types, they ought to be wrapped as such
    Struct(StructSymbol),
    Coproduct(CoproductSymbol),
}

#[derive(Debug, Clone)]
pub struct ValueSymbol<A, Id> {
    pub name: parser::Identifier,
    pub type_signature: Option<TypeSignature>,
    // What type?
    // parser::Identifer at this point and
    // resolve_bindings on the whole table?
    pub body: ast::Expr<A, Id>,
}

#[derive(Debug, Clone)]
pub struct ModuleSymbol<A, Id> {
    pub name: parser::Identifier,
    pub contents: Symbols<A, Id>,
}

#[derive(Debug, Clone)]
pub struct StructSymbol {
    pub name: parser::Identifier,
    pub fields: Vec<parser::Identifier>,
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol;

// make part of SymbolTable?
#[derive(Debug, Default)]
struct DeBruijnIndex(Vec<parser::Identifier>);

impl DeBruijnIndex {
    fn resolve(&self, id: &parser::Identifier) -> Identifier {
        if let Some(index) = self.0.iter().rposition(|n| n == id) {
            Identifier::Bound(index)
        } else {
            Identifier::Free(id.clone())
        }
    }

    fn bind<F, A>(&mut self, id: parser::Identifier, mut block: F) -> A
    where
        F: FnMut(&mut DeBruijnIndex, Identifier) -> A,
    {
        let de_bruijn = self.0.len();
        println!("bind: {id} -> {de_bruijn}");

        self.0.push(id);
        let a = block(self, Identifier::Bound(de_bruijn));
        self.0.pop();
        a
    }
}

impl parser::Expr {
    pub fn resolve_bindings(&self) -> Expr {
        self.resolve(&mut DeBruijnIndex::default())
    }

    fn resolve(&self, names: &mut DeBruijnIndex) -> Expr {
        match self {
            Self::Variable(a, info) => Expr::Variable(*a, names.resolve(info)),
            Self::Constant(a, info) => Expr::Constant(*a, info.clone()),
            Self::RecursiveLambda(a, info) => Expr::RecursiveLambda(*a, info.resolve(names)),
            Self::Lambda(a, info) => Expr::Lambda(*a, info.resolve(names)),
            Self::Apply(a, x) => Expr::Apply(*a, x.resolve(names)),
            Self::Let(a, x) => Expr::Let(*a, x.resolve(names)),
            Self::Tuple(a, x) => Expr::Tuple(*a, x.resolve(names)),
            Self::Project(a, x) => Expr::Project(*a, x.resolve(names)),
        }
    }
}

impl parser::SelfReference {
    fn resolve(&self, names: &mut DeBruijnIndex) -> SelfReferential {
        names.bind(self.own_name.clone(), |names, name| SelfReferential {
            own_name: name,
            underlying: self.underlying.resolve(names),
        })
    }
}

impl parser::Lambda {
    fn resolve(&self, names: &mut DeBruijnIndex) -> Lambda {
        names.bind(self.parameter.clone(), |names, parameter| Lambda {
            parameter,
            body: self.body.resolve(names).into(),
        })
    }
}

impl parser::Apply {
    fn resolve(&self, names: &mut DeBruijnIndex) -> Apply {
        Apply {
            function: self.function.resolve(names).into(),
            argument: self.argument.resolve(names).into(),
        }
    }
}

impl parser::Binding {
    fn resolve(&self, names: &mut DeBruijnIndex) -> Binding {
        let bound = Rc::new(self.bound.resolve(names));
        names.bind(self.binder.clone(), |names, binder| Binding {
            binder,
            bound: Rc::clone(&bound),
            body: self.body.resolve(names).into(),
        })
    }
}

impl parser::Tuple {
    fn resolve(&self, names: &mut DeBruijnIndex) -> Tuple {
        Tuple {
            elements: self
                .elements
                .iter()
                .map(|e| e.resolve(names).into())
                .collect(),
        }
    }
}

impl parser::Projection {
    fn resolve(&self, names: &mut DeBruijnIndex) -> Projection {
        Projection {
            base: self.base.resolve(names).into(),

            // How does this happen?
            // It needs the decl to know which fields it has
            // which is to say: it needs the type of base, really.
            select: self.select.clone(),
        }
    }
}
