use std::{collections::HashMap, fmt, marker::PhantomData, rc::Rc, vec};

use crate::{
    ast::{self, CompilationUnit, Declaration, ProductElement, TypeSignature},
    parser::{self, IdentifierPath, ParseInfo},
};

pub type Expr = ast::Expr<ParseInfo, Identifier>;
pub type SelfReferential = ast::SelfReferential<ParseInfo, Identifier>;
pub type Lambda = ast::Lambda<ParseInfo, Identifier>;
pub type Apply = ast::Apply<ParseInfo, Identifier>;
pub type Binding = ast::Binding<ParseInfo, Identifier>;
pub type Record = ast::Record<ParseInfo, Identifier>;
pub type Tuple = ast::Tuple<ParseInfo, Identifier>;
pub type Projection = ast::Projection<ParseInfo, Identifier>;

#[derive(Debug, Clone)]
pub enum Identifier {
    Bound(usize),
    Free(MemberPath),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SymbolAccessPath {
    module_prefix: parser::IdentifierPath,
    member: String,
    member_suffix: Vec<String>,
}

impl SymbolAccessPath {
    fn into_expr(self, parse_info: ParseInfo) -> Expr {
        let path = MemberPath {
            module: self.module_prefix,
            member: parser::Identifier::from_str(&self.member),
        };
        self.member_suffix.iter().fold(
            Expr::Variable(parse_info, Identifier::Free(path)),
            |base, field| {
                ast::Expr::Project(
                    parse_info,
                    ast::Projection {
                        base: base.into(),
                        select: ProductElement::Name(parser::Identifier::from_str(field.as_str())),
                    },
                )
            },
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MemberPath {
    module: parser::IdentifierPath,
    member: parser::Identifier,
}

impl MemberPath {
    fn from_root_symbol(member: parser::Identifier) -> Self {
        Self {
            module: parser::IdentifierPath::new(ast::ROOT_MODULE_NAME),
            member,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Symbols<A> {
    table: HashMap<String, Symbol<A>>,
    _bogus: PhantomData<A>,
}

impl<A> Default for Symbols<A> {
    fn default() -> Self {
        Self {
            table: HashMap::default(),
            _bogus: PhantomData::default(),
        }
    }
}

impl<A> Symbols<A> {
    // resolve_path
    // resolve_projection

    // take as many of path.iter() that forms an all module prefix
    // M0.M1.S.F0.F1
    pub fn resolve_path(&self, path: &parser::IdentifierPath) -> Option<SymbolAccessPath> {
        let mut module_path = vec![];
        let mut member = vec![];
        let mut in_module_prefix = true;

        for segment in path.iter() {
            if in_module_prefix {
                if let Symbol::Module(..) = self.table.get(&module_path.join("/"))? {
                    module_path.push(segment);
                } else {
                    in_module_prefix = false;
                    member.push(segment);
                }
            } else {
                member.push(segment);
            }
        }

        let mut members = member.iter().map(|&s| s.to_owned());
        Some(SymbolAccessPath {
            module_prefix: parser::IdentifierPath::try_from_components(&module_path)?,
            member: members.next()?,
            member_suffix: members.collect(),
        })
    }

    pub fn lookup(&self, id: &parser::Identifier) -> Option<&Symbol<A>> {
        self.table.get(id.as_str())
    }

    pub fn from(compilation: CompilationUnit<A>) -> Self {
        Self::index_module_members(
            &mut IdentifierPath::new(compilation.root.name.as_str()),
            compilation.root.declarator.members,
        )
    }

    // This must flatten the module namespace
    pub fn index_module_members(
        prefix: &mut IdentifierPath,
        declarations: Vec<Declaration<A>>,
    ) -> Symbols<A> {
        let mut the = Self::default();

        for decl in declarations {
            let (member_path, symbol) = match decl {
                ast::Declaration::Value(_, ast::ValueDeclaration { name, declarator }) => (
                    prefix.make_member_path(name.as_str()),
                    Symbol::Value(ValueSymbol {
                        name: name,
                        type_signature: declarator.type_signature,
                    }),
                ),
                ast::Declaration::Module(_, ast::ModuleDeclaration { name, declarator }) => {
                    let name_str = name.as_str();
                    let owned_str = name_str.to_owned();
                    (
                        prefix.make_member_path(name_str),
                        Symbol::Module(ModuleSymbol {
                            name,
                            contents: {
                                prefix.tail.push(owned_str);
                                let member_symbols =
                                    Self::index_module_members(prefix, declarator.members);
                                prefix.tail.pop();
                                member_symbols
                            },
                        }),
                    )
                }
                ast::Declaration::Type(_, ast::TypeDeclaration { name, declarator }) => (
                    prefix.make_member_path(name.as_str()),
                    match declarator {
                        ast::TypeDeclarator::Record(_, record) => Symbol::Struct(StructSymbol {
                            name: name,
                            fields: record.fields.into_iter().map(|f| f.name).collect(),
                        }),
                    },
                ),
            };

            the.table.insert(member_path, symbol);
        }

        the
    }
}

#[derive(Debug, Clone)]
pub enum Symbol<A> {
    Value(ValueSymbol),
    Module(ModuleSymbol<A>),
    // These are both types, they ought to be wrapped as such
    Struct(StructSymbol),
    Coproduct(CoproductSymbol),
}

impl<A> Symbol<A> {
    pub fn name(&self) -> &parser::Identifier {
        match self {
            Symbol::Value(sym) => &sym.name,
            Symbol::Module(sym) => &sym.name,
            Symbol::Struct(sym) => &sym.name,
            Symbol::Coproduct(sym) => &sym.name,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ValueSymbol {
    pub name: parser::Identifier,
    pub type_signature: Option<TypeSignature>,
    // What type?
    // parser::Identifer at this point and
    // resolve_bindings on the whole table?
    //    pub body: ast::Expr<A, Id>,
}

#[derive(Debug, Clone)]
pub struct ModuleSymbol<A> {
    pub name: parser::Identifier,
    pub contents: Symbols<A>,
}

#[derive(Debug, Clone)]
pub struct StructSymbol {
    pub name: parser::Identifier,
    pub fields: Vec<parser::Identifier>,
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol {
    pub name: parser::Identifier,
}

// make part of SymbolTable?
#[derive(Debug, Default)]
struct DeBruijnIndex(Vec<parser::Identifier>);

impl DeBruijnIndex {
    fn resolve(&self, id: &parser::Identifier) -> Identifier {
        if let Some(index) = self.0.iter().rposition(|n| n == id) {
            Identifier::Bound(index)
        } else {
            Identifier::Free(MemberPath::from_root_symbol(id.to_owned()))
        }
    }

    fn bind<F, A>(&mut self, id: parser::Identifier, mut block: F) -> A
    where
        F: FnMut(&mut DeBruijnIndex, Identifier) -> A,
    {
        let de_bruijn_index = self.0.len();
        self.0.push(id);
        let a = block(self, Identifier::Bound(de_bruijn_index));
        self.0.pop();
        a
    }
}

impl parser::Expr {
    pub fn resolve_names(&self, symbols: &Symbols<ParseInfo>) -> Expr {
        self.resolve(&mut DeBruijnIndex::default(), symbols)
    }

    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Expr {
        match self {
            Self::Variable(a, path) => {
                // Make sure to insert project here.

                if let Some(name) = path.try_as_simple() {
                    Expr::Variable(*a, names.resolve(&name))
                } else if let Some(path) = symbols.resolve_path(path) {
                    path.into_expr(*a)
                } else if let Some(path) = symbols.resolve_path(&path.as_root_module_member()) {
                    path.into_expr(*a)
                } else {
                    panic!("Unresolved symbol {}", path)
                }
            }
            Self::Constant(a, literal) => Expr::Constant(*a, literal.clone()),
            Self::RecursiveLambda(a, node) => {
                Expr::RecursiveLambda(*a, node.resolve(names, symbols))
            }
            Self::Lambda(a, node) => Expr::Lambda(*a, node.resolve(names, symbols)),
            Self::Apply(a, node) => Expr::Apply(*a, node.resolve(names, symbols)),
            Self::Let(a, node) => Expr::Let(*a, node.resolve(names, symbols)),
            Self::Record(a, node) => Expr::Record(*a, node.resolve(names, symbols)),
            Self::Tuple(a, node) => Expr::Tuple(*a, node.resolve(names, symbols)),
            Self::Project(a, node) => Expr::Project(*a, node.resolve(names, symbols)),
        }
    }
}

impl parser::SelfReference {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> SelfReferential {
        if let Some(own_name) = self.own_name.try_as_simple() {
            names.bind(own_name, |names, name| SelfReferential {
                own_name: name,
                lambda: self.lambda.resolve(names, symbols),
            })
        } else {
            panic!("Parser erroneously accepted a pathed identifier for recursive function name")
        }
    }
}

impl parser::Lambda {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Lambda {
        if let Some(parameter) = self.parameter.try_as_simple() {
            names.bind(parameter, |names, parameter| Lambda {
                parameter,
                body: self.body.resolve(names, symbols).into(),
            })
        } else {
            panic!("Parser erroneously accepted a pathed identifier for lambda parameter")
        }
    }
}

impl parser::Apply {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Apply {
        Apply {
            function: self.function.resolve(names, symbols).into(),
            argument: self.argument.resolve(names, symbols).into(),
        }
    }
}

impl parser::Binding {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Binding {
        if let Some(binder) = self.binder.try_as_simple() {
            let bound = Rc::new(self.bound.resolve(names, symbols));
            names.bind(binder, |names, binder| Binding {
                binder,
                bound: Rc::clone(&bound),
                body: self.body.resolve(names, symbols).into(),
            })
        } else {
            panic!("Parser erroneously accepted a pathed identifier for binder")
        }
    }
}

impl parser::Record {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Record {
        Record {
            fields: self
                .fields
                .iter()
                .map(|(label, e)| (label.clone(), e.resolve(names, symbols).into()))
                .collect(),
        }
    }
}

impl parser::Tuple {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Tuple {
        Tuple {
            elements: self
                .elements
                .iter()
                .map(|e| e.resolve(names, symbols).into())
                .collect(),
        }
    }
}

impl parser::Projection {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &Symbols<ParseInfo>) -> Projection {
        Projection {
            base: self.base.resolve(names, symbols).into(),
            select: self.select.clone(),
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound(ix) => write!(f, "#{ix}"),
            Self::Free(identifier) => write!(f, "{identifier}"),
        }
    }
}

impl fmt::Display for SymbolAccessPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}::{}.{}",
            self.module_prefix,
            self.member,
            self.member_suffix.join("."),
        )
    }
}

impl fmt::Display for MemberPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { module, member } = self;
        write!(f, "{module}::{member}")
    }
}
