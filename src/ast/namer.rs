use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    hash::Hash,
    marker::PhantomData,
    rc::Rc,
    vec,
};

use crate::{
    ast::{self, CompilationUnit, Declaration, ProductElement, TypeSignature},
    parser::{self, ParseInfo},
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
    Free(ModuleMemberPath),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ModulePathExpr {
    module_prefix: parser::IdentifierPath,
    member: String,
    member_suffix: Vec<String>,
}

impl ModulePathExpr {
    fn into_projection(self, parse_info: ParseInfo) -> Expr {
        let path = ModuleMemberPath {
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

    pub fn into_member_path(self) -> ModuleMemberPath {
        ModuleMemberPath {
            module: self.module_prefix,
            member: parser::Identifier::from_str(&self.member),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ModuleMemberPath {
    module: parser::IdentifierPath,
    member: parser::Identifier,
}

impl ModuleMemberPath {
    fn from_root_symbol(member: parser::Identifier) -> Self {
        Self {
            module: parser::IdentifierPath::new(ast::ROOT_MODULE_NAME),
            member,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DependencyMatrix<Id>(HashMap<Id, Vec<Id>>);

impl<Id> Default for DependencyMatrix<Id> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

impl<Id> DependencyMatrix<Id>
where
    Id: Eq + Hash,
{
    fn is_satisfied(&self) -> bool {
        let Self(map) = self;
        let unsatisfieds = map
            .iter()
            .filter_map(|(_, deps)| deps.iter().find(|&dep| !map.contains_key(dep)))
            .collect::<Vec<_>>();

        unsatisfieds.is_empty()
    }

    pub fn initialization_order(&self) -> Vec<&Id> {
        let mut resolved = Vec::with_capacity(self.0.len());

        let mut graph = self
            .0
            .iter()
            // Filter out recursive definitions
            .map(|(node, edges)| {
                (
                    node,
                    edges
                        .iter()
                        .filter(|&edge| edge != node)
                        .collect::<HashSet<_>>(),
                )
            })
            .collect::<Vec<_>>();

        let mut in_degrees = graph
            .iter()
            .map(|(node, edges)| (*node, edges.len()))
            .collect::<HashMap<_, _>>();

        let mut queue = in_degrees
            .iter()
            .filter_map(|(node, in_degree)| (*in_degree == 0).then_some(*node))
            .collect::<VecDeque<_>>();

        while let Some(independent) = queue.pop_front() {
            resolved.push(independent);

            for (node, edges) in &mut graph {
                if edges.remove(independent) {
                    if let Some(count) = in_degrees.get_mut(node) {
                        *count -= 1;
                        if *count == 0 {
                            queue.push_back(node);
                        }
                    }
                }
            }

            in_degrees.remove(independent);
        }

        resolved
    }
}

// This thing is craving a better name
#[derive(Debug, Clone)]
pub struct SymbolEnvironment<A, Name, Id> {
    pub symbol_table: HashMap<Name, Symbol<A, Id>>,
    pub dependency_matrix: DependencyMatrix<Name>,
    pub phase: PhantomData<A>,
}

impl<A, Name, Id> Default for SymbolEnvironment<A, Name, Id> {
    fn default() -> Self {
        Self {
            symbol_table: HashMap::default(),
            dependency_matrix: DependencyMatrix::default(),
            phase: PhantomData::default(),
        }
    }
}

impl SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath> {
    pub fn dependencies_satisfiable(&self) -> bool {
        self.dependency_matrix.is_satisfied()
    }

    pub fn resolution_order(&self) -> Vec<&parser::IdentifierPath> {
        self.dependency_matrix.initialization_order()
    }

    pub fn resolve_module_path_expr(
        &self,
        path: &parser::IdentifierPath,
    ) -> Option<ModulePathExpr> {
        let mut module_path = vec![];
        let mut member = vec![];
        let mut in_module_prefix = true;

        for segment in path.iter() {
            if in_module_prefix {
                let identifier_path = parser::IdentifierPath::try_from_components(&module_path)?;
                if let Symbol::Module(..) = self.symbol_table.get(&identifier_path)? {
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
        Some(ModulePathExpr {
            module_prefix: parser::IdentifierPath::try_from_components(&module_path)?,
            member: members.next()?,
            member_suffix: members.collect(),
        })
    }

    pub fn from(compilation: &CompilationUnit<ParseInfo>) -> Self {
        let mut symbol_table = HashMap::default();

        let _ = Self::index_module_contents(
            &mut parser::IdentifierPath::new(compilation.root.name.as_str()),
            &compilation.root.declarator.members,
            &mut symbol_table,
        );

        Self {
            symbol_table,
            dependency_matrix: DependencyMatrix::default(),
            phase: PhantomData::default(),
        }
    }

    pub fn index_module_contents(
        prefix: &mut parser::IdentifierPath,
        declarations: &[Declaration<ParseInfo>],
        symbol_table: &mut HashMap<
            parser::IdentifierPath,
            Symbol<ParseInfo, parser::IdentifierPath>,
        >,
    ) -> Vec<Symbol<ParseInfo, parser::IdentifierPath>> {
        let mut symbols = Vec::with_capacity(declarations.len());
        for decl in declarations {
            let (member_path, symbol) = match decl {
                ast::Declaration::Value(_, ast::ValueDeclaration { name, declarator }) => (
                    prefix.clone().with_suffix(name.as_str()),
                    Symbol::Value(ValueSymbol {
                        name: name.clone(),
                        type_signature: declarator.type_signature.clone(),

                        // This is a very expensive clone
                        // perhaps I _could_ move into here
                        body: declarator.body.clone(),
                    }),
                ),
                ast::Declaration::Module(_, ast::ModuleDeclaration { name, declarator }) => {
                    let name_str = name.as_str();
                    let owned_str = name_str.to_owned();
                    (
                        prefix.clone().with_suffix(name_str),
                        Symbol::Module(ModuleSymbol {
                            name: name.clone(),
                            contents: {
                                prefix.tail.push(owned_str);
                                let member_symbols = Self::index_module_contents(
                                    prefix,
                                    &declarator.members,
                                    symbol_table,
                                );
                                prefix.tail.pop();
                                member_symbols
                            },
                            _bogus: PhantomData::default(),
                        }),
                    )
                }
                ast::Declaration::Type(_, ast::TypeDeclaration { name, declarator }) => (
                    prefix.clone().with_suffix(name.as_str()),
                    match declarator {
                        ast::TypeDeclarator::Record(_, record) => {
                            Symbol::Type(TypeSymbol::Record(RecordSymbol {
                                name: parser::IdentifierPath::new(name.as_str()),
                                fields: record.fields.iter().map(|f| f.name.clone()).collect(),
                            }))
                        }
                    },
                ),
            };
            symbols.push(symbol.clone());
            symbol_table.insert(member_path, symbol);
        }

        symbols
    }
}

// It seems to me that this sucker needs 3 type parameters:
// 1. A for Phase Annotation
// 2. Name
// 3. AST identifier type
//
// #2 and #3 are not the same because:
// #2 is always free and #3 is sometimes bound
#[derive(Debug, Clone)]
pub enum Symbol<A, Id> {
    Value(ValueSymbol<A, Id>),
    Module(ModuleSymbol<A, Id>),
    Type(TypeSymbol<Id>),
}

#[derive(Debug, Clone)]
pub enum TypeSymbol<Id> {
    Record(RecordSymbol<Id>),
    Coproduct(CoproductSymbol<Id>),
}

// It has to have Id in here too
#[derive(Debug, Clone)]
pub struct ValueSymbol<A, Id> {
    pub name: parser::Identifier,
    pub type_signature: Option<TypeSignature>,
    pub body: ast::Expr<A, Id>,
}

#[derive(Debug, Clone)]
pub struct ModuleSymbol<A, Id> {
    pub name: parser::Identifier,
    pub contents: Vec<Symbol<A, Id>>,
    _bogus: PhantomData<A>,
}

#[derive(Debug, Clone)]
pub struct RecordSymbol<Id> {
    pub name: Id,
    pub fields: Vec<parser::Identifier>,
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol<Id> {
    pub name: Id,
}

#[derive(Debug, Default)]
struct DeBruijnIndex(Vec<parser::Identifier>);

impl DeBruijnIndex {
    fn resolve(&self, id: &parser::Identifier) -> Identifier {
        if let Some(index) = self.0.iter().rposition(|n| n == id) {
            Identifier::Bound(index)
        } else {
            Identifier::Free(ModuleMemberPath::from_root_symbol(id.to_owned()))
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

impl Expr {}

impl parser::Expr {
    pub fn resolve_names(
        &self,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Expr {
        self.resolve(&mut DeBruijnIndex::default(), symbols)
    }

    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Expr {
        match self {
            Self::Variable(a, identifier_path) => {
                if let Some(name) = identifier_path.try_as_simple() {
                    Expr::Variable(*a, names.resolve(&name))
                } else if let Some(path) = symbols.resolve_module_path_expr(identifier_path) {
                    path.into_projection(*a)
                } else if let Some(path) =
                    symbols.resolve_module_path_expr(&identifier_path.as_root_module_member())
                {
                    path.into_projection(*a)
                } else {
                    panic!("Unresolved symbol {}", identifier_path)
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> SelfReferential {
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Lambda {
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Apply {
        Apply {
            function: self.function.resolve(names, symbols).into(),
            argument: self.argument.resolve(names, symbols).into(),
        }
    }
}

impl parser::Binding {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Binding {
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Record {
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Tuple {
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
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Projection {
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

impl fmt::Display for ModulePathExpr {
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

impl fmt::Display for ModuleMemberPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { module, member } = self;
        write!(f, "{module}::{member}")
    }
}
