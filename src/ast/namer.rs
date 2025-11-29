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
pub type TypeExpression = ast::TypeExpression<ParseInfo, ModuleMemberPath>;

/*
 * module A =
 *   module B =
 *     type Option a = Some of a | None
 *     let map f xs : (a -> b) -> Option a -> Option b = ...
 *
 *
 */

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
    fn into_expression(self, parse_info: ParseInfo) -> Expr {
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
    pub fn from_root_symbol(member: parser::Identifier) -> Self {
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

// Why 2 type parameters really? When will they
// be different types?
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermId<TypeId, ValueId> {
    Type(TypeId),
    Value(ValueId),
}

impl<TypeId, ValueId> TermId<TypeId, ValueId> {
    pub fn try_into_type(self) -> Option<TypeId> {
        if let Self::Type(id) = self {
            Some(id)
        } else {
            None
        }
    }

    pub fn try_into_value_term(self) -> Option<ValueId> {
        if let Self::Value(id) = self {
            Some(id)
        } else {
            None
        }
    }
}

// "Modules do not exist" - they should get their own table.
#[derive(Debug, Clone)]
pub struct SymbolEnvironment<A, GlobalName, LocalId> {
    // does it even need this?
    pub modules: HashSet<parser::IdentifierPath>,
    pub symbols: HashMap<TermId<GlobalName, LocalId>, Symbol<A, GlobalName, LocalId>>,
    pub dependency_matrix: DependencyMatrix<TermId<GlobalName, LocalId>>,
    pub phase: PhantomData<(A, GlobalName, LocalId)>,
}

impl<A, TypeId, ValueId> Default for SymbolEnvironment<A, TypeId, ValueId> {
    fn default() -> Self {
        Self {
            modules: HashSet::default(),
            symbols: HashMap::default(),
            dependency_matrix: DependencyMatrix::default(),
            phase: PhantomData::default(),
        }
    }
}

impl<A, GlobalName, LocalId> SymbolEnvironment<A, GlobalName, LocalId>
where
    GlobalName: Eq + Hash,
    LocalId: Eq + Hash,
{
    pub fn initialization_order(&self) -> Vec<&TermId<GlobalName, LocalId>> {
        self.dependency_matrix.initialization_order()
    }

    pub fn value_symbols(&self) -> Vec<&ValueSymbol<A, GlobalName, LocalId>> {
        self.extract_symbols(|sym| {
            if let Symbol::Value(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    pub fn type_symbols(&self) -> Vec<&TypeSymbol<A, GlobalName>> {
        self.extract_symbols(|sym| {
            if let Symbol::Type(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    fn extract_symbols<F, Sym>(&self, p: F) -> Vec<&Sym>
    where
        F: Fn(&Symbol<A, GlobalName, LocalId>) -> Option<&Sym>,
    {
        self.initialization_order()
            .iter()
            .filter_map(|id| self.symbols.get(id))
            .filter_map(p)
            .collect()
    }
}

impl SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath> {
    pub fn dependencies_satisfiable(&self) -> bool {
        self.dependency_matrix.is_satisfied()
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
                if self.modules.contains(&identifier_path) {
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
        let mut modules = HashSet::default();

        let _ = Self::index_module_contents(
            &mut parser::IdentifierPath::new(compilation.root.name.as_str()),
            &compilation.root.declarator.members,
            &mut modules,
            &mut symbol_table,
        );

        Self {
            modules,
            symbols: symbol_table,
            dependency_matrix: DependencyMatrix::default(),
            phase: PhantomData::default(),
        }
    }

    // This could just as well keep a running module_path of varified
    // modules. Shouldn't I just rewrite this sucker?
    pub fn index_module_contents(
        prefix: &mut parser::IdentifierPath,
        declarations: &[Declaration<ParseInfo>],
        modules: &mut HashSet<parser::IdentifierPath>,
        symbol_table: &mut HashMap<
            TermId<parser::IdentifierPath, parser::IdentifierPath>,
            Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
        >,
    ) -> Vec<Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>> {
        let mut symbols = Vec::with_capacity(declarations.len());
        for decl in declarations {
            match decl {
                ast::Declaration::Value(_, ast::ValueDeclaration { name, declarator }) => {
                    let term = TermId::Value(prefix.clone().with_suffix(name.as_str()));
                    let symbol = Symbol::Value(ValueSymbol {
                        name: parser::IdentifierPath::new(name.as_str()),
                        type_signature: declarator.type_signature.clone(),

                        // This is a very expensive clone
                        // perhaps I _could_ move into here
                        body: declarator.body.clone(),
                    });

                    symbols.push(symbol.clone());
                    symbol_table.insert(term, symbol);
                }
                ast::Declaration::Module(_, ast::ModuleDeclaration { name, declarator }) => {
                    let name_str = name.as_str();
                    let owned_str = name_str.to_owned();

                    let term = prefix.clone().with_suffix(name_str);
                    let module = ModuleSymbol {
                        name: parser::IdentifierPath::new(name.as_str()),
                        contents: {
                            prefix.tail.push(owned_str);
                            let member_symbols = Self::index_module_contents(
                                prefix,
                                &declarator.members,
                                modules,
                                symbol_table,
                            );
                            prefix.tail.pop();
                            member_symbols
                        },
                        _bogus: PhantomData::default(),
                    };

                    symbols.push(Symbol::Module(module.clone()));
                    modules.insert(term);
                }
                ast::Declaration::Type(_, ast::TypeDeclaration { name, declarator }) => {
                    let term = TermId::Type(prefix.clone().with_suffix(name.as_str()));
                    let symbol = match declarator {
                        ast::TypeDeclarator::Record(_, record) => {
                            Symbol::Type(TypeSymbol::Record(RecordSymbol {
                                name: parser::IdentifierPath::new(name.as_str()),
                                fields: record
                                    .fields
                                    .iter()
                                    .map(|f| (f.name.clone(), f.type_signature.clone()))
                                    .collect(),
                            }))
                        }
                    };

                    symbols.push(symbol.clone());
                    symbol_table.insert(term, symbol);
                }
            };
        }

        symbols
    }
}

#[derive(Debug, Clone)]
pub enum Symbol<A, GlobalName, LocalId> {
    Value(ValueSymbol<A, GlobalName, LocalId>),
    Module(ModuleSymbol<A, GlobalName, LocalId>),
    Type(TypeSymbol<A, GlobalName>),
}

#[derive(Debug, Clone)]
pub enum TypeSymbol<A, GlobalName> {
    Record(RecordSymbol<A, GlobalName>),
    Coproduct(CoproductSymbol<GlobalName>),
}

// This fucker needs a Name parameter anyway because the name
// field behaves more like TypeId than ValueId. It will never
// be Bound, always Free.
//
// What about substituting TypeId for Name? Is there ever a time
// when the data type for symbols and types must be different?
#[derive(Debug, Clone)]
pub struct ValueSymbol<A, GlobalName, LocalId> {
    pub name: GlobalName,
    pub type_signature: Option<TypeSignature<ParseInfo, GlobalName>>,
    pub body: ast::Expr<A, LocalId>,
}

#[derive(Debug, Clone)]
pub struct ModuleSymbol<A, GlobalName, LocalId> {
    pub name: parser::IdentifierPath,
    pub contents: Vec<Symbol<A, GlobalName, LocalId>>,
    _bogus: PhantomData<A>,
}

#[derive(Debug, Clone)]
pub struct RecordSymbol<A, GlobalName> {
    pub name: GlobalName,
    pub fields: Vec<(parser::Identifier, TypeSignature<A, GlobalName>)>,
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol<GlobalName> {
    pub name: GlobalName,
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

impl parser::TypeExpression {
    pub fn resolve_names(
        &self,
        _symbols: &SymbolEnvironment<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> TypeExpression {
        todo!()
    }
}

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
                    path.into_expression(*a)
                } else if let Some(path) =
                    symbols.resolve_module_path_expr(&identifier_path.as_root_module_member())
                {
                    path.into_expression(*a)
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
