use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    hash::Hash,
    marker::PhantomData,
    rc::Rc,
    vec,
};

use crate::{
    ast::{
        self, CompilationUnit, Declaration, ProductElement, TypeApply, TypeArrow, TypeSignature,
    },
    parser::{self, IdentifierPath, ParseInfo},
    typer::BaseType,
};

pub type Expr = ast::Expr<ParseInfo, Identifier>;
pub type SelfReferential = ast::SelfReferential<ParseInfo, Identifier>;
pub type Lambda = ast::Lambda<ParseInfo, Identifier>;
pub type Apply = ast::Apply<ParseInfo, Identifier>;
pub type Binding = ast::Binding<ParseInfo, Identifier>;
pub type Record = ast::Record<ParseInfo, Identifier>;
pub type Tuple = ast::Tuple<ParseInfo, Identifier>;
pub type Projection = ast::Projection<ParseInfo, Identifier>;
pub type Sequence = ast::Sequence<ParseInfo, Identifier>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, QualifiedName>;

type RawTermId = SymbolName<parser::IdentifierPath, parser::IdentifierPath>;
type RawCompilationContext =
    CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
type RawSymbol = Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
pub type TermId = SymbolName<QualifiedName, Identifier>;
pub type NamedCompilationContext = CompilationContext<ParseInfo, QualifiedName, Identifier>;
pub type NamedSymbol = Symbol<ParseInfo, QualifiedName, Identifier>;

impl<A> ast::Expr<A, Identifier> {
    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        let mut free = HashSet::default();
        self.gather_free_variables(&mut free);
        free
    }

    fn gather_free_variables<'a>(&'a self, free: &mut HashSet<&'a QualifiedName>) {
        match self {
            Self::Variable(_, Identifier::Free(id)) => {
                free.insert(id);
            }
            Self::RecursiveLambda(_, rec) => rec.lambda.body.gather_free_variables(free),
            Self::Lambda(_, lambda) => lambda.body.gather_free_variables(free),
            Self::Apply(_, apply) => {
                apply.function.gather_free_variables(free);
                apply.argument.gather_free_variables(free)
            }
            Self::Let(_, binding) => {
                binding.bound.gather_free_variables(free);
                binding.body.gather_free_variables(free)
            }
            Self::Tuple(_, tuple) => {
                for elt in &tuple.elements {
                    elt.gather_free_variables(free)
                }
            }
            Self::Record(_, record) => {
                for (_, init) in &record.fields {
                    init.gather_free_variables(free)
                }
            }
            Self::Project(_, projection) => projection.base.gather_free_variables(free),
            _otherwise => (),
        }
    }
}

impl TypeExpression {
    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        let mut free = HashSet::default();
        self.gather_free_variables(&mut free);
        free
    }

    fn gather_free_variables<'a>(&'a self, free: &mut HashSet<&'a QualifiedName>) {
        match self {
            Self::Constructor(_, id) => {
                free.insert(id);
            }
            Self::Parameter(..) => (),
            Self::Apply(_, apply) => {
                apply.function.gather_free_variables(free);
                apply.argument.gather_free_variables(free);
            }
            Self::Arrow(_, arrow) => {
                arrow.domain.gather_free_variables(free);
                arrow.codomain.gather_free_variables(free);
            }
        }
    }
}

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
    Free(QualifiedName),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct QualifiedNameExpr {
    module_prefix: parser::IdentifierPath,
    member: String,
    member_suffix: Vec<String>,
}

impl QualifiedNameExpr {
    fn into_expression(self, parse_info: ParseInfo) -> Expr {
        let path = QualifiedName {
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

    pub fn into_member_path(self) -> QualifiedName {
        QualifiedName {
            module: self.module_prefix,
            member: parser::Identifier::from_str(&self.member),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct QualifiedName {
    module: parser::IdentifierPath,
    member: parser::Identifier,
}

impl QualifiedName {
    pub fn builtin(member: &str) -> Self {
        Self {
            module: parser::IdentifierPath::new(ast::BUILTIN_MODULE_NAME),
            member: parser::Identifier::from_str(member),
        }
    }

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
    Id: Eq + Hash + fmt::Display + fmt::Debug,
{
    pub fn add_edge(&mut self, node: Id, vertices: Vec<Id>) {
        self.0.insert(node, vertices);
    }

    pub fn are_sound(&self) -> bool {
        let Self(map) = self;
        let unsatisfieds = map
            .iter()
            .filter_map(|(_, deps)| deps.iter().find(|&dep| !map.contains_key(dep)))
            .collect::<Vec<_>>();

        unsatisfieds.is_empty()
    }

    pub fn in_resolvable_order(&self) -> Vec<&Id> {
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
                if edges.remove(independent)
                    && let Some(count) = in_degrees.get_mut(node)
                {
                    *count -= 1;
                    if *count == 0 {
                        queue.push_back(node);
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
pub enum SymbolName<TypeId, ValueId> {
    Type(TypeId),
    Value(ValueId),
}

// "Modules do not exist" - they should get their own table.
#[derive(Debug, Clone)]
pub struct CompilationContext<A, GlobalName, LocalId> {
    pub modules: HashSet<parser::IdentifierPath>,
    pub symbols: HashMap<SymbolName<GlobalName, LocalId>, Symbol<A, GlobalName, LocalId>>,
    pub phase: PhantomData<(A, GlobalName, LocalId)>,
}

impl<A, TypeId, ValueId> Default for CompilationContext<A, TypeId, ValueId> {
    fn default() -> Self {
        Self {
            modules: HashSet::default(),
            symbols: HashMap::default(),
            phase: PhantomData,
        }
    }
}

impl CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath> {
    pub fn resolve_module_path_expr(
        &self,
        path: &parser::IdentifierPath,
    ) -> Option<QualifiedNameExpr> {
        let mut module_path = vec![];
        let mut member = vec![];
        let mut in_module_prefix = true;

        for segment in path.iter() {
            if in_module_prefix {
                module_path.push(segment);
                let identifier_path = parser::IdentifierPath::try_from_components(&module_path)?;

                if !self.modules.contains(&identifier_path) {
                    module_path.pop();
                    in_module_prefix = false;
                    member.push(segment);
                }
            } else {
                member.push(segment);
            }
        }

        let mut members = member.iter().map(|&s| s.to_owned());
        Some(QualifiedNameExpr {
            module_prefix: parser::IdentifierPath::try_from_components(&module_path)?,
            member: members.next()?,
            member_suffix: members.collect(),
        })
    }

    pub fn from(program: &CompilationUnit<ParseInfo>) -> Self {
        let mut symbols = HashMap::default();
        let mut modules = HashSet::default();

        let builtins = parser::IdentifierPath::new(ast::BUILTIN_MODULE_NAME);

        modules.insert(parser::IdentifierPath::new(ast::ROOT_MODULE_NAME));
        modules.insert(builtins.clone());

        symbols.insert(
            SymbolName::Type(builtins.clone().with_suffix("Int")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Int),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );

        symbols.insert(
            SymbolName::Type(builtins.with_suffix("Text")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Text),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );

        let _ = Self::index_module_contents(
            parser::IdentifierPath::new(program.root.name.as_str()),
            &program.root.declarator.members,
            &mut modules,
            &mut symbols,
        );

        Self {
            modules,
            symbols,
            phase: PhantomData,
        }
    }

    // This could just as well keep a running module_path of varified
    // modules. Shouldn't I just rewrite this sucker?
    pub fn index_module_contents(
        prefix: parser::IdentifierPath,
        declarations: &[Declaration<ParseInfo>],
        modules: &mut HashSet<parser::IdentifierPath>,
        symbol_table: &mut HashMap<
            SymbolName<parser::IdentifierPath, parser::IdentifierPath>,
            Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
        >,
    ) -> Vec<Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>> {
        let mut symbols = Vec::with_capacity(declarations.len());
        for decl in declarations {
            match decl {
                ast::Declaration::Value(_, ast::ValueDeclaration { name, declarator }) => {
                    let symbol_name = prefix.clone().with_suffix(name.as_str());
                    let term = SymbolName::Value(symbol_name.clone());
                    let symbol = Symbol::Term(TermSymbol {
                        name: symbol_name,
                        type_signature: declarator.type_signature.clone(),

                        // This is a very expensive clone
                        // perhaps I _could_ move into here
                        body: declarator.body.clone(),
                    });

                    symbols.push(symbol.clone());
                    symbol_table.insert(term, symbol);
                }

                ast::Declaration::Module(_, decl) => {
                    modules.insert(prefix.clone().with_suffix(decl.name.as_str()));
                }

                ast::Declaration::Type(
                    _,
                    ast::TypeDeclaration {
                        name,
                        type_parameters,
                        declarator,
                    },
                ) => {
                    let symbol_name = prefix.clone().with_suffix(name.as_str());
                    let term = SymbolName::Type(symbol_name.clone());
                    let symbol = match declarator {
                        ast::TypeDeclarator::Record(_, record) => Symbol::Type(TypeSymbol {
                            definition: TypeDefinition::Record(RecordSymbol {
                                name: symbol_name,
                                type_parameters: type_parameters.clone(),
                                fields: record
                                    .fields
                                    .iter()
                                    .map(|decl| FieldSymbol {
                                        name: decl.name.clone(),
                                        type_signature: decl.type_signature.clone(),
                                    })
                                    .collect(),
                            }),
                            origin: TypeOrigin::UserDefined,
                            arity: type_parameters.len(),
                        }),

                        ast::TypeDeclarator::Coproduct(_, coproduct) => Symbol::Type(TypeSymbol {
                            definition: TypeDefinition::Coproduct(CoproductSymbol {
                                name: symbol_name,
                                type_parameters: type_parameters.clone(),
                                constructors: coproduct
                                    .constructors
                                    .iter()
                                    .map(|decl| ConstructorSymbol::<IdentifierPath> {
                                        name: IdentifierPath::new(decl.name.as_str()),
                                        signature: decl.signature.clone(),
                                    })
                                    .collect(),
                            }),
                            origin: TypeOrigin::UserDefined,
                            arity: type_parameters.len(),
                        }),
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
    Term(TermSymbol<A, GlobalName, LocalId>),
    Type(TypeSymbol<GlobalName>),
}

impl<A> Symbol<A, QualifiedName, Identifier> {
    pub fn dependencies(&self) -> HashSet<SymbolName<QualifiedName, Identifier>> {
        let mut deps = HashSet::default();

        match self {
            Self::Term(symbol) => {
                deps.extend(
                    symbol
                        .body
                        .free_variables()
                        .iter()
                        .map(|&id| SymbolName::Value(Identifier::Free(id.clone()))),
                );
            }

            Self::Type(..) => {
                //deps.extend(
                //    symbol
                //        .free_variables()
                //        .iter()
                //        .map(|&id| SymbolName::Value(Identifier::Free(id.clone()))),
                //);
            }
        }

        deps
    }
}

impl<A, GlobalName, LocalId> fmt::Display for Symbol<A, GlobalName, LocalId> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct TypeSymbol<GlobalName> {
    pub definition: TypeDefinition<GlobalName>,
    pub origin: TypeOrigin,
    pub arity: usize,
}

#[derive(Debug, Clone)]
pub enum TypeOrigin {
    UserDefined,
    Builtin,
}

#[derive(Debug, Clone)]
pub enum TypeDefinition<GlobalName> {
    Record(RecordSymbol<GlobalName>),
    Coproduct(CoproductSymbol<GlobalName>),
    Builtin(BaseType),
}

impl<GlobalName> TypeDefinition<GlobalName> {
    pub fn is_base_type(&self) -> bool {
        matches!(self, Self::Builtin(..))
    }
}

impl TypeSymbol<QualifiedName> {
    pub fn qualified_name(&self) -> QualifiedName {
        match &self.definition {
            TypeDefinition::Record(symbol) => symbol.name.clone(),
            TypeDefinition::Coproduct(symbol) => symbol.name.clone(),
            TypeDefinition::Builtin(base_type) => base_type.qualified_name(),
        }
    }
}

impl TypeSymbol<QualifiedName> {
    pub fn type_parameters(&self) -> &[parser::Identifier] {
        match &self.definition {
            TypeDefinition::Record(sym) => &sym.type_parameters,
            TypeDefinition::Coproduct(sym) => &sym.type_parameters,
            TypeDefinition::Builtin(..) => &[],
        }
    }

    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        match &self.definition {
            TypeDefinition::Record(symbol) => symbol.free_variables(),
            TypeDefinition::Coproduct(symbol) => symbol.free_variables(),
            TypeDefinition::Builtin(..) => HashSet::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordSymbol<GlobalName> {
    pub name: GlobalName,
    pub type_parameters: Vec<parser::Identifier>,
    pub fields: Vec<FieldSymbol<GlobalName>>,
}

#[derive(Debug, Clone)]
pub struct FieldSymbol<GlobalName> {
    pub name: parser::Identifier,
    pub type_signature: ast::TypeExpression<ParseInfo, GlobalName>,
}

impl RecordSymbol<QualifiedName> {
    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        self.fields
            .iter()
            .flat_map(|field| field.type_signature.free_variables())
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol<GlobalName> {
    pub name: GlobalName,
    pub type_parameters: Vec<parser::Identifier>,
    pub constructors: Vec<ConstructorSymbol<GlobalName>>,
}

impl CoproductSymbol<QualifiedName> {
    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        self.constructors
            .iter()
            .flat_map(|ctor| ctor.free_variables())
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct ConstructorSymbol<GlobalName> {
    pub name: GlobalName,
    pub signature: Vec<ast::TypeExpression<ParseInfo, GlobalName>>,
}

impl ConstructorSymbol<QualifiedName> {
    pub fn free_variables(&self) -> HashSet<&QualifiedName> {
        self.signature
            .iter()
            .flat_map(|ty_expr| ty_expr.free_variables())
            .collect()
    }
}

impl<GlobalName> TypeSymbol<GlobalName> {}

#[derive(Debug, Clone)]
pub struct TermSymbol<A, GlobalName, LocalId> {
    pub name: GlobalName,
    pub type_signature: Option<TypeSignature<ParseInfo, GlobalName>>,
    pub body: ast::Expr<A, LocalId>,
}

// Is this thing necessary?
#[derive(Debug, Clone)]
pub struct ModuleSymbol<A, GlobalName, LocalId> {
    pub name: GlobalName,
    pub contents: Vec<Symbol<A, GlobalName, LocalId>>,
}

#[derive(Debug, Default)]
struct DeBruijnIndex(Vec<parser::Identifier>);

impl DeBruijnIndex {
    fn resolve(&self, id: &parser::Identifier) -> Identifier {
        if let Some(index) = self.0.iter().rposition(|n| n == id) {
            Identifier::Bound(index)
        } else {
            Identifier::Free(QualifiedName::from_root_symbol(id.to_owned()))
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

impl parser::TypeExpression {
    pub fn resolve_names(
        &self,
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> TypeExpression {
        match self {
            Self::Constructor(a, name) => {
                // TODO: Is this where this happens? What exactly is _this_?
                // Resolve local name against _import prefixes_?
                let new_name = if name.tail.is_empty() {
                    if BaseType::is_name(&name.head) {
                        name.as_builtin_module_member()
                    } else {
                        name.as_root_module_member()
                    }
                } else {
                    name.clone()
                };

                TypeExpression::Constructor(*a, symbols.resolve_member_path(&new_name))
            }
            Self::Parameter(a, name) => TypeExpression::Parameter(*a, name.clone()),
            Self::Apply(a, apply) => TypeExpression::Apply(
                *a,
                TypeApply {
                    function: apply.function.resolve_names(symbols).into(),
                    argument: apply.argument.resolve_names(symbols).into(),
                    phase: PhantomData,
                },
            ),
            Self::Arrow(a, arrow) => TypeExpression::Arrow(
                *a,
                TypeArrow {
                    domain: arrow.domain.resolve_names(symbols).into(),
                    codomain: arrow.codomain.resolve_names(symbols).into(),
                },
            ),
        }
    }
}

impl parser::Expr {
    pub fn resolve_names(
        &self,
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Expr {
        self.resolve(&mut DeBruijnIndex::default(), symbols)
    }

    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
            Self::Sequence(a, node) => Expr::Sequence(*a, node.resolve(names, symbols)),
        }
    }
}

impl parser::SelfReference {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
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
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Projection {
        Projection {
            base: self.base.resolve(names, symbols).into(),
            select: self.select.clone(),
        }
    }
}

impl parser::Sequence {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) -> Sequence {
        Sequence {
            this: self.this.resolve(names, symbols).into(),
            and_then: self.and_then.resolve(names, symbols).into(),
        }
    }
}

impl RawCompilationContext {
    // Move to namer.rs
    // This does not need the symbols in any particular order, so long as all
    // modules are known
    pub fn rename_symbols(self) -> NamedCompilationContext {
        CompilationContext {
            modules: self.modules.clone(),
            symbols: self
                .symbols
                .iter()
                //                   The builtins must receive a name prefigured with __builtin__ here
                //                   or they cannot be resolved
                .map(|(id, symbol)| (self.rename_term_id(id), self.rename_symbol(symbol)))
                .collect(),
            phase: PhantomData,
        }
    }

    fn rename_term_id(&self, id: &RawTermId) -> TermId {
        match id {
            SymbolName::Type(id) => {
                // What is it really doing here?
                //   `id` either represents a user type or a builtin

                let new_name = if id.tail.is_empty() {
                    if BaseType::is_name(&id.head) {
                        id.as_builtin_module_member()
                    } else {
                        id.as_root_module_member()
                    }
                } else {
                    id.clone()
                };

                SymbolName::Type(self.resolve_member_path(&new_name))
            }
            SymbolName::Value(id) => {
                SymbolName::Value(Identifier::Free(self.resolve_member_path(id)))
            }
        }
    }

    pub fn resolve_member_path(&self, id: &parser::IdentifierPath) -> QualifiedName {
        self.resolve_module_path_expr(id)
            .expect(&format!("a valid type identifier path: {id}"))
            .into_member_path()
    }

    // Own and move instead?
    fn rename_symbol(&self, symbol: &RawSymbol) -> NamedSymbol {
        match symbol {
            Symbol::Term(symbol) => Symbol::Term(TermSymbol {
                name: self.resolve_member_path(&symbol.name),
                type_signature: symbol
                    .type_signature
                    .clone()
                    .map(|ts| ts.map(|te| te.resolve_names(self))),
                body: symbol.body.resolve_names(self),
            }),

            Symbol::Type(symbol) => Symbol::Type(match &symbol.definition {
                TypeDefinition::Record(record) => TypeSymbol {
                    definition: TypeDefinition::Record(RecordSymbol {
                        name: self.resolve_member_path(&record.name),
                        type_parameters: record.type_parameters.clone(),
                        fields: record
                            .fields
                            .iter()
                            .map(|symbol| FieldSymbol {
                                name: symbol.name.clone(),
                                type_signature: symbol.type_signature.resolve_names(self),
                            })
                            .collect(),
                    }),
                    origin: symbol.origin.clone(),
                    arity: symbol.arity.clone(),
                },

                TypeDefinition::Coproduct(coproduct) => TypeSymbol {
                    definition: TypeDefinition::Coproduct(CoproductSymbol {
                        name: self.resolve_member_path(&coproduct.name),
                        type_parameters: coproduct.type_parameters.clone(),
                        constructors: coproduct
                            .constructors
                            .iter()
                            .map(|symbol| ConstructorSymbol {
                                name: self.resolve_member_path(&symbol.name),
                                signature: symbol
                                    .signature
                                    .iter()
                                    .map(|te| te.resolve_names(self))
                                    .collect(),
                            })
                            .collect(),
                    }),
                    origin: symbol.origin.clone(),
                    arity: symbol.arity.clone(),
                },

                TypeDefinition::Builtin(base_type) => TypeSymbol {
                    definition: TypeDefinition::Builtin(base_type.clone()),
                    origin: symbol.origin.clone(),
                    arity: symbol.arity,
                },
            }),
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

impl fmt::Display for QualifiedNameExpr {
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

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { module, member } = self;
        write!(f, "{module}::{member}")
    }
}

impl<TypeId, ValueId> fmt::Display for SymbolName<TypeId, ValueId>
where
    TypeId: fmt::Display,
    ValueId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(id) => write!(f, "{id}"),
            Self::Value(id) => write!(f, "{id}"),
        }
    }
}
