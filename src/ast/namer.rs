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
        self, ApplyTypeExpr, ArrowTypeExpr, CompilationUnit, Declaration, ProductElement, Tree,
        TupleTypeExpr,
        pattern::{StructPattern, TuplePattern},
    },
    parser::{self, IdentifierPath, ParseInfo},
    stdlib,
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
pub type Construct = ast::Construct<ParseInfo, Identifier>;
pub type Sequence = ast::Sequence<ParseInfo, Identifier>;
pub type Deconstruct = ast::Deconstruct<ParseInfo, Identifier>;
pub type IfThenElse = ast::IfThenElse<ParseInfo, Identifier>;
pub type Interpolate = ast::Interpolate<ParseInfo, Identifier>;
pub type Segment = ast::Segment<ParseInfo, Identifier>;
pub type MatchClause = ast::pattern::MatchClause<ParseInfo, Identifier>;
pub type Pattern = ast::pattern::Pattern<ParseInfo, Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<ParseInfo, Identifier>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, QualifiedName>;
pub type TypeSignature = ast::TypeSignature<ParseInfo, QualifiedName>;

type ParserCompilationContext =
    CompilationContext<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
type ParserSymbol = Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
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

            Self::InvokeBridge(_, bridge) => {
                free.insert(bridge.qualified_name());
            }

            Self::RecursiveLambda(_, rec) => rec.lambda.body.gather_free_variables(free),

            Self::Lambda(_, lambda) => {
                // not quite right?
                // surely remove lambda.param?
                lambda.body.gather_free_variables(free)
            }

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

            Self::Construct(
                _,
                ast::Construct {
                    constructor: Identifier::Free(id),
                    arguments,
                },
            ) => {
                free.insert(id);
                for arg in arguments {
                    arg.gather_free_variables(free);
                }
            }

            Self::Deconstruct(
                _,
                ast::Deconstruct {
                    scrutinee,
                    match_clauses,
                },
            ) => {
                scrutinee.gather_free_variables(free);
                for clause in match_clauses {
                    clause.consequent.gather_free_variables(free);
                }
            }

            Self::Sequence(_, ast::Sequence { this, and_then }) => {
                this.gather_free_variables(free);
                and_then.gather_free_variables(free);
            }

            Self::If(_, the) => {
                the.predicate.gather_free_variables(free);
                the.consequent.gather_free_variables(free);
                the.alternate.gather_free_variables(free);
            }

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

            Self::Tuple(_, tuple) => {
                for el in &tuple.0 {
                    el.gather_free_variables(free);
                }
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

impl Identifier {
    pub fn try_as_free(&self) -> Option<&QualifiedName> {
        if let Self::Free(name) = self {
            Some(name)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NameExpr {
    module_prefix: parser::IdentifierPath,
    member: String,
    projections: Vec<String>,
}

impl NameExpr {
    fn into_projection(self, pi: ParseInfo) -> Expr {
        let path = QualifiedName {
            module: self.module_prefix,
            member: parser::Identifier::from_str(&self.member),
        };

        self.projections
            .iter()
            .fold(Expr::Variable(pi, Identifier::Free(path)), |base, field| {
                ast::Expr::Project(
                    pi,
                    ast::Projection {
                        base: base.into(),
                        select: ProductElement::Name(parser::Identifier::from_str(field.as_str())),
                    },
                )
            })
    }

    pub fn into_qualified_name(self) -> QualifiedName {
        QualifiedName {
            module: self.module_prefix,
            member: parser::Identifier::from_str(&self.member),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct QualifiedName {
    module: parser::IdentifierPath,
    member: parser::Identifier,
}

impl QualifiedName {
    pub fn new(module: parser::IdentifierPath, member: &str) -> QualifiedName {
        Self {
            module,
            member: parser::Identifier::from_str(member),
        }
    }

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

    pub fn into_identifier_path(self) -> parser::IdentifierPath {
        parser::IdentifierPath {
            head: self.module.head,
            tail: {
                let mut tail = self.module.tail;
                tail.push(self.member.as_str().to_owned());

                tail
            },
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

        println!("dependencies: unsatisfied {:?}", unsatisfieds);

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
pub enum SymbolName {
    Type(QualifiedName),
    Term(QualifiedName),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ModuleMember {
    Type(parser::Identifier),
    Term(parser::Identifier),
}

impl parser::IdentifierPath {
    pub fn try_into_qualified_name(self) -> Option<QualifiedName> {
        println!("try_into_qualified_name: {}", self);
        let Self { head, mut tail } = self;

        let member = tail.pop();
        println!("try_into_qualified_name: member {member:?}");

        member.map(|member| QualifiedName {
            module: parser::IdentifierPath { head, tail },
            member: parser::Identifier::from_str(&member),
        })
    }
}

// "Modules do not exist" - they should get their own table.
#[derive(Debug, Clone)]
pub struct CompilationContext<A, GlobalName, LocalId> {
    pub module_members: HashMap<parser::IdentifierPath, Vec<ModuleMember>>,
    pub member_module: HashMap<ModuleMember, parser::IdentifierPath>,
    pub symbols: HashMap<SymbolName, Symbol<A, GlobalName, LocalId>>,
    pub phase: PhantomData<(A, GlobalName, LocalId)>,
}

impl<A, TypeId, ValueId> Default for CompilationContext<A, TypeId, ValueId> {
    fn default() -> Self {
        Self {
            module_members: HashMap::default(),
            member_module: HashMap::default(),
            symbols: HashMap::default(),
            phase: PhantomData,
        }
    }
}

impl ParserCompilationContext {
    fn resolve_as_term_member(&self, path: &parser::IdentifierPath) -> parser::IdentifierPath {
        println!("resolve_as_term_member: {path}");
        self.member_module
            .get(&ModuleMember::Term(parser::Identifier::from_str(
                path.head.as_str(),
            )))
            .map(|module| path.in_module(module))
            .unwrap_or_else(|| path.clone())
    }

    // This ought to return QualifiedName
    fn resolve_as_type_member(&self, path: &parser::IdentifierPath) -> Option<QualifiedName> {
        println!("resolve_as_type_member: {path}");

        self.member_module
            .get(&ModuleMember::Type(parser::Identifier::from_str(
                path.last(),
            )))
            .inspect(|x| println!("resolve_as_type_member: x {path} -- {x}"))
            .and_then(|module| path.in_module(module).try_into_qualified_name())
    }

    pub fn resolve_module_path_expr(&self, path: &parser::IdentifierPath) -> Option<NameExpr> {
        println!("resolve_module_path_expr: {path}");

        let mut module_path = vec![];
        let mut member = vec![];
        let mut in_module_prefix = true;

        for segment in path.iter() {
            if in_module_prefix {
                module_path.push(segment);
                let identifier_path = parser::IdentifierPath::try_from_components(&module_path)?;

                if !self.module_members.contains_key(&identifier_path) {
                    module_path.pop();
                    in_module_prefix = false;
                    member.push(segment);
                }
            } else {
                member.push(segment);
            }
        }

        let mut members = member.iter().map(|&s| s.to_owned());
        Some(NameExpr {
            module_prefix: parser::IdentifierPath::try_from_components(&module_path)?,
            member: members.next()?,
            projections: members.collect(),
        })
    }

    pub fn from(program: &CompilationUnit<ParseInfo>) -> Self {
        let mut symbols = HashMap::default();
        let mut modules = HashMap::default();

        let builtins = parser::IdentifierPath::new(ast::BUILTIN_MODULE_NAME);

        modules.insert(parser::IdentifierPath::new(ast::ROOT_MODULE_NAME), vec![]);
        modules.insert(parser::IdentifierPath::new(ast::STDLIB_MODULE_NAME), vec![]);
        modules.insert(builtins.clone(), vec![]);

        // Change when I move the base types into a module proper
        for symbol in stdlib::import() {
            println!("from: {symbol:?}");
            modules
                .entry(symbol.name.module.clone())
                .or_default()
                .push(ModuleMember::Term(symbol.name.member.clone()));
            symbols.insert(SymbolName::Term(symbol.name.clone()), Symbol::Term(symbol));
        }

        symbols.insert(
            SymbolName::Type(QualifiedName::builtin("Int")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Int),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );
        modules
            .entry(builtins.clone())
            .or_default()
            .push(ModuleMember::Type(parser::Identifier::from_str("Int")));

        symbols.insert(
            SymbolName::Type(QualifiedName::builtin("Text")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Text),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );
        modules
            .entry(builtins.clone())
            .or_default()
            .push(ModuleMember::Type(parser::Identifier::from_str("Text")));

        symbols.insert(
            SymbolName::Type(QualifiedName::builtin("Bool")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Bool),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );
        modules
            .entry(builtins.clone())
            .or_default()
            .push(ModuleMember::Type(parser::Identifier::from_str("Bool")));

        symbols.insert(
            SymbolName::Type(QualifiedName::builtin("Unit")),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Builtin(BaseType::Unit),
                origin: TypeOrigin::Builtin,
                arity: 0,
            }),
        );
        modules
            .entry(builtins.clone())
            .or_default()
            .push(ModuleMember::Type(parser::Identifier::from_str("Unit")));

        Self::collect_symbols(
            parser::IdentifierPath::new(program.root.name.as_str()),
            &program.root.declarator.members,
            &mut modules,
            &mut symbols,
        );

        let member_module = modules
            .iter()
            .flat_map(|(module, members)| {
                members
                    .iter()
                    .cloned()
                    .map(|member| (member, module.clone()))
            })
            .collect();

        Self {
            module_members: modules,
            member_module,
            symbols,
            phase: PhantomData,
        }
    }

    // This could just as well keep a running module_path of varified
    // modules. Shouldn't I just rewrite this sucker?
    pub fn collect_symbols(
        module_path: parser::IdentifierPath,
        declarations: &[Declaration<ParseInfo>],
        module_members: &mut HashMap<parser::IdentifierPath, Vec<ModuleMember>>,
        symbols: &mut HashMap<SymbolName, ParserSymbol>,
    ) {
        for decl in declarations {
            match decl {
                ast::Declaration::Value(_, ast::ValueDeclaration { name, declarator }) => {
                    println!("from: add {name} to {module_path}");
                    module_members
                        .entry(module_path.clone())
                        .or_default()
                        .push(ModuleMember::Term(name.clone()));

                    let name = QualifiedName::new(module_path.clone(), name.as_str());
                    let symbol = TermSymbol {
                        name: name.clone(),
                        type_signature: declarator.type_signature.clone(),
                        body: declarator.body.clone().into(),
                    };

                    symbols.insert(SymbolName::Term(name), Symbol::Term(symbol));
                }

                ast::Declaration::Module(_, decl) => {
                    module_members.entry(module_path.clone()).or_default().push(
                        // Think about this. Do modules and terms share namespace?
                        ModuleMember::Term(parser::Identifier::from_str(decl.name.as_str())),
                    );
                    let module_path = module_path.clone().with_suffix(decl.name.as_str());
                    module_members.insert(module_path.clone(), vec![]);

                    Self::collect_symbols(
                        module_path,
                        &decl.declarator.members,
                        module_members,
                        symbols,
                    );
                }

                ast::Declaration::Type(
                    pi,
                    ast::TypeDeclaration {
                        name,
                        type_parameters,
                        declarator,
                    },
                ) => {
                    println!("collect_symbols: add type {name} to {module_path}");
                    module_members
                        .entry(module_path.clone())
                        .or_default()
                        .push(ModuleMember::Type(name.clone()));

                    let name = QualifiedName::new(module_path.clone(), name.as_str());
                    let symbol = match declarator {
                        ast::TypeDeclarator::Record(_, record) => {
                            make_record_type_symbol(type_parameters, &name, record)
                        }

                        ast::TypeDeclarator::Coproduct(_, coproduct) => {
                            let constructors = coproduct
                                .constructors
                                .iter()
                                .map(|decl| ConstructorSymbol {
                                    name: QualifiedName::new(
                                        module_path.clone(),
                                        decl.name.as_str(),
                                    ),
                                    signature: decl.signature.clone(),
                                })
                                .collect::<Vec<_>>();

                            println!("collect_symbols: module {module_path}");
                            collect_coproduct_constructors(
                                *pi,
                                symbols,
                                type_parameters,
                                &name,
                                &constructors,
                                module_members.entry(module_path.clone()).or_default(),
                            );

                            TypeSymbol {
                                definition: TypeDefinition::Coproduct(CoproductSymbol {
                                    name: name.clone(),
                                    type_parameters: type_parameters.clone(),
                                    constructors,
                                }),
                                origin: TypeOrigin::UserDefined,
                                arity: type_parameters.len(),
                            }
                        }
                    };

                    symbols.insert(SymbolName::Type(name), Symbol::Type(symbol));
                }
            };
        }
    }
}

fn collect_coproduct_constructors(
    pi: ParseInfo,
    symbols: &mut HashMap<SymbolName, ParserSymbol>,
    type_parameters: &Vec<parser::Identifier>,
    type_constructor_name: &QualifiedName,
    constructors: &Vec<ConstructorSymbol<parser::IdentifierPath>>,
    module_members: &mut Vec<ModuleMember>,
) {
    for constructor in constructors {
        module_members.push(ModuleMember::Term(parser::Identifier::from_str(
            &constructor.name.member.as_str().to_owned(),
        )));
        let symbol = constructor.make_constructor_term(pi, type_parameters, type_constructor_name);
        symbols.insert(
            SymbolName::Term(constructor.name.clone()),
            Symbol::Term(symbol),
        );
    }
}

fn make_record_type_symbol(
    type_parameters: &Vec<parser::Identifier>,
    symbol_name: &QualifiedName,
    record: &ast::RecordDeclarator<ParseInfo>,
) -> TypeSymbol<parser::IdentifierPath> {
    TypeSymbol {
        definition: TypeDefinition::Record(RecordSymbol {
            name: symbol_name.clone(),
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
    }
}

#[derive(Debug, Clone)]
pub enum Symbol<A, GlobalName, LocalId> {
    Term(TermSymbol<A, GlobalName, LocalId>),
    Type(TypeSymbol<GlobalName>),
}

impl<A> Symbol<A, QualifiedName, Identifier> {
    pub fn dependencies(&self) -> HashSet<SymbolName> {
        let mut deps = HashSet::default();

        match self {
            Self::Term(symbol) => {
                deps.extend(
                    symbol
                        .body()
                        .free_variables()
                        .iter()
                        .map(|&id| SymbolName::Term(id.clone())),
                );
            }

            Self::Type(..) => {}
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

#[derive(Debug, Copy, Clone)]
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

    pub fn type_parameters(&self) -> &[parser::Identifier] {
        match &self.definition {
            TypeDefinition::Record(sym) => &sym.type_parameters,
            TypeDefinition::Coproduct(sym) => &sym.type_parameters,
            TypeDefinition::Builtin(..) => &[],
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordSymbol<GlobalName> {
    pub name: QualifiedName,
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
    pub name: QualifiedName,
    pub type_parameters: Vec<parser::Identifier>,
    pub constructors: Vec<ConstructorSymbol<GlobalName>>,
}

#[derive(Debug, Clone)]
pub struct ConstructorSymbol<GlobalName> {
    pub name: QualifiedName,
    pub signature: Vec<ast::TypeExpression<ParseInfo, GlobalName>>,
}

impl ConstructorSymbol<parser::IdentifierPath> {
    fn make_applied_type_constructor(
        &self,
        pi: ParseInfo,
        type_parameters: &[parser::Identifier],
        type_constructor_name: &QualifiedName,
    ) -> parser::TypeExpression {
        type_parameters.iter().cloned().fold(
            parser::TypeExpression::Constructor(
                pi,
                type_constructor_name.clone().into_identifier_path(),
            ),
            |function, argument| {
                parser::TypeExpression::Apply(
                    pi,
                    ApplyTypeExpr {
                        function: function.into(),
                        argument: parser::TypeExpression::Parameter(pi, argument).into(),
                        phase: PhantomData,
                    },
                )
            },
        )
    }

    fn make_constructor_term(
        &self,
        pi: ParseInfo,
        type_parameters: &[parser::Identifier],
        type_constructor_name: &QualifiedName,
    ) -> TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath> {
        TermSymbol {
            name: self.name.clone(),
            type_signature: self
                .make_type_signature(pi, type_parameters, type_constructor_name)
                .into(),
            body: self.make_curried_constructor_term(pi).into(),
        }
    }

    fn make_type_signature(
        &self,
        pi: ParseInfo,
        type_parameters: &[parser::Identifier],
        type_constructor_name: &QualifiedName,
    ) -> parser::TypeSignature {
        parser::TypeSignature {
            universal_quantifiers: type_parameters.to_vec(),
            body: self.signature.iter().cloned().rfold(
                self.make_applied_type_constructor(pi, type_parameters, type_constructor_name),
                |rhs, lhs| {
                    parser::TypeExpression::Arrow(
                        pi,
                        ArrowTypeExpr {
                            domain: lhs.into(),
                            codomain: rhs.into(),
                        },
                    )
                },
            ),
            phase: PhantomData,
        }
    }

    pub fn make_curried_constructor_term(&self, pi: ParseInfo) -> parser::Expr {
        let terms = (0..self.signature.len()).into_iter();
        let construct = parser::Expr::Construct(
            pi,
            ast::Construct {
                constructor: self.name.clone().into_identifier_path(),
                arguments: terms
                    .clone()
                    .map(|i| {
                        parser::Expr::Variable(pi, parser::IdentifierPath::new(&format!("p{i}")))
                            .into()
                    })
                    .collect(),
            },
        );

        terms.rfold(construct, |z, i| {
            parser::Expr::Lambda(
                pi,
                parser::Lambda {
                    parameter: parser::IdentifierPath::new(&format!("p{i}")),
                    body: z.into(),
                },
            )
        })
    }
}

#[derive(Debug, Clone)]
pub struct TermSymbol<A, GlobalName, LocalId> {
    pub name: QualifiedName,
    pub type_signature: Option<ast::TypeSignature<ParseInfo, GlobalName>>,
    pub body: Option<ast::Expr<A, LocalId>>,
}

impl<A, GlobalName, LocalId> TermSymbol<A, GlobalName, LocalId> {
    pub fn body(&self) -> &ast::Expr<A, LocalId> {
        self.body
            .as_ref()
            .expect("Internal assertion - empty TermSymbol body.")
    }
}

// Is this thing necessary?
#[derive(Debug, Clone)]
pub struct ModuleSymbol<A, GlobalName, LocalId> {
    pub name: QualifiedName,
    pub contents: Vec<Symbol<A, GlobalName, LocalId>>,
}

#[derive(Debug, Default)]
struct DeBruijnIndex {
    stack: Vec<parser::Identifier>,
    restore_points: Vec<usize>,
}

impl DeBruijnIndex {
    fn mark(&mut self) {
        self.restore_points.push(self.stack.len());
    }

    fn restore(&mut self) {
        self.stack.truncate(
            self.restore_points
                .pop()
                .expect("Restore without restore points"),
        );
    }

    fn try_resolve_bound(&self, id: &parser::Identifier) -> Option<Identifier> {
        if let bound @ Identifier::Bound(..) = self.resolve(id) {
            Some(bound)
        } else {
            None
        }
    }

    fn resolve(&self, id: &parser::Identifier) -> Identifier {
        if let Some(index) = self.stack.iter().rposition(|n| n == id) {
            Identifier::Bound(index)
        } else {
            Identifier::Free(QualifiedName::from_root_symbol(id.to_owned()))
        }
    }

    fn bind_and_then<F, A>(&mut self, id: parser::Identifier, mut block: F) -> A
    where
        F: FnMut(&mut DeBruijnIndex, Identifier) -> A,
    {
        let de_bruijn_index = self.stack.len();
        self.stack.push(id);
        let a = block(self, Identifier::Bound(de_bruijn_index));
        self.stack.pop();
        a
    }

    fn bind(&mut self, id: parser::Identifier) -> usize {
        let de_bruijn_index = self.stack.len();
        self.stack.push(id);
        de_bruijn_index
    }
}

impl parser::TypeExpression {
    pub fn resolve_names(&self, symbols: &ParserCompilationContext) -> TypeExpression {
        match self {
            Self::Constructor(a, name) => TypeExpression::Constructor(
                *a,
                symbols
                    .resolve_as_type_member(&name)
                    .expect("Resolvable type name"),
            ),

            Self::Parameter(a, name) => TypeExpression::Parameter(*a, name.clone()),

            Self::Apply(a, apply) => TypeExpression::Apply(
                *a,
                ApplyTypeExpr {
                    function: apply.function.resolve_names(symbols).into(),
                    argument: apply.argument.resolve_names(symbols).into(),
                    phase: PhantomData,
                },
            ),

            Self::Arrow(a, arrow) => TypeExpression::Arrow(
                *a,
                ArrowTypeExpr {
                    domain: arrow.domain.resolve_names(symbols).into(),
                    codomain: arrow.codomain.resolve_names(symbols).into(),
                },
            ),

            Self::Tuple(a, tuple) => TypeExpression::Tuple(
                *a,
                TupleTypeExpr(tuple.0.iter().map(|te| te.resolve_names(symbols)).collect()),
            ),
        }
    }
}

fn map_lower_tuples(body: Tree<ParseInfo, IdentifierPath>) -> Tree<ParseInfo, IdentifierPath> {
    Rc::unwrap_or_clone(body).lower_tuples().into()
}

impl parser::Expr {
    pub fn lower_tuples(self) -> parser::Expr {
        match self {
            parser::Expr::Variable(..)
            | parser::Expr::Constant(..)
            | parser::Expr::InvokeBridge(..) => self,

            parser::Expr::RecursiveLambda(a, the) => parser::Expr::RecursiveLambda(
                a,
                parser::SelfReferential {
                    own_name: the.own_name,
                    lambda: parser::Lambda {
                        parameter: the.lambda.parameter,
                        body: map_lower_tuples(the.lambda.body),
                    },
                },
            ),

            parser::Expr::Lambda(a, the) => parser::Expr::Lambda(
                a,
                parser::Lambda {
                    parameter: the.parameter,
                    body: map_lower_tuples(the.body),
                },
            ),

            parser::Expr::Apply(a, the) => parser::Expr::Apply(
                a,
                parser::Apply {
                    function: map_lower_tuples(the.function),
                    argument: map_lower_tuples(the.argument),
                },
            ),

            parser::Expr::Let(a, the) => parser::Expr::Let(
                a,
                parser::Binding {
                    binder: the.binder,
                    bound: map_lower_tuples(the.bound),
                    body: map_lower_tuples(the.body),
                },
            ),

            parser::Expr::Tuple(a, the) => {
                let elements = the.elements;
                parser::Expr::Tuple(
                    a,
                    parser::Tuple {
                        elements: unspine_tuple(elements),
                    },
                )
            }

            parser::Expr::Record(a, the) => parser::Expr::Record(
                a,
                parser::Record {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| (label, map_lower_tuples(e)))
                        .collect(),
                },
            ),

            parser::Expr::Construct(a, the) => parser::Expr::Construct(
                a,
                parser::Construct {
                    constructor: the.constructor,
                    arguments: the
                        .arguments
                        .into_iter()
                        .map(|e| map_lower_tuples(e))
                        .collect(),
                },
            ),

            parser::Expr::Project(a, the) => parser::Expr::Project(
                a,
                parser::Projection {
                    base: map_lower_tuples(the.base),
                    select: the.select,
                },
            ),

            parser::Expr::Sequence(a, the) => parser::Expr::Sequence(
                a,
                parser::Sequence {
                    this: map_lower_tuples(the.this),
                    and_then: map_lower_tuples(the.and_then),
                },
            ),

            parser::Expr::Deconstruct(a, the) => parser::Expr::Deconstruct(
                a,
                parser::Deconstruct {
                    scrutinee: map_lower_tuples(the.scrutinee),
                    match_clauses: the
                        .match_clauses
                        .iter()
                        .map(|clause| parser::MatchClause {
                            pattern: clause.pattern.normalize(),
                            consequent: map_lower_tuples(clause.consequent.clone()),
                        })
                        .collect(),
                },
            ),

            parser::Expr::If(a, the) => parser::Expr::If(
                a,
                parser::IfThenElse {
                    predicate: map_lower_tuples(the.predicate),
                    consequent: map_lower_tuples(the.consequent),
                    alternate: map_lower_tuples(the.alternate),
                },
            ),

            parser::Expr::Interpolate(a, ast::Interpolate(the)) => parser::Expr::Interpolate(
                a,
                ast::Interpolate(
                    the.into_iter()
                        .map(|s| match s {
                            ast::Segment::Literal(a, literal) => ast::Segment::Literal(a, literal),
                            ast::Segment::Expression(expr) => {
                                ast::Segment::Expression(map_lower_tuples(expr))
                            }
                        })
                        .collect(),
                ),
            ),
        }
    }

    pub fn resolve_names(&self, symbols: &ParserCompilationContext) -> Expr {
        self.resolve(&mut DeBruijnIndex::default(), symbols)
    }

    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Expr {
        match self {
            Self::Variable(a, identifier_path) => {
                println!("resolve: {identifier_path}");
                if let Some(bound) =
                    names.try_resolve_bound(&parser::Identifier::from_str(&identifier_path.head))
                {
                    into_projection(a, bound, identifier_path)
                } else if let Some(path) =
                    // I guess this would have to resolve the this name against every
                    // imported namespace
                    symbols.resolve_module_path_expr(
                        &symbols.resolve_as_term_member(&identifier_path),
                    )
                {
                    path.into_projection(*a)
                } else {
                    panic!("Unresolved symbol {}", identifier_path)
                }
            }

            Self::InvokeBridge(a, bridge) => Expr::InvokeBridge(*a, bridge.clone()),

            Self::Constant(a, literal) => Expr::Constant(*a, literal.clone()),

            Self::RecursiveLambda(a, node) => {
                Expr::RecursiveLambda(*a, node.resolve(names, symbols))
            }

            Self::Lambda(a, node) => Expr::Lambda(*a, node.resolve(names, symbols)),

            Self::Apply(a, node) => Expr::Apply(*a, node.resolve(names, symbols)),

            Self::Let(a, node) => Expr::Let(*a, node.resolve(names, symbols)),

            Self::Record(a, node) => Expr::Record(*a, node.resolve(names, symbols)),

            Self::Tuple(a, node) => Expr::Tuple(*a, node.resolve(names, symbols)),

            Self::Construct(a, node) => Expr::Construct(*a, node.resolve(names, symbols)),

            Self::Project(a, node) => Expr::Project(*a, node.resolve(names, symbols)),

            Self::Sequence(a, node) => Expr::Sequence(*a, node.resolve(names, symbols)),

            Self::Deconstruct(a, node) => Expr::Deconstruct(*a, node.resolve(names, symbols)),

            Self::If(a, node) => Expr::If(*a, node.resolve(names, symbols)),

            Self::Interpolate(a, node) => Expr::Interpolate(*a, node.resolve(names, symbols)),
        }
    }
}

fn unspine_tuple(
    elements: Vec<ast::Tree<ParseInfo, IdentifierPath>>,
) -> Vec<ast::Tree<ParseInfo, IdentifierPath>> {
    elements
        .into_iter()
        .flat_map(|e| match (*e).clone() {
            // This is probably not correct - it flattens too much
            parser::Expr::Tuple(_, tuple) => unspine_tuple(tuple.elements.to_vec()),
            atom => vec![atom.into()],
        })
        .collect()
}

fn into_projection(pi: &ParseInfo, base: Identifier, path: &parser::IdentifierPath) -> Expr {
    path.tail
        .iter()
        .fold(Expr::Variable(*pi, base), |base, member| {
            Expr::Project(
                *pi,
                Projection {
                    base: base.into(),
                    select: ProductElement::Name(parser::Identifier::from_str(member)),
                },
            )
        })
}

impl parser::SelfReferential {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &ParserCompilationContext,
    ) -> SelfReferential {
        if let Some(own_name) = self.own_name.try_as_simple() {
            names.bind_and_then(own_name.clone(), |names, own_name| SelfReferential {
                own_name,
                lambda: self.lambda.resolve(names, symbols),
            })
        } else {
            panic!("Parser erroneously accepted a pathed identifier for recursive function name")
        }
    }
}

impl parser::Lambda {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Lambda {
        if let Some(parameter) = self.parameter.try_as_simple() {
            names.bind_and_then(parameter, |names, parameter| Lambda {
                parameter,
                body: self.body.resolve(names, symbols).into(),
            })
        } else {
            panic!("Parser erroneously accepted a pathed identifier for lambda parameter")
        }
    }
}

impl parser::Apply {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Apply {
        Apply {
            function: self.function.resolve(names, symbols).into(),
            argument: self.argument.resolve(names, symbols).into(),
        }
    }
}

impl parser::Binding {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Binding {
        if let Some(binder) = self.binder.try_as_simple() {
            let bound = Rc::new(self.bound.resolve(names, symbols));
            names.bind_and_then(binder, |names, binder| Binding {
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
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Record {
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
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Tuple {
        Tuple {
            elements: self
                .elements
                .iter()
                .map(|e| e.resolve(names, symbols).into())
                .collect(),
        }
    }
}

impl parser::Construct {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Construct {
        Construct {
            constructor: Identifier::Free(
                symbols.resolve_qualified(&symbols.resolve_as_term_member(&self.constructor)),
            ),
            arguments: self
                .arguments
                .iter()
                .map(|e| e.resolve(names, symbols).into())
                .collect(),
        }
    }
}

impl parser::Projection {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Projection {
        Projection {
            base: self.base.resolve(names, symbols).into(),
            select: self.select.clone(),
        }
    }
}

impl parser::Sequence {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Sequence {
        Sequence {
            this: self.this.resolve(names, symbols).into(),
            and_then: self.and_then.resolve(names, symbols).into(),
        }
    }
}

impl parser::Deconstruct {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &ParserCompilationContext,
    ) -> Deconstruct {
        Deconstruct {
            scrutinee: self.scrutinee.resolve(names, symbols).into(),
            match_clauses: self
                .match_clauses
                .iter()
                .map(|clause| clause.resolve(names, symbols))
                .collect(),
        }
    }
}

impl parser::IfThenElse {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> IfThenElse {
        IfThenElse {
            predicate: self.predicate.resolve(names, symbols).into(),
            consequent: self.consequent.resolve(names, symbols).into(),
            alternate: self.alternate.resolve(names, symbols).into(),
        }
    }
}

impl parser::Interpolate {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &ParserCompilationContext,
    ) -> Interpolate {
        let Self(segments) = self;
        ast::Interpolate(
            segments
                .into_iter()
                .map(|s| match s {
                    ast::Segment::Literal(a, literal) => ast::Segment::Literal(*a, literal.clone()),
                    ast::Segment::Expression(expr) => {
                        ast::Segment::Expression(expr.resolve(names, symbols).into())
                    }
                })
                .collect(),
        )
    }
}

impl parser::MatchClause {
    fn resolve(
        &self,
        names: &mut DeBruijnIndex,
        symbols: &ParserCompilationContext,
    ) -> MatchClause {
        let Self {
            pattern,
            consequent,
        } = self;
        names.mark();

        let clause = MatchClause {
            pattern: pattern.resolve(names, symbols),
            consequent: consequent.resolve(names, symbols).into(),
        };

        names.restore();
        clause
    }
}

impl parser::Pattern {
    fn resolve(&self, names: &mut DeBruijnIndex, symbols: &ParserCompilationContext) -> Pattern {
        match self {
            parser::Pattern::Coproduct(a, pattern) => Pattern::Coproduct(
                *a,
                ConstructorPattern {
                    constructor: Identifier::Free(
                        // Resolve this against imported namespaces
                        symbols.resolve_qualified(
                            &symbols.resolve_as_term_member(&pattern.constructor),
                        ),
                    ),
                    arguments: pattern
                        .arguments
                        .iter()
                        .map(|arg| arg.resolve(names, symbols))
                        .collect(),
                },
            ),

            parser::Pattern::Tuple(a, pattern) => Pattern::Tuple(
                *a,
                TuplePattern {
                    elements: pattern
                        .elements
                        .iter()
                        .map(|p| p.resolve(names, symbols))
                        .collect(),
                },
            ),

            parser::Pattern::Struct(a, pattern) => Pattern::Struct(
                *a,
                StructPattern {
                    fields: pattern
                        .fields
                        .iter()
                        .map(|(field, pattern)| (field.clone(), pattern.resolve(names, symbols)))
                        .collect(),
                },
            ),

            parser::Pattern::Literally(a, pattern) => Pattern::Literally(*a, pattern.clone()),

            parser::Pattern::Bind(a, pattern) => {
                if let Some(id) = pattern.try_as_simple() {
                    Pattern::Bind(*a, Identifier::Bound(names.bind(id)))
                } else {
                    panic!(
                        "Parser erroneously accepted a pathed identifier for recursive function name"
                    )
                }
            }
        }
    }
}

impl ParserCompilationContext {
    pub fn lower_tuples(&mut self) {
        for symbol in self.symbols.values_mut() {
            match symbol {
                Symbol::Term(symbol) => {
                    let body = symbol
                        .body
                        .take()
                        .expect("Internal Assertion - expected a symbol body.");
                    symbol.body = body.lower_tuples().into();
                }
                _ => (),
            }
        }
    }

    // Move to namer.rs
    // This does not need the symbols in any particular order, so long as all
    // modules are known
    pub fn rename_symbols(self) -> NamedCompilationContext {
        CompilationContext {
            // Any kind of renaming necessary here?
            module_members: self.module_members.clone(),
            // Any kind of renaming necessary here?
            member_module: self.member_module.clone(),
            symbols: self
                .symbols
                .iter()
                .map(|(id, symbol)| (id.clone(), self.rename_symbol(symbol)))
                .collect(),
            phase: PhantomData,
        }
    }

    pub fn resolve_qualified(&self, id: &parser::IdentifierPath) -> QualifiedName {
        self.resolve_module_path_expr(id)
            .expect(&format!("a valid type identifier path: {id}"))
            .into_qualified_name()
    }

    // Own and move instead?
    fn rename_symbol(&self, symbol: &ParserSymbol) -> NamedSymbol {
        match symbol {
            Symbol::Term(symbol) => Symbol::Term(TermSymbol {
                name: symbol.name.clone(),
                type_signature: symbol
                    .type_signature
                    .clone()
                    .map(|ts| ts.map(|te| te.resolve_names(self))),
                body: symbol.body().resolve_names(self).into(),
            }),

            Symbol::Type(symbol) => Symbol::Type(match &symbol.definition {
                TypeDefinition::Record(record) => TypeSymbol {
                    definition: TypeDefinition::Record(RecordSymbol {
                        name: record.name.clone(),
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
                    origin: symbol.origin,
                    arity: symbol.arity,
                },

                TypeDefinition::Coproduct(coproduct) => TypeSymbol {
                    definition: TypeDefinition::Coproduct(CoproductSymbol {
                        name: coproduct.name.clone(),
                        type_parameters: coproduct.type_parameters.clone(),
                        constructors: coproduct
                            .constructors
                            .iter()
                            .map(|symbol| ConstructorSymbol {
                                name: symbol.name.clone(),
                                signature: symbol
                                    .signature
                                    .iter()
                                    .map(|ty| ty.resolve_names(self))
                                    .collect(),
                            })
                            .collect(),
                    }),
                    origin: symbol.origin,
                    arity: symbol.arity,
                },

                TypeDefinition::Builtin(base_type) => TypeSymbol {
                    definition: TypeDefinition::Builtin(*base_type),
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

impl fmt::Display for NameExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}::{}.{}",
            self.module_prefix,
            self.member,
            self.projections.join("."),
        )
    }
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { module, member } = self;
        write!(f, "{module}::{member}")
    }
}

impl fmt::Display for SymbolName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(id) => write!(f, "{id}"),
            Self::Term(id) => write!(f, "{id}"),
        }
    }
}
