use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
    iter,
    marker::PhantomData,
    rc::Rc,
    vec,
};

use thiserror::Error;

use crate::{
    ast::{
        self, ApplyTypeExpr, ArrowTypeExpr, BUILTIN_MODULE_NAME, CompilationUnit, Declaration,
        ModuleDeclarator, ProductElement, STDLIB_MODULE_NAME, TupleTypeExpr, pattern::TuplePattern,
    },
    builtin,
    compiler::{Compilation, Compiler, Located, LocatedError},
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
pub type Injection = ast::Injection<ParseInfo, Identifier>;
pub type Sequence = ast::Sequence<ParseInfo, Identifier>;
pub type Deconstruct = ast::Deconstruct<ParseInfo, Identifier>;
pub type IfThenElse = ast::IfThenElse<ParseInfo, Identifier>;
pub type Interpolate = ast::Interpolate<ParseInfo, Identifier>;
pub type Segment = ast::Segment<ParseInfo, Identifier>;
pub type MatchClause = ast::pattern::MatchClause<ParseInfo, Identifier>;
pub type Pattern = ast::pattern::Pattern<ParseInfo, Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<ParseInfo, Identifier>;
pub type StructPattern = ast::pattern::StructPattern<ParseInfo, Identifier>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, QualifiedName>;
pub type TypeSignature = ast::TypeSignature<ParseInfo, QualifiedName>;
pub type TypeAscription = ast::TypeAscription<ParseInfo, Identifier>;
pub type ConstraintExpression = ast::ConstraintExpression<ParseInfo, QualifiedName>;

type ParserSymbolTable = SymbolTable<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
type ParserSymbol = Symbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>;
pub type NamedSymbolTable = SymbolTable<ParseInfo, QualifiedName, Identifier>;
pub type NamedSymbol = Symbol<ParseInfo, QualifiedName, Identifier>;

#[derive(Debug, Error)]
pub enum NameError {
    #[error("Unknown name `{0}`")]
    UnknownName(IdentifierPath),

    #[error("Parser erroneously accepted pathed identifier {0} for recursive function name")]
    BadOwnName(IdentifierPath),

    #[error("Parser erroneously accepted pathed identifier {0} for lambda parameter")]
    BadParameterName(IdentifierPath),

    #[error("Parser erroneously accepted pathed identifier {0} for binder")]
    BadBinderName(IdentifierPath),

    #[error("Unknown module member {0}")]
    UnknownMember(ModuleMember),
}

pub type Naming<A> = Result<A, Located<NameError>>;

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

            Self::Interpolate(_, ast::Interpolate(segments)) => {
                for s in segments {
                    if let ast::Segment::Expression(expr) = s {
                        expr.gather_free_variables(free)
                    }
                }
            }

            Self::Project(_, projection) => projection.base.gather_free_variables(free),

            Self::Inject(
                _,
                ast::Injection {
                    constructor,
                    arguments,
                },
            ) => {
                free.insert(constructor);
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

            Self::Ascription(_, the) => {
                the.ascribed_tree.gather_free_variables(free);
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Identifier {
    Bound(usize),
    Free(Box<QualifiedName>),
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

        self.projections.iter().fold(
            Expr::Variable(pi, Identifier::Free(path.into())),
            |base, field| {
                ast::Expr::Project(
                    pi,
                    ast::Projection {
                        base: base.into(),
                        select: ProductElement::Name(parser::Identifier::from_str(field.as_str())),
                    },
                )
            },
        )
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

    pub fn module(&self) -> &parser::IdentifierPath {
        &self.module
    }

    pub fn member(&self) -> &parser::Identifier {
        &self.member
    }
}

#[derive(Debug, Clone)]
pub struct DependencyMatrix<Id> {
    graph: HashMap<Id, Vec<Id>>,
    witnesses: HashSet<Id>,
}

impl<Id> Default for DependencyMatrix<Id> {
    fn default() -> Self {
        Self {
            graph: HashMap::default(),
            witnesses: HashSet::default(),
        }
    }
}

impl<Id> DependencyMatrix<Id>
where
    Id: Eq + Hash + fmt::Display + fmt::Debug,
{
    pub fn add_edge(&mut self, node: Id, vertices: Vec<Id>) {
        self.graph.insert(node, vertices);
    }

    pub fn add_witness(&mut self, witness: Id) {
        self.witnesses.insert(witness);
    }

    pub fn are_sound(&self) -> bool {
        //        let Self(map) = self;
        let unsatisfieds = self
            .graph
            .iter()
            .filter_map(|(_, deps)| deps.iter().find(|&dep| !self.graph.contains_key(dep)))
            .collect::<Vec<_>>();

        println!("dependencies: unsatisfied {:?}", unsatisfieds);

        unsatisfieds.is_empty()
    }

    pub fn in_resolvable_order(&self) -> Vec<&Id> {
        let mut resolved = Vec::with_capacity(self.graph.len());

        let mut graph = self
            .graph
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

        //        let mut queue = in_degrees
        //            .iter()
        //            .filter_map(|(node, in_degree)| (*in_degree == 0).then_some(*node))
        //            .collect::<VecDeque<_>>();

        let mut witnesses = VecDeque::new();
        let mut non_witnesses = VecDeque::new();

        for (&node, in_degree) in &in_degrees {
            if *in_degree == 0 {
                if self.witnesses.contains(node) {
                    witnesses.push_back(node);
                } else {
                    non_witnesses.push_back(node);
                }
            }
        }

        while let Some(independent) = if !witnesses.is_empty() {
            witnesses.pop_front()
        } else {
            non_witnesses.pop_front()
        } {
            resolved.push(independent);

            for (node, edges) in &mut graph {
                if edges.remove(independent)
                    && let Some(count) = in_degrees.get_mut(node)
                {
                    *count -= 1;
                    if *count == 0 {
                        //                        queue.push_back(node);
                        if self.witnesses.contains(node) {
                            witnesses.push_back(node);
                        } else {
                            non_witnesses.push_back(node);
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
pub enum SymbolName {
    Type(QualifiedName),
    Term(QualifiedName),
}

impl SymbolName {
    pub fn name(&self) -> &QualifiedName {
        match self {
            Self::Type(name) => name,
            Self::Term(name) => name,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ModuleMember {
    Type(parser::Identifier),
    Term(parser::Identifier),
}

impl parser::IdentifierPath {
    pub fn try_into_qualified_name(self) -> Option<QualifiedName> {
        let Self { head, mut tail } = self;

        let member = tail.pop();

        member.map(|member| QualifiedName {
            module: parser::IdentifierPath { head, tail },
            member: parser::Identifier::from_str(&member),
        })
    }
}

impl parser::RecordDeclarator {
    fn as_type_symbol(
        &self,
        type_parameters: &[parser::Identifier],
        name: &QualifiedName,
    ) -> TypeSymbol<IdentifierPath> {
        TypeSymbol {
            definition: TypeDefinition::Record(RecordSymbol {
                name: name.clone(),
                type_parameters: type_parameters.to_owned(),
                fields: self
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
}

impl parser::CoproductDeclarator {
    fn as_type_symbol(
        &self,
        type_parameters: Vec<parser::Identifier>,
        name: &QualifiedName,
        constructors: Vec<ConstructorSymbol<IdentifierPath>>,
    ) -> TypeSymbol<IdentifierPath> {
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
}

// Rename to Symbols? SymbolContext?
#[derive(Debug, Clone)]
pub struct SymbolTable<A, GlobalName, LocalId> {
    pub module_members: HashMap<parser::IdentifierPath, Vec<ModuleMember>>,
    pub member_modules: HashMap<ModuleMember, Vec<parser::IdentifierPath>>,

    // Why only one table?
    pub symbols: HashMap<SymbolName, Symbol<A, GlobalName, LocalId>>,
    pub imports: Vec<parser::IdentifierPath>,

    pub constraints: HashSet<QualifiedName>,
    pub witnesses: HashSet<QualifiedName>,
}

impl<A, TypeId, ValueId> Default for SymbolTable<A, TypeId, ValueId> {
    fn default() -> Self {
        Self {
            module_members: HashMap::default(),
            member_modules: HashMap::default(),
            symbols: HashMap::default(),
            imports: Vec::default(),
            constraints: HashSet::default(),
            witnesses: HashSet::default(),
        }
    }
}

impl ParserSymbolTable {
    // This ought to give a Result so that we can know what it failed to do
    fn resolve_free_term_name(
        &self,
        id: &parser::IdentifierPath,
        semantic_scope: &parser::IdentifierPath,
    ) -> Option<NameExpr> {
        let search_space = self
            .member_modules
            .get(&ModuleMember::Term(parser::Identifier::from_str(&id.head)))?;

        let parents = prefix_chain(semantic_scope);

        let mut search_order = parents.chain(self.imports.iter().rev().cloned());

        // Could this call in_module instead?
        let fully_qualified = search_order.find_map(|m| {
            search_space.contains(&m).then_some(IdentifierPath {
                head: m.head.clone(),
                tail: {
                    let mut new_tail = m.tail.clone();
                    new_tail.push(id.head.clone());
                    new_tail.extend_from_slice(&id.tail);
                    new_tail
                },
            })
        })?;

        prefix_chain(&fully_qualified).find_map(|prefix| {
            self.module_members
                .contains_key(&prefix)
                .then_some(NameExpr {
                    module_prefix: prefix.clone(),
                    member: fully_qualified.element(prefix.len())?.to_owned(),
                    projections: fully_qualified.tail[prefix.len()..].to_vec(),
                })
        })
    }

    fn resolve_type_name(
        &self,
        id: &parser::IdentifierPath,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<QualifiedName> {
        let type_name = parser::Identifier::from_str(id.last());
        let member = ModuleMember::Type(type_name);
        let search_space = self
            .member_modules
            .get(&member)
            .ok_or_else(|| NameError::UnknownMember(member).at(pi))?;

        let mut search_order =
            prefix_chain(semantic_scope).chain(self.imports.iter().rev().cloned());

        search_order
            .find_map(|m| {
                let owner = if let Some(parent) = id.clone().try_into_parent() {
                    parent.in_module(&m)
                } else {
                    m.clone()
                };

                search_space.contains(&owner).then_some(id.in_module(&m))
            })
            .and_then(|id| id.try_into_qualified_name())
            .ok_or_else(|| NameError::UnknownName(id.clone()).at(pi))
    }

    pub fn add_term_symbol(
        &mut self,
        name: QualifiedName,
        symbol: TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>,
    ) {
        self.symbols
            .insert(SymbolName::Term(name), Symbol::Term(symbol));
    }

    pub fn add_type_symbol(
        &mut self,
        name: QualifiedName,
        symbol: TypeSymbol<parser::IdentifierPath>,
    ) {
        self.symbols
            .insert(SymbolName::Type(name), Symbol::Type(symbol));
    }

    pub fn add_module_term_member(
        &mut self,
        module_path: parser::IdentifierPath,
        member: parser::Identifier,
    ) {
        self.add_module_member(module_path, ModuleMember::Term(member));
    }

    pub fn add_module_type_member(
        &mut self,
        module_path: parser::IdentifierPath,
        member: parser::Identifier,
    ) {
        self.add_module_member(module_path, ModuleMember::Type(member));
    }

    pub fn add_module_member(&mut self, module_path: parser::IdentifierPath, member: ModuleMember) {
        self.module_members
            .entry(module_path.clone())
            .or_default()
            .push(member.clone());

        self.member_modules
            .entry(member)
            .or_default()
            .push(module_path);
    }

    pub fn add_type_declaration(
        &mut self,
        module_path: &parser::IdentifierPath,
        ast::TypeDeclaration {
            name,
            type_parameters,
            declarator,
        }: ast::TypeDeclaration<ParseInfo>,
    ) {
        {
            self.add_module_type_member(module_path.clone(), name.clone());

            let name = QualifiedName::new(module_path.clone(), name.as_str());
            match declarator {
                ast::TypeDeclarator::Record(_, record) => {
                    self.add_type_symbol(
                        name.clone(),
                        record.as_type_symbol(&type_parameters, &name),
                    );
                }

                ast::TypeDeclarator::Coproduct(pi, coproduct) => {
                    let constructors = coproduct
                        .constructors
                        .iter()
                        .map(|decl| ConstructorSymbol {
                            name: QualifiedName::new(module_path.clone(), decl.name.as_str()),
                            signature: decl.signature.clone(),
                        })
                        .collect::<Vec<_>>();

                    for constructor in &constructors {
                        self.add_module_term_member(
                            module_path.clone(),
                            parser::Identifier::from_str(constructor.name.member.as_str()),
                        );
                        self.add_term_symbol(
                            constructor.name.clone(),
                            constructor.as_constructor_term_symbol(pi, &type_parameters, &name),
                        );
                    }

                    self.add_type_symbol(
                        name.clone(),
                        coproduct.as_type_symbol(type_parameters, &name, constructors),
                    );
                }
            };
        }
    }

    pub fn add_value_declaration(
        &mut self,
        module_path: &parser::IdentifierPath,
        ast::ValueDeclaration { name, declarator }: ast::ValueDeclaration<ParseInfo>,
    ) {
        self.add_module_term_member(module_path.clone(), name.clone());
        let name = QualifiedName::new(module_path.clone(), name.as_str());
        self.add_term_symbol(
            name.clone(),
            TermSymbol {
                name,
                type_signature: declarator.type_signature.clone(),
                body: declarator.body.clone().into(),
            },
        );
    }

    pub fn add_module_declaration(
        &mut self,
        module_path: &parser::IdentifierPath,
        decl: ast::ModuleDeclaration<ParseInfo>,
        compiler: &Compiler,
    ) -> Compilation<()> {
        // Modules compete in the term namespace
        self.add_module_term_member(
            module_path.clone(),
            parser::Identifier::from_str(decl.name.as_str()),
        );

        let module_path = module_path.clone().with_suffix(decl.name.as_str());
        self.add_module_contents(
            compiler,
            module_path,
            Self::module_declarations(compiler, decl.declarator)?,
        )
    }

    fn add_module_contents(
        &mut self,
        compiler: &Compiler,
        module_path: IdentifierPath,
        declarations: Vec<Declaration<ParseInfo>>,
    ) -> Compilation<()> {
        for decl in declarations {
            match decl {
                Declaration::Value(_, decl) => self.add_value_declaration(&module_path, decl),

                Declaration::Module(_, decl) => {
                    self.add_module_declaration(&module_path, decl, compiler)?
                }

                Declaration::Type(_, decl) => self.add_type_declaration(&module_path, decl),

                Declaration::Use(_, decl) => {
                    self.add_use_declaration(compiler, &module_path, decl)?
                }

                Declaration::Constraint(_, decl) => {
                    self.add_constraint_declaration(&module_path, decl)
                }

                Declaration::Witness(_, decl) => {
                    println!("add_module_contents: witness {decl}");
                    self.add_witness_declaration(&module_path, decl)
                }
            };
        }

        Ok(())
    }

    fn add_witness_declaration(
        &mut self,
        module_path: &IdentifierPath,
        decl: ast::WitnessDeclaration<ParseInfo>,
    ) {
        let decl_name = fresh_name("witness_", &decl.type_signature.to_string());

        // These must be indexed by type signature
        let name = QualifiedName::new(module_path.clone(), &decl_name);
        self.add_module_term_member(
            module_path.clone(),
            parser::Identifier::from_str(&decl_name),
        );
        self.add_term_symbol(
            name.clone(),
            TermSymbol {
                name: name.clone(),
                type_signature: Some(decl.type_signature),
                body: Some(decl.implementation),
            },
        );
        self.witnesses.insert(name);
    }

    fn add_constraint_declaration(
        &mut self,
        module_path: &IdentifierPath,
        decl: ast::ConstraintDeclaration<ParseInfo>,
    ) {
        let name = QualifiedName::new(module_path.clone(), decl.name.as_str());
        self.add_module_type_member(module_path.clone(), decl.name);
        for field in &decl.declarator.fields {
            self.add_module_member(module_path.clone(), ModuleMember::Term(field.name.clone()));
        }
        self.add_type_symbol(
            name.clone(),
            decl.declarator.as_type_symbol(&decl.type_parameters, &name),
        );
        self.constraints.insert(name);
    }

    fn add_use_declaration(
        &mut self,
        compiler: &Compiler,
        module_path: &IdentifierPath,
        use_declaration: ast::UseDeclaration<ParseInfo>,
    ) -> Compilation<()> {
        if use_declaration.qualified_binder.is_some() {
            todo!()
        }
        let module = use_declaration.module;
        self.add_import_prefix(module_path.clone().with_suffix(module.name.as_str()));
        self.add_module_declaration(module_path, module, compiler)
    }

    pub fn add_import_prefix(&mut self, prefix: parser::IdentifierPath) {
        self.imports.push(prefix);
    }

    pub fn import_compilation_unit(program: CompilationUnit<ParseInfo>) -> Compilation<Self> {
        let mut ctx = Self::default();

        ctx.add_import_prefix(IdentifierPath::new(BUILTIN_MODULE_NAME));
        let stdlib = IdentifierPath::new(STDLIB_MODULE_NAME);
        ctx.add_import_prefix(stdlib.clone());

        for symbol in builtin::import() {
            match symbol {
                Symbol::Term(symbol) => {
                    let qualified_name = &symbol.name;
                    ctx.add_module_term_member(
                        qualified_name.module().clone(),
                        qualified_name.member.clone(),
                    );
                    ctx.add_term_symbol(qualified_name.clone(), symbol);
                }

                Symbol::Type(symbol) => {
                    let qualified_name = symbol.definition.qualified_name();
                    ctx.add_module_type_member(
                        qualified_name.module().clone(),
                        qualified_name.member.clone(),
                    );
                    ctx.add_type_symbol(qualified_name, symbol);
                }
            }
        }

        ctx.add_module_contents(
            &program.compiler,
            parser::IdentifierPath::new(program.root_module.name.as_str()),
            Self::module_declarations(&program.compiler, program.root_module.declarator)?,
        )?;

        Ok(ctx)
    }

    fn module_declarations(
        loader: &Compiler,
        module: ModuleDeclarator<ParseInfo>,
    ) -> Compilation<Vec<Declaration<ParseInfo>>> {
        match module {
            ModuleDeclarator::Inline(declarations) => Ok(declarations),
            ModuleDeclarator::External(module_name) => {
                Ok(loader.load_module_declarations(&module_name)?)
            }
        }
    }
}

fn fresh_name(prefix: &str, source: &str) -> String {
    let hasher = &mut DefaultHasher::default();
    source.hash(hasher);
    let hash = hasher.finish();
    format!("{prefix}{hash}")
}

fn prefix_chain(identifier_path: &IdentifierPath) -> impl Iterator<Item = IdentifierPath> {
    iter::successors(Some(identifier_path.clone()), |path| {
        if !path.tail.is_empty() {
            let mut path = path.clone();
            path.tail.pop();
            Some(path)
        } else {
            None
        }
    })
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

// Why doesn't this have a ParseInfo in it?
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

    pub fn qualified_name(&self) -> QualifiedName {
        match self {
            Self::Record(the) => the.name.clone(),
            Self::Coproduct(the) => the.name.clone(),
            Self::Builtin(the) => the.qualified_name(),
        }
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

    fn as_constructor_term_symbol(
        &self,
        pi: ParseInfo,
        type_parameters: &[parser::Identifier],
        type_constructor_name: &QualifiedName,
    ) -> TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath> {
        let type_signature = self.make_type_signature(pi, type_parameters, type_constructor_name);
        let body = self.make_curried_constructor_term(pi);
        TermSymbol {
            name: self.name.clone(),
            type_signature: type_signature.into(),
            body: body.into(),
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
            constraints: Vec::default(),
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
        let terms = 0..self.signature.len();
        let construct = parser::Expr::Inject(
            pi,
            ast::Injection {
                constructor: self.name.clone(),
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
struct DeBruijn {
    stack: Vec<parser::Identifier>,
    restore_points: Vec<usize>,
}

impl DeBruijn {
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
            Identifier::Free(QualifiedName::from_root_symbol(id.to_owned()).into())
        }
    }

    fn bind_and_then<F, A>(&mut self, id: parser::Identifier, mut block: F) -> A
    where
        F: FnMut(&mut DeBruijn, Identifier) -> A,
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

impl parser::ConstraintExpression {
    pub fn resolve_names(
        &self,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<ConstraintExpression> {
        let Self {
            annotation,
            class,
            parameters,
        } = self;

        Ok(ConstraintExpression {
            annotation: *annotation,
            class: symbols.resolve_type_name(class, pi, semantic_scope)?,
            parameters: parameters
                .iter()
                .map(|te| te.resolve_names(symbols, pi, semantic_scope))
                .collect::<Naming<_>>()?,
        })
    }
}

impl parser::TypeExpression {
    pub fn resolve_names(
        &self,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<TypeExpression> {
        match self {
            Self::Constructor(a, name) => Ok(TypeExpression::Constructor(*a, {
                symbols.resolve_type_name(name, pi, semantic_scope)?
            })),

            Self::Parameter(a, name) => Ok(TypeExpression::Parameter(*a, name.clone())),

            Self::Apply(a, apply) => Ok(TypeExpression::Apply(
                *a,
                ApplyTypeExpr {
                    function: apply
                        .function
                        .resolve_names(symbols, pi, semantic_scope)?
                        .into(),
                    argument: apply
                        .argument
                        .resolve_names(symbols, pi, semantic_scope)?
                        .into(),
                    phase: PhantomData,
                },
            )),

            Self::Arrow(a, arrow) => Ok(TypeExpression::Arrow(
                *a,
                ArrowTypeExpr {
                    domain: arrow
                        .domain
                        .resolve_names(symbols, pi, semantic_scope)?
                        .into(),
                    codomain: arrow
                        .codomain
                        .resolve_names(symbols, pi, semantic_scope)?
                        .into(),
                },
            )),

            Self::Tuple(a, tuple) => Ok(TypeExpression::Tuple(
                *a,
                TupleTypeExpr(
                    tuple
                        .0
                        .iter()
                        .map(|te| te.resolve_names(symbols, pi, semantic_scope))
                        .collect::<Naming<_>>()?,
                ),
            )),
        }
    }
}

impl parser::Expr {
    pub fn lower_tuples(self) -> parser::Expr {
        self.map(&mut |e| match e {
            parser::Expr::Tuple(a, tuple) => parser::Expr::Tuple(
                a,
                parser::Tuple {
                    elements: unspine_tuple(tuple.elements),
                },
            ),
            otherwise => otherwise,
        })
    }

    pub fn resolve_names(
        &self,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Expr> {
        self.resolve(&mut DeBruijn::default(), symbols, semantic_scope)
    }

    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Expr> {
        match self {
            Self::Variable(pi, identifier_path) => {
                // head is locally bound and tail projects off of it
                if let Some(bound) =
                    names.try_resolve_bound(&parser::Identifier::from_str(&identifier_path.head))
                {
                    Ok(project_base(pi, bound, &identifier_path.tail))

                // identier_path is a free term
                // Module1.ModuleN.term.projection1.projectionN
                } else if let Some(path) =
                    symbols.resolve_free_term_name(identifier_path, semantic_scope)
                {
                    Ok(path.into_projection(*pi))
                } else {
                    Err(NameError::UnknownName(identifier_path.clone()).at(*pi))
                }
            }

            Self::InvokeBridge(pi, bridge) => Ok(Expr::InvokeBridge(*pi, bridge.clone())),

            Self::Constant(pi, literal) => Ok(Expr::Constant(*pi, literal.clone())),

            Self::RecursiveLambda(pi, node) => Ok(Expr::RecursiveLambda(
                *pi,
                node.resolve(names, symbols, *pi, semantic_scope)?,
            )),

            Self::Lambda(pi, node) => Ok(Expr::Lambda(
                *pi,
                node.resolve(names, symbols, *pi, semantic_scope)?,
            )),

            Self::Apply(pi, node) => Ok(Expr::Apply(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Let(pi, node) => Ok(Expr::Let(
                *pi,
                node.resolve(names, symbols, *pi, semantic_scope)?,
            )),

            Self::Record(pi, node) => Ok(Expr::Record(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Tuple(pi, node) => Ok(Expr::Tuple(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Inject(pi, node) => Ok(Expr::Inject(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Project(pi, node) => Ok(Expr::Project(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Sequence(pi, node) => Ok(Expr::Sequence(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Deconstruct(pi, node) => Ok(Expr::Deconstruct(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::If(pi, node) => Ok(Expr::If(*pi, node.resolve(names, symbols, semantic_scope)?)),

            Self::Interpolate(pi, node) => Ok(Expr::Interpolate(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::Ascription(pi, node) => Ok(Expr::Ascription(
                *pi,
                node.resolve(names, symbols, semantic_scope)?,
            )),

            Self::MakeClosure(pi, node) => Ok(Expr::MakeClosure(*pi, node.clone())),
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

fn project_base(pi: &ParseInfo, base: Identifier, projection_path: &[String]) -> Expr {
    projection_path
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
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<SelfReferential> {
        if let Some(own_name) = self.own_name.try_as_simple() {
            names.bind_and_then(own_name.clone(), |names, own_name| {
                Ok(SelfReferential {
                    own_name,
                    lambda: self.lambda.resolve(names, symbols, pi, semantic_scope)?,
                })
            })
        } else {
            Err(NameError::BadOwnName(self.own_name.clone()).at(pi))
        }
    }
}

impl parser::Lambda {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Lambda> {
        if let Some(parameter) = self.parameter.try_as_simple() {
            names.bind_and_then(parameter, |names, parameter| {
                Ok(Lambda {
                    parameter,
                    body: self.body.resolve(names, symbols, semantic_scope)?.into(),
                })
            })
        } else {
            Err(NameError::BadParameterName(self.parameter.clone()).at(pi))
        }
    }
}

impl parser::Apply {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Apply> {
        Ok(Apply {
            function: self
                .function
                .resolve(names, symbols, semantic_scope)?
                .into(),
            argument: self
                .argument
                .resolve(names, symbols, semantic_scope)?
                .into(),
        })
    }
}

impl parser::Binding {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Binding> {
        if let Some(binder) = self.binder.try_as_simple() {
            let bound = Rc::new(self.bound.resolve(names, symbols, semantic_scope)?);
            names.bind_and_then(binder, |names, binder| {
                Ok(Binding {
                    binder,
                    bound: Rc::clone(&bound),
                    body: self.body.resolve(names, symbols, semantic_scope)?.into(),
                })
            })
        } else {
            Err(NameError::BadBinderName(self.binder.clone()).at(pi))
        }
    }
}

impl parser::Record {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Record> {
        Ok(Record {
            fields: self
                .fields
                .iter()
                .map(|(label, e)| {
                    e.resolve(names, symbols, semantic_scope)
                        .map(|e| (label.clone(), e.into()))
                })
                .collect::<Naming<_>>()?,
        })
    }
}

impl parser::Tuple {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Tuple> {
        Ok(Tuple {
            elements: self
                .elements
                .iter()
                .map(|e| e.resolve(names, symbols, semantic_scope).map(|e| e.into()))
                .collect::<Naming<_>>()?,
        })
    }
}

impl parser::Injection {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Injection> {
        Ok(Injection {
            constructor: self.constructor.clone(),
            arguments: self
                .arguments
                .iter()
                .map(|e| e.resolve(names, symbols, semantic_scope).map(|e| e.into()))
                .collect::<Naming<_>>()?,
        })
    }
}

impl parser::Projection {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Projection> {
        Ok(Projection {
            base: self
                .base
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            select: self.select.clone(),
        })
    }
}

impl parser::Sequence {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Sequence> {
        Ok(Sequence {
            this: self
                .this
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            and_then: self
                .and_then
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
        })
    }
}

impl parser::Deconstruct {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Deconstruct> {
        Ok(Deconstruct {
            scrutinee: self
                .scrutinee
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            match_clauses: self
                .match_clauses
                .iter()
                .map(|clause| clause.resolve(names, symbols, semantic_scope))
                .collect::<Naming<_>>()?,
        })
    }
}

impl parser::IfThenElse {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<IfThenElse> {
        Ok(IfThenElse {
            predicate: self
                .predicate
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            consequent: self
                .consequent
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            alternate: self
                .alternate
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
        })
    }
}

impl parser::Interpolate {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<Interpolate> {
        let Self(segments) = self;
        Ok(ast::Interpolate(
            segments
                .iter()
                .map(|s| match s {
                    ast::Segment::Literal(pi, literal) => {
                        Ok(ast::Segment::Literal(*pi, literal.clone()))
                    }

                    ast::Segment::Expression(expr) => expr
                        .resolve(names, symbols, semantic_scope)
                        .map(|e| ast::Segment::Expression(e.into())),
                })
                .collect::<Naming<_>>()?,
        ))
    }
}

impl parser::TypeAscription {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<TypeAscription> {
        let ast::TypeSignature {
            universal_quantifiers,
            constraints,
            body,
            phase,
        } = self.type_signature.clone().map_names(&|qn| qn.module);

        Ok(TypeAscription {
            ascribed_tree: self
                .ascribed_tree
                .resolve(names, symbols, semantic_scope)?
                .into(),

            type_signature: TypeSignature {
                universal_quantifiers,
                constraints: constraints
                    .into_iter()
                    .map(|e| e.resolve_names(symbols, ParseInfo::default(), semantic_scope))
                    .collect::<Naming<_>>()?,
                body: body.resolve_names(symbols, ParseInfo::default(), semantic_scope)?,
                phase,
            },
        })
    }
}

impl parser::MatchClause {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Naming<MatchClause> {
        let Self {
            pattern,
            consequent,
        } = self;
        names.mark();

        let clause = MatchClause {
            pattern: pattern.resolve(names, symbols, semantic_scope),
            consequent: consequent.resolve(names, symbols, semantic_scope)?.into(),
        };

        names.restore();
        Ok(clause)
    }
}

impl parser::Pattern {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &parser::IdentifierPath,
    ) -> Pattern {
        match self {
            parser::Pattern::Coproduct(a, pattern) => Pattern::Coproduct(
                *a,
                ConstructorPattern {
                    constructor: Identifier::Free(
                        symbols
                            .resolve_free_term_name(&pattern.constructor, semantic_scope)
                            .expect("msg")
                            .into_qualified_name()
                            .into(),
                    ),
                    arguments: pattern
                        .arguments
                        .iter()
                        .map(|arg| arg.resolve(names, symbols, semantic_scope))
                        .collect(),
                },
            ),

            parser::Pattern::Tuple(a, pattern) => Pattern::Tuple(
                *a,
                TuplePattern {
                    elements: pattern
                        .elements
                        .iter()
                        .map(|p| p.resolve(names, symbols, semantic_scope))
                        .collect(),
                },
            ),

            parser::Pattern::Struct(a, pattern) => Pattern::Struct(
                *a,
                StructPattern {
                    fields: pattern
                        .fields
                        .iter()
                        .map(|(field, pattern)| {
                            (
                                field.clone(),
                                pattern.resolve(names, symbols, semantic_scope),
                            )
                        })
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

impl ParserSymbolTable {
    pub fn lower_tuples(&mut self) {
        for symbol in self.symbols.values_mut() {
            if let Symbol::Term(symbol) = symbol {
                let body = symbol
                    .body
                    .take()
                    .expect("Internal Assertion - expected a symbol body.");
                symbol.body = body.lower_tuples().into();
            }
        }
    }

    // Move to namer.rs
    // This does not need the symbols in any particular order, so long as all
    // modules are known
    pub fn resolve_names(self) -> Naming<NamedSymbolTable> {
        Ok(SymbolTable {
            // Any kind of renaming necessary here?
            module_members: self.module_members.clone(),
            // Any kind of renaming necessary here?
            member_modules: self.member_modules.clone(),
            symbols: self
                .symbols
                .iter()
                .map(|(id, symbol)| {
                    // Bad with ParseInfo::default() but I guess I need location
                    // per Identifier really.
                    self.rename_symbol(ParseInfo::default(), symbol)
                        .map(|symbol| (id.clone(), symbol))
                })
                .collect::<Naming<_>>()?,
            imports: self.imports,
            // Any kind of renaming necessary here?
            constraints: self.constraints.clone(),
            // Any kind of renaming necessary here?
            witnesses: self.witnesses.clone(),
        })
    }

    fn rename_symbol(&self, pi: ParseInfo, symbol: &ParserSymbol) -> Naming<NamedSymbol> {
        match symbol {
            Symbol::Term(symbol) => Ok(Symbol::Term(if let Some(ts) = &symbol.type_signature {
                let type_signature = TypeSignature {
                    universal_quantifiers: ts.universal_quantifiers.clone(),
                    constraints: ts
                        .constraints
                        .iter()
                        .map(|ce| ce.resolve_names(self, pi, &symbol.name.module))
                        .collect::<Naming<_>>()?,
                    body: ts.body.resolve_names(self, pi, &symbol.name.module)?,
                    phase: PhantomData,
                };

                TermSymbol {
                    name: symbol.name.clone(),
                    type_signature: Some(type_signature.clone()),
                    body: Some(Expr::Ascription(
                        *symbol.body().parse_info(),
                        TypeAscription {
                            ascribed_tree: symbol
                                .body()
                                .resolve_names(self, &symbol.name.module)?
                                .into(),
                            type_signature,
                        },
                    )),
                }
            } else {
                TermSymbol {
                    name: symbol.name.clone(),
                    type_signature: None,
                    body: Some(symbol.body().resolve_names(self, &symbol.name.module)?),
                }
            })),

            Symbol::Type(symbol) => Ok(Symbol::Type({
                let semantic_scope = &symbol.definition.qualified_name().module;
                match &symbol.definition {
                    TypeDefinition::Record(record) => TypeSymbol {
                        definition: TypeDefinition::Record(RecordSymbol {
                            name: record.name.clone(),
                            type_parameters: record.type_parameters.clone(),
                            fields: record
                                .fields
                                .iter()
                                .map(|field| {
                                    field
                                        .type_signature
                                        .resolve_names(self, pi, semantic_scope)
                                        .map(|te| FieldSymbol {
                                            name: field.name.clone(),
                                            type_signature: te,
                                        })
                                })
                                .collect::<Naming<Vec<_>>>()?,
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
                                .map(|symbol| {
                                    symbol
                                        .signature
                                        .iter()
                                        .map(|ty| ty.resolve_names(self, pi, semantic_scope))
                                        .collect::<Naming<_>>()
                                        .map(|signature| ConstructorSymbol {
                                            name: symbol.name.clone(),
                                            signature,
                                        })
                                })
                                .collect::<Naming<_>>()?,
                        }),
                        origin: symbol.origin,
                        arity: symbol.arity,
                    },

                    TypeDefinition::Builtin(base_type) => TypeSymbol {
                        definition: TypeDefinition::Builtin(*base_type),
                        origin: symbol.origin,
                        arity: symbol.arity,
                    },
                }
            })),
        }
    }
}

impl fmt::Display for ModuleMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(identifier) => write!(f, "type {identifier}"),
            Self::Term(identifier) => write!(f, "term {identifier}"),
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
        write!(f, "{module}.{member}")
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
