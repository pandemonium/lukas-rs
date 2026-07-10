use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
    iter,
    marker::PhantomData,
    path::Path,
    rc::Rc,
};

use thiserror::Error;

use crate::{
    ast::{
        self, Apply, ApplyTypeExpr, ArrowTypeExpr, BUILTIN_MODULE_NAME, Binding, CompilationUnit,
        ConstraintExpression, CoproductDeclarator, Declaration, Deconstruct, IdentifierPattern,
        IfThenElse, Injection, Kind, Lambda, ModuleDeclarator, ProductElement, Projection,
        ROOT_MODULE_NAME, Record, RecordDeclarator, STDLIB_MODULE_NAME, SelfReferential, Sequence,
        Tuple, TupleTypeExpr, TypeAscription, TypeExpression, TypeSignature, TypeVariable,
        desugar::Desugared,
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    builtin,
    compiler::{Compilation, Compiler, Located, LocatedError},
    parser::{self, IdentifierPath, ParseInfo, Parsed},
    phase::{self, Phase},
    typer::{BaseType, display_list},
};

pub struct Named;

impl phase::Phase for Named {
    type Annotation = ParseInfo;
    type TermId = Identifier;
    type TypeId = QualifiedName;
}

pub type Expr = phase::Expr<Named>;

type ParserSymbolTable = SymbolTable<ParseInfo, IdentifierPath, IdentifierPath>;
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

impl TypeExpression<ParseInfo, QualifiedName> {
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
    module_prefix: IdentifierPath,
    member: String,
    projections: Vec<String>,
}

impl NameExpr {
    /// The `module_prefix` + `member` as a qualified name, ignoring any trailing
    /// projections.
    pub fn qualified_name(&self) -> QualifiedName {
        QualifiedName {
            module: self.module_prefix.clone(),
            member: parser::Identifier::from_str(&self.member),
        }
    }

    fn into_projection(self, pi: ParseInfo) -> Expr {
        let path = self.qualified_name();

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
        self.qualified_name()
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct QualifiedName {
    pub module: IdentifierPath,
    pub member: parser::Identifier,
}

impl QualifiedName {
    pub fn new(module: IdentifierPath, member: &str) -> QualifiedName {
        Self {
            module,
            member: parser::Identifier::from_str(member),
        }
    }

    pub fn builtin(member: &str) -> Self {
        Self {
            module: IdentifierPath::new(ast::BUILTIN_MODULE_NAME),
            member: parser::Identifier::from_str(member),
        }
    }

    pub fn from_root_symbol(member: parser::Identifier) -> Self {
        Self {
            module: IdentifierPath::new(ast::ROOT_MODULE_NAME),
            member,
        }
    }

    pub fn into_identifier_path(self) -> IdentifierPath {
        IdentifierPath {
            head: self.module.head,
            tail: {
                let mut tail = self.module.tail;
                tail.push(self.member.as_str().to_owned());
                tail
            },
        }
    }

    pub fn module(&self) -> &IdentifierPath {
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
    pub fn merge(&mut self, rhs: DependencyMatrix<Id>) {
        let Self { graph, witnesses } = rhs;
        for (k, v) in graph {
            self.add_edge(k, v);
        }
        self.witnesses.extend(witnesses);
    }

    pub fn map<F, B>(self, f: F) -> DependencyMatrix<B>
    where
        F: Fn(Id) -> B,
        B: Hash + Eq,
    {
        let Self { graph, witnesses } = self;
        DependencyMatrix {
            graph: graph
                .into_iter()
                .map(|(k, v)| (f(k), v.into_iter().map(&f).collect()))
                .collect(),
            witnesses: witnesses.into_iter().map(f).collect(),
        }
    }

    pub fn add_edge(&mut self, node: Id, vertices: Vec<Id>) {
        self.graph.entry(node).or_default().extend(vertices);
    }

    pub fn add_witness(&mut self, witness: Id) {
        self.witnesses.insert(witness);
    }

    /// Every `(symbol, dependency)` edge whose dependency has no defining node in
    /// the graph -- i.e. a name that is referenced but never defined.
    pub fn unsatisfied(&self) -> Vec<(&Id, &Id)> {
        self.graph
            .iter()
            .flat_map(|(node, deps)| {
                deps.iter()
                    .filter(|dep| !self.graph.contains_key(dep))
                    .map(move |dep| (node, dep))
            })
            .collect()
    }

    pub fn are_sound(&self) -> bool {
        self.unsatisfied().is_empty()
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
        // Deterministic order: the resolved sequence drives type-checking order and
        // hence fresh-variable allocation, so HashMap iteration order here must not
        // leak into the result.
        graph.sort_by_key(|(node, _)| node.to_string());

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

        // Seed the frontier in a deterministic order (HashMap iteration order is
        // not stable), so the whole initialization order is reproducible.
        let mut seeds = in_degrees
            .iter()
            .filter(|(_, in_degree)| **in_degree == 0)
            .map(|(&node, _)| node)
            .collect::<Vec<_>>();
        seeds.sort_by_key(|node| node.to_string());
        for node in seeds {
            if self.witnesses.contains(node) {
                witnesses.push_back(node);
            } else {
                non_witnesses.push_back(node);
            }
        }

        loop {
            let independent = if let Some(node) = witnesses.pop_front() {
                node
            } else if let Some(node) = non_witnesses.pop_front() {
                node
            } else {
                // Both frontiers are empty. Any nodes still left form a
                // dependency cycle -- e.g. a recursive dictionary and its lifted
                // method body reference each other. Those references resolve
                // lazily at runtime, so break the cycle by emitting a remaining
                // node rather than dropping it (and everything downstream, like
                // `start`). Prefer a non-witness with the fewest remaining
                // dependencies, so a witness record that eagerly holds a lifted
                // method body is emitted after that body.
                // Break ties deterministically (fewest deps, then name) so the
                // static-initialization order is reproducible -- HashMap iteration
                // order otherwise makes it flaky.
                let breaker = in_degrees
                    .iter()
                    .filter(|(node, _)| !self.witnesses.contains(**node))
                    .min_by_key(|(node, count)| (**count, node.to_string()))
                    .or_else(|| {
                        in_degrees
                            .iter()
                            .min_by_key(|(node, count)| (**count, node.to_string()))
                    })
                    .map(|(node, _)| *node);
                match breaker {
                    Some(node) => node,
                    None => break,
                }
            };

            resolved.push(independent);

            for (node, edges) in &mut graph {
                if edges.remove(independent)
                    && let Some(count) = in_degrees.get_mut(node)
                {
                    *count = count.saturating_sub(1);
                    if *count == 0 {
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

impl IdentifierPath {
    pub fn try_into_qualified_name(self) -> Option<QualifiedName> {
        let Self { head, mut tail } = self;

        let member = tail.pop();

        member.map(|member| QualifiedName {
            module: IdentifierPath { head, tail },
            member: parser::Identifier::from_str(&member),
        })
    }
}

impl RecordDeclarator<ParseInfo> {
    fn as_record_symbol(
        &self,
        type_parameters: &[TypeVariable],
        name: &QualifiedName,
    ) -> RecordSymbol<IdentifierPath> {
        RecordSymbol {
            name: name.clone(),
            type_parameters: type_parameters.to_vec(),
            fields: self
                .fields
                .iter()
                .map(|decl| FieldSymbol {
                    name: decl.name.clone(),
                    type_signature: decl.type_signature.clone(),
                })
                .collect(),
        }
    }

    fn as_type_symbol(
        &self,
        type_parameters: &[TypeVariable],
        name: &QualifiedName,
        origin: TypeOrigin,
        opacity: Opacity,
    ) -> TypeSymbol<IdentifierPath> {
        TypeSymbol {
            definition: TypeDefinition::Record(self.as_record_symbol(type_parameters, name)),
            origin,
            opacity,
            arity: type_parameters.len(),
            kind: compute_type_constructor_kind(type_parameters),
        }
    }
}

fn compute_type_constructor_kind(type_parameters: &[TypeVariable]) -> Kind {
    type_parameters.iter().rfold(Kind::Star, |z, tv| {
        Kind::Arrow(tv.kind.clone().into(), z.into())
    })
}

impl CoproductDeclarator<ParseInfo> {
    fn as_type_symbol(
        &self,
        type_parameters: &[TypeVariable],
        name: &QualifiedName,
        constructors: Vec<ConstructorSymbol<IdentifierPath>>,
        origin: TypeOrigin,
        opacity: Opacity,
    ) -> TypeSymbol<IdentifierPath> {
        TypeSymbol {
            definition: TypeDefinition::Coproduct(CoproductSymbol {
                name: name.clone(),
                type_parameters: type_parameters.to_vec(),
                constructors,
            }),
            origin,
            opacity,
            arity: type_parameters.len(),
            kind: compute_type_constructor_kind(type_parameters),
        }
    }
}

// Rename to Symbols? SymbolContext?
#[derive(Debug, Clone)]
pub struct SymbolTable<A, GlobalName, LocalId> {
    pub module_members: HashMap<IdentifierPath, Vec<ModuleMember>>,
    pub member_modules: HashMap<ModuleMember, Vec<IdentifierPath>>,

    // Why only one table?
    pub symbols: HashMap<SymbolName, Symbol<A, GlobalName, LocalId>>,
    pub imports: Vec<IdentifierPath>,

    pub foreign_terms: Vec<ForeignTerm<GlobalName>>,

    pub signatures: HashSet<QualifiedName>,
    pub witnesses: HashSet<QualifiedName>,

    pub constructor_opacity: HashMap<QualifiedName, Opacity>,
}

impl<A, TypeId, ValueId> Default for SymbolTable<A, TypeId, ValueId> {
    fn default() -> Self {
        Self {
            module_members: HashMap::default(),
            member_modules: HashMap::default(),
            symbols: HashMap::default(),
            imports: Vec::default(),
            foreign_terms: Vec::default(),
            signatures: HashSet::default(),
            witnesses: HashSet::default(),
            constructor_opacity: HashMap::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ForeignTerm<GlobalName> {
    pub name: QualifiedName,
    //This ought not be of A, but of ParseInfo because wtf does it buy?
    pub type_signature: TypeSignature<ParseInfo, GlobalName>,
}

impl phase::SymbolTable<Desugared> {
    fn resolve_free_term_name(
        &self,
        id: &IdentifierPath,
        semantic_scope: &IdentifierPath,
    ) -> Option<NameExpr> {
        let search_space = self
            .member_modules
            .get(&ModuleMember::Term(parser::Identifier::from_str(&id.head)))?;

        let parents = prefix_chain(semantic_scope);

        let search_order = parents.chain(self.imports.iter().rev().cloned());

        let resolved = search_order
            .filter(|m| search_space.contains(m))
            .find_map(|m| {
                let fully_qualified = IdentifierPath {
                    head: m.head.clone(),
                    tail: {
                        let mut new_tail = m.tail.clone();
                        new_tail.push(id.head.clone());
                        new_tail.extend_from_slice(&id.tail);
                        new_tail
                    },
                };

                let name_expr = prefix_chain(&fully_qualified).find_map(|prefix| {
                    self.module_members
                        .contains_key(&prefix)
                        .then_some(NameExpr {
                            module_prefix: prefix.clone(),
                            member: fully_qualified.element(prefix.len())?.to_owned(),
                            projections: fully_qualified.tail[prefix.len()..].to_vec(),
                        })
                })?;

                let names_a_real_member = self
                    .member_modules
                    .get(&ModuleMember::Term(parser::Identifier::from_str(
                        name_expr.member.as_str(),
                    )))
                    .is_some_and(|modules| modules.contains(&name_expr.module_prefix));

                (!name_expr.projections.is_empty() || names_a_real_member).then_some(name_expr)
            })?;

        let hidden = resolved.projections.is_empty()
            && self
                .constructor_opacity
                .get(&resolved.qualified_name())
                .is_some_and(|opacity| !opacity.is_visible_from(semantic_scope));

        (!hidden).then_some(resolved)
    }

    fn resolve_type_name(
        &self,
        id: &IdentifierPath,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
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
}

impl phase::SymbolTable<Parsed> {
    pub fn add_term_symbol(
        &mut self,
        name: QualifiedName,
        symbol: TermSymbol<ParseInfo, IdentifierPath, <Parsed as Phase>::TermId>,
    ) {
        self.symbols
            .insert(SymbolName::Term(name), Symbol::Term(symbol));
    }

    pub fn add_type_symbol(&mut self, name: QualifiedName, symbol: TypeSymbol<IdentifierPath>) {
        self.symbols
            .insert(SymbolName::Type(name), Symbol::Type(symbol));
    }

    pub fn add_module_term_member(
        &mut self,
        module_path: IdentifierPath,
        member: parser::Identifier,
    ) {
        self.add_module_member(module_path, ModuleMember::Term(member));
    }

    pub fn add_module_type_member(
        &mut self,
        module_path: IdentifierPath,
        member: parser::Identifier,
    ) {
        self.add_module_member(module_path, ModuleMember::Type(member));
    }

    pub fn add_module_member(&mut self, module_path: IdentifierPath, member: ModuleMember) {
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
        module_path: &IdentifierPath,
        ast::TypeDeclaration {
            name,
            type_parameters,
            declarator,
            origin,
            opaque,
        }: ast::TypeDeclaration<ParseInfo>,
    ) {
        {
            self.add_module_type_member(module_path.clone(), name.clone());

            let name = QualifiedName::new(module_path.clone(), name.as_str());

            let opacity = if opaque || matches!(origin, TypeOrigin::Foreign) {
                Opacity::TransparentWithin(module_path.clone())
            } else {
                Opacity::Transparent
            };

            match declarator {
                ast::TypeDeclarator::Record(_, record) => {
                    self.add_type_symbol(
                        name.clone(),
                        record.as_type_symbol(&type_parameters, &name, origin, opacity),
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
                        // Project the owning type's opacity onto each constructor so
                        // `resolve_free_term_name` can enforce it by constructor name.
                        // Only restricted constructors are indexed; transparent ones
                        // are always visible and need no entry.
                        if !matches!(opacity, Opacity::Transparent) {
                            self.constructor_opacity
                                .insert(constructor.name.clone(), opacity.clone());
                        }
                    }

                    self.add_type_symbol(
                        name.clone(),
                        coproduct.as_type_symbol(
                            &type_parameters,
                            &name,
                            constructors,
                            origin,
                            opacity,
                        ),
                    );
                }
            };
        }
    }

    pub fn add_value_declaration(
        &mut self,
        module_path: &IdentifierPath,
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
        module_path: &IdentifierPath,
        dir: &Path,
        decl: ast::ModuleDeclaration<ParseInfo>,
        compiler: &Compiler,
        loaded: &mut HashSet<IdentifierPath>,
    ) -> Compilation<()> {
        let name = parser::Identifier::from_str(decl.name.as_str());
        self.add_module_term_member(module_path.clone(), name);

        let canonical = module_path.clone().with_suffix(decl.name.as_str());

        if loaded.insert(canonical.clone()) {
            let (declarations, child_dir) = match decl.declarator {
                ModuleDeclarator::Inline(declarations) => {
                    (declarations, dir.join(decl.name.as_str()))
                }
                ModuleDeclarator::External(_) => {
                    compiler.load_nested_module(dir, decl.name.as_str())?
                }
            };
            self.add_module_contents(compiler, canonical, &child_dir, declarations, loaded)
        } else {
            Ok(())
        }
    }

    fn add_module_contents(
        &mut self,
        compiler: &Compiler,
        module_path: IdentifierPath,
        dir: &Path,
        declarations: Vec<Declaration<ParseInfo>>,
        loaded: &mut HashSet<IdentifierPath>,
    ) -> Compilation<()> {
        for decl in declarations {
            match decl {
                Declaration::Value(_, decl) => self.add_value_declaration(&module_path, decl),

                Declaration::Module(_, decl) => {
                    self.add_module_declaration(&module_path, dir, decl, compiler, loaded)?
                }

                Declaration::Type(_, decl) => self.add_type_declaration(&module_path, decl),

                Declaration::Use(pi, decl) => {
                    self.add_use_declaration(compiler, &module_path, pi, decl, loaded)?
                }

                Declaration::Signature(_, decl) => {
                    self.add_signature_declaration(&module_path, decl)
                }

                Declaration::Witness(_, decl) => self.add_witness_declaration(&module_path, decl),

                Declaration::Foreign(_, decl) => {
                    self.add_module_term_member(module_path.clone(), decl.name.clone());
                    self.add_foreign_declaration(&module_path, decl);
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
                body: decl.implementation,
            },
        );
        self.witnesses.insert(name);
    }

    fn add_foreign_declaration(
        &mut self,
        module_path: &IdentifierPath,
        decl: ast::ForeignDeclaration<ParseInfo>,
    ) {
        self.foreign_terms.push(ForeignTerm {
            name: QualifiedName::new(module_path.clone(), decl.name.as_str()),
            type_signature: decl.type_signature,
        });
    }

    fn add_signature_declaration(
        &mut self,
        module_path: &IdentifierPath,
        decl: ast::SignatureDeclaration<ParseInfo>,
    ) {
        let name = QualifiedName::new(module_path.clone(), decl.name.as_str());
        self.add_module_type_member(module_path.clone(), decl.name);
        for field in &decl.declarator.fields {
            self.add_module_member(module_path.clone(), ModuleMember::Term(field.name.clone()));
        }
        self.add_type_symbol(
            name.clone(),
            TypeSymbol {
                definition: TypeDefinition::Signature(SignatureSymbol {
                    vtable: decl
                        .declarator
                        .as_record_symbol(&decl.type_parameters, &name),
                    supersignatures: decl.constraints,
                }),
                origin: TypeOrigin::UserDefined,
                opacity: Opacity::Transparent,
                arity: decl.type_parameters.len(),
                kind: compute_type_constructor_kind(&decl.type_parameters),
            },
        );
        self.signatures.insert(name);
    }

    fn add_use_declaration(
        &mut self,
        compiler: &Compiler,
        module_path: &IdentifierPath,
        pi: ParseInfo,
        use_declaration: ast::UseDeclaration<ParseInfo>,
        loaded: &mut HashSet<IdentifierPath>,
    ) -> Compilation<()> {
        if use_declaration.qualified_binder.is_some() {
            todo!()
        }
        let path = use_declaration.path;

        if path.tail.is_empty() {
            let name = parser::Identifier::from_str(&path.head);
            let root = IdentifierPath::new(ROOT_MODULE_NAME);
            self.add_module_term_member(root.clone(), name.clone());
            let canonical = root.with_suffix(&path.head);
            self.add_import_prefix(canonical.clone());

            if loaded.insert(canonical.clone()) {
                let (declarations, child_dir) = compiler.load_top_level_module(&path.head)?;
                self.add_module_contents(compiler, canonical, &child_dir, declarations, loaded)?;
            }
            Ok(())
        } else {
            let canonical = self.resolve_module_path(&path, module_path, pi)?;
            self.add_import_prefix(canonical);
            Ok(())
        }
    }

    fn resolve_module_path(
        &self,
        path: &IdentifierPath,
        scope: &IdentifierPath,
        pi: ParseInfo,
    ) -> Compilation<IdentifierPath> {
        prefix_chain(scope)
            .chain(self.imports.iter().rev().cloned())
            .find_map(|base| {
                let candidate = IdentifierPath {
                    head: base.head.clone(),
                    tail: {
                        let mut tail = base.tail.clone();
                        tail.push(path.head.clone());
                        tail.extend(path.tail.iter().cloned());
                        tail
                    },
                };
                self.module_members
                    .contains_key(&candidate)
                    .then_some(candidate)
            })
            .ok_or_else(|| NameError::UnknownName(path.clone()).at(pi).into())
    }

    pub fn add_import_prefix(&mut self, prefix: IdentifierPath) {
        self.imports.push(prefix);
    }

    pub fn import_compilation_unit(program: CompilationUnit<ParseInfo>) -> Compilation<Self> {
        let mut symtab = Self::default();

        symtab.add_import_prefix(IdentifierPath::new(BUILTIN_MODULE_NAME));

        // this is probably not stdlib--but what is it?
        let stdlib = IdentifierPath::new(STDLIB_MODULE_NAME);
        symtab.add_import_prefix(stdlib.clone());

        for symbol in builtin::import() {
            match symbol {
                Symbol::Term(symbol) => {
                    let qualified_name = &symbol.name;
                    symtab.add_module_term_member(
                        qualified_name.module().clone(),
                        qualified_name.member.clone(),
                    );
                    symtab.add_term_symbol(qualified_name.clone(), symbol);
                }

                Symbol::Type(symbol) => {
                    let qualified_name = symbol.definition.qualified_name();
                    symtab.add_module_type_member(
                        qualified_name.module().clone(),
                        qualified_name.member.clone(),
                    );
                    symtab.add_type_symbol(qualified_name, symbol);
                }
            }
        }

        let mut loaded = HashSet::from([IdentifierPath::new(program.root_module.name.as_str())]);
        let root_dir = program.compiler.source_path.clone();
        symtab.add_module_contents(
            &program.compiler,
            IdentifierPath::new(program.root_module.name.as_str()),
            &root_dir,
            Self::module_declarations(&program.compiler, program.root_module.declarator)?,
            &mut loaded,
        )?;

        Ok(symtab)
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

// TODO: Is this fine? Why would I do it this way?
pub fn fresh_name(prefix: &str, source: &str) -> String {
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
                        .body
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
    pub opacity: Opacity,
    pub arity: usize,
    pub kind: Kind,
}

#[derive(Debug, Copy, Clone)]
pub enum TypeOrigin {
    UserDefined,
    Builtin,
    Foreign,
}

#[derive(Debug, Clone)]
pub enum Opacity {
    Transparent,
    TransparentWithin(IdentifierPath),
}

impl Opacity {
    pub fn is_visible_from(&self, semantic_scope: &IdentifierPath) -> bool {
        match self {
            Self::Transparent => true,
            Self::TransparentWithin(module) => prefix_chain(semantic_scope).any(|m| &m == module),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeDefinition<GlobalName> {
    Record(RecordSymbol<GlobalName>),
    Signature(SignatureSymbol<GlobalName>),
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
            Self::Signature(the) => the.vtable.name.clone(),
            Self::Coproduct(the) => the.name.clone(),
            Self::Builtin(the) => the.qualified_name(),
        }
    }
}

impl TypeSymbol<QualifiedName> {
    pub fn qualified_name(&self) -> QualifiedName {
        match &self.definition {
            TypeDefinition::Record(symbol) => symbol.name.clone(),
            TypeDefinition::Signature(symbol) => symbol.vtable.name.clone(),
            TypeDefinition::Coproduct(symbol) => symbol.name.clone(),
            TypeDefinition::Builtin(base_type) => base_type.qualified_name(),
        }
    }

    pub fn type_parameters(&self) -> &[TypeVariable] {
        match &self.definition {
            TypeDefinition::Record(sym) => &sym.type_parameters,
            TypeDefinition::Signature(sym) => &sym.vtable.type_parameters,
            TypeDefinition::Coproduct(sym) => &sym.type_parameters,
            TypeDefinition::Builtin(..) => &[],
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordSymbol<GlobalName> {
    pub name: QualifiedName,
    pub type_parameters: Vec<TypeVariable>,
    pub fields: Vec<FieldSymbol<GlobalName>>,
}

/// A `signature` (type class): the method-dictionary record (`vtable`) plus the
/// supersignatures it requires. See notes/supersignatures.md.
#[derive(Debug, Clone)]
pub struct SignatureSymbol<GlobalName> {
    pub vtable: RecordSymbol<GlobalName>,
    pub supersignatures: Vec<ast::ConstraintExpression<ParseInfo, GlobalName>>,
}

#[derive(Debug, Clone)]
pub struct FieldSymbol<GlobalName> {
    pub name: parser::Identifier,
    pub type_signature: ast::TypeSignature<ParseInfo, GlobalName>,
}

#[derive(Debug, Clone)]
pub struct CoproductSymbol<GlobalName> {
    pub name: QualifiedName,
    pub type_parameters: Vec<TypeVariable>,
    pub constructors: Vec<ConstructorSymbol<GlobalName>>,
}

#[derive(Debug, Clone)]
pub struct ConstructorSymbol<GlobalName> {
    pub name: QualifiedName,
    pub signature: Vec<ast::TypeExpression<ParseInfo, GlobalName>>,
}

impl ConstructorSymbol<IdentifierPath> {
    fn make_applied_type_constructor(
        &self,
        pi: ParseInfo,
        type_parameters: &[TypeVariable],
        type_constructor_name: &QualifiedName,
    ) -> phase::TypeExpression<Parsed> {
        type_parameters.iter().cloned().fold(
            TypeExpression::Constructor(pi, type_constructor_name.clone().into_identifier_path()),
            |function, argument| {
                TypeExpression::Apply(
                    pi,
                    ApplyTypeExpr {
                        function: function.into(),
                        argument: TypeExpression::Parameter(pi, argument.name).into(),
                        phase: PhantomData,
                    },
                )
            },
        )
    }

    fn as_constructor_term_symbol(
        &self,
        pi: ParseInfo,
        type_parameters: &[TypeVariable],
        type_constructor_name: &QualifiedName,
    ) -> TermSymbol<ParseInfo, IdentifierPath, <Parsed as Phase>::TermId> {
        let type_signature = self.make_type_signature(pi, type_parameters, type_constructor_name);
        let body = self.make_curried_constructor_term(pi);
        TermSymbol {
            name: self.name.clone(),
            type_signature: type_signature.into(),
            body: body,
        }
    }

    fn make_type_signature(
        &self,
        pi: ParseInfo,
        type_parameters: &[TypeVariable],
        type_constructor_name: &QualifiedName,
    ) -> phase::TypeSignature<Parsed> {
        TypeSignature {
            universal_quantifiers: type_parameters.to_vec(),
            constraints: Vec::default(),
            body: self.signature.iter().cloned().rfold(
                self.make_applied_type_constructor(pi, type_parameters, type_constructor_name),
                |rhs, lhs| {
                    TypeExpression::Arrow(
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

    // These things are also phase like. What are they?
    pub fn make_curried_constructor_term(&self, pi: ParseInfo) -> phase::Expr<Parsed> {
        let terms = 0..self.signature.len();
        let construct = ast::Expr::Inject(
            pi,
            ast::Injection {
                constructor: self.name.clone(),
                arguments: terms
                    .clone()
                    .map(|i| {
                        ast::Expr::Variable(pi, IdentifierPattern::from_atom(pi, &format!("p{i}")))
                            .into()
                    })
                    .collect(),
            },
        );

        terms.rfold(construct, |z, i| {
            ast::Expr::Lambda(
                pi,
                Lambda {
                    parameter: IdentifierPattern::from_atom(pi, &format!("p{i}")),
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
    pub body: ast::Expr<A, LocalId>,
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

impl phase::ConstraintExpression<Desugared> {
    pub fn resolve_names(
        &self,
        symbols: &phase::SymbolTable<Desugared>,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<ConstraintExpression<ParseInfo, QualifiedName>> {
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

impl phase::TypeSignature<Desugared> {
    pub fn resolve_names(
        &self,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<TypeSignature<ParseInfo, QualifiedName>> {
        let Self {
            universal_quantifiers,
            constraints,
            body,
            ..
        } = self;
        Ok(TypeSignature {
            universal_quantifiers: universal_quantifiers.clone(),
            constraints: constraints
                .iter()
                .map(|ce| ce.resolve_names(symbols, pi, &semantic_scope))
                .collect::<Naming<_>>()?,
            body: body.resolve_names(symbols, pi, &semantic_scope)?,
            phase: PhantomData,
        })
    }
}

impl phase::TypeExpression<Desugared> {
    pub fn resolve_names(
        &self,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<TypeExpression<ParseInfo, QualifiedName>> {
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

impl phase::Expr<Desugared> {
    pub fn resolve_names(
        &self,
        symbols: &phase::SymbolTable<Desugared>,
        semantic_scope: &IdentifierPath,
    ) -> Naming<Expr> {
        self.resolve(&mut DeBruijn::default(), symbols, semantic_scope)
    }

    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &phase::SymbolTable<Desugared>,
        semantic_scope: &IdentifierPath,
    ) -> Naming<Expr> {
        match self {
            Self::Variable(pi, name) => resolve_name(*pi, names, symbols, semantic_scope, name),

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

fn resolve_name(
    pi: ParseInfo,
    names: &mut DeBruijn,
    symbols: &phase::SymbolTable<Desugared>,
    semantic_scope: &IdentifierPath,
    identifier_path: &IdentifierPath,
) -> Naming<Expr> {
    // head is locally bound and tail projects off of it
    if let Some(bound) =
        names.try_resolve_bound(&parser::Identifier::from_str(&identifier_path.head))
    {
        Ok(project_base(pi, bound, &identifier_path.tail))

    // identier_path is a free term
    // Module1.ModuleN.term.projection1.projectionN
    } else if let Some(path) = symbols.resolve_free_term_name(identifier_path, semantic_scope) {
        Ok(path.into_projection(pi))
    } else {
        Err(NameError::UnknownName(identifier_path.clone()).at(pi))
    }
}

fn project_base(pi: ParseInfo, base: Identifier, projection_path: &[String]) -> Expr {
    projection_path
        .iter()
        .fold(Expr::Variable(pi, base), |base, member| {
            Expr::Project(
                pi,
                Projection {
                    base: base.into(),
                    select: ProductElement::Name(parser::Identifier::from_str(member)),
                },
            )
        })
}

impl phase::SelfReferential<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::SelfReferential<Named>> {
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

impl phase::Lambda<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Lambda<Named>> {
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

impl phase::Apply<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Apply<Named>> {
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

impl phase::Binding<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        pi: ParseInfo,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Binding<Named>> {
        if let Some(binder) = self.binder.try_as_simple() {
            let bound = Rc::new(self.bound.resolve(names, symbols, semantic_scope)?);
            names.bind_and_then(binder, |names, binder| {
                Ok(Binding {
                    binder,
                    operator: self.operator,
                    bound: Rc::clone(&bound),
                    body: self.body.resolve(names, symbols, semantic_scope)?.into(),
                })
            })
        } else {
            Err(NameError::BadBinderName(self.binder.clone()).at(pi))
        }
    }
}

impl phase::Record<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Record<Named>> {
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

impl phase::Tuple<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Tuple<Named>> {
        Ok(Tuple {
            elements: self
                .elements
                .iter()
                .map(|e| e.resolve(names, symbols, semantic_scope).map(|e| e.into()))
                .collect::<Naming<_>>()?,
        })
    }
}

impl phase::Injection<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Injection<Named>> {
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

impl phase::Projection<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Projection<Named>> {
        Ok(Projection {
            base: self
                .base
                .resolve(names, symbols, semantic_scope)
                .map(|e| e.into())?,
            select: self.select.clone(),
        })
    }
}

impl phase::Sequence<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Sequence<Named>> {
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

impl phase::Deconstruct<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Deconstruct<Named>> {
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

impl phase::IfThenElse<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::IfThenElse<Named>> {
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

impl phase::Interpolate<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::Interpolate<Named>> {
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

impl phase::TypeAscription<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::TypeAscription<Named>> {
        let TypeSignature {
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

impl phase::MatchClause<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> Naming<phase::MatchClause<Named>> {
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

impl phase::Pattern<Desugared> {
    fn resolve(
        &self,
        names: &mut DeBruijn,
        symbols: &ParserSymbolTable,
        semantic_scope: &IdentifierPath,
    ) -> phase::Pattern<Named> {
        match self {
            Pattern::Coproduct(a, pattern) => Pattern::Coproduct(
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

            Pattern::Tuple(a, pattern) => Pattern::Tuple(
                *a,
                TuplePattern {
                    elements: pattern
                        .elements
                        .iter()
                        .map(|p| p.resolve(names, symbols, semantic_scope))
                        .collect(),
                },
            ),

            Pattern::Struct(a, pattern) => Pattern::Struct(
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

            Pattern::Literally(a, pattern) => Pattern::Literally(*a, pattern.clone()),

            Pattern::Bind(a, pattern) => {
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

impl phase::SymbolTable<Desugared> {
    // Move to namer.rs
    // This does not need the symbols in any particular order, so long as all
    // modules are known
    pub fn resolve_names(self) -> Naming<phase::SymbolTable<Named>> {
        Ok(SymbolTable {
            module_members: self.module_members.clone(),
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
            foreign_terms: self
                .foreign_terms
                .iter()
                .map(|e| {
                    e.type_signature
                        .resolve_names(&self, ParseInfo::default(), &e.name.module)
                        .map(|type_signature| ForeignTerm {
                            name: e.name.clone(),
                            type_signature,
                        })
                })
                .collect::<Naming<_>>()?,
            imports: self.imports,
            signatures: self.signatures.clone(),
            witnesses: self.witnesses.clone(),
            constructor_opacity: self.constructor_opacity.clone(),
        })
    }

    fn rename_symbol(
        &self,
        pi: ParseInfo,
        symbol: &phase::Symbol<Desugared>,
    ) -> Naming<phase::Symbol<Named>> {
        match symbol {
            Symbol::Term(symbol) => Ok(Symbol::Term(if let Some(ts) = &symbol.type_signature {
                let type_signature = ts.resolve_names(self, pi, &symbol.name.module)?;

                TermSymbol {
                    name: symbol.name.clone(),
                    type_signature: Some(type_signature.clone()),
                    body: Expr::Ascription(
                        *symbol.body.parse_info(),
                        TypeAscription {
                            ascribed_tree: symbol
                                .body
                                .resolve_names(self, &symbol.name.module)?
                                .into(),
                            type_signature,
                        },
                    ),
                }
            } else {
                TermSymbol {
                    name: symbol.name.clone(),
                    type_signature: None,
                    body: symbol.body.resolve_names(self, &symbol.name.module)?,
                }
            })),

            Symbol::Type(symbol) => Ok(Symbol::Type({
                let semantic_scope = &symbol.definition.qualified_name().module;

                let resolve_record =
                    |record: &RecordSymbol<IdentifierPath>| -> Naming<RecordSymbol<QualifiedName>> {
                        Ok(RecordSymbol {
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
                        })
                    };

                match &symbol.definition {
                    TypeDefinition::Record(record) => TypeSymbol {
                        definition: TypeDefinition::Record(resolve_record(record)?),
                        origin: symbol.origin,
                        opacity: symbol.opacity.clone(),
                        arity: symbol.arity,
                        kind: symbol.kind.clone(),
                    },

                    TypeDefinition::Signature(sig) => TypeSymbol {
                        definition: TypeDefinition::Signature(SignatureSymbol {
                            vtable: resolve_record(&sig.vtable)?,
                            supersignatures: sig
                                .supersignatures
                                .iter()
                                .map(|c| c.resolve_names(self, pi, semantic_scope))
                                .collect::<Naming<Vec<_>>>()?,
                        }),
                        origin: symbol.origin,
                        opacity: symbol.opacity.clone(),
                        arity: symbol.arity,
                        kind: symbol.kind.clone(),
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
                        opacity: symbol.opacity.clone(),
                        arity: symbol.arity,
                        kind: symbol.kind.clone(),
                    },

                    TypeDefinition::Builtin(base_type) => TypeSymbol {
                        definition: TypeDefinition::Builtin(*base_type),
                        origin: symbol.origin,
                        opacity: symbol.opacity.clone(),
                        arity: symbol.arity,
                        kind: Kind::default(),
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

impl<Id> fmt::Display for DependencyMatrix<Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { graph, witnesses } = self;
        write!(f, "graph: ")?;
        for (k, v) in graph {
            write!(f, "{k} -> {}; ", display_list(", ", v))?;
        }
        writeln!(f, ".")?;
        write!(
            f,
            "witnesses: {}",
            display_list(", ", &witnesses.iter().collect::<Vec<_>>())
        )
    }
}
