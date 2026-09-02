use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt,
    marker::PhantomData,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering as AtomicOrdering},
};

use crate::{
    ast::{
        self,
        annotation::Annotated,
        namer::{QualifiedName, TypeOrigin},
        pattern::{MatchClause, Pattern},
    },
    bridge::Bridge,
    compiler, lambda_lift,
    lexer::BindingOperator,
    parser::{self, IdentifierPath},
    typer::display_list,
};

pub mod annotation;
pub mod constraints;
pub mod desugar;
pub mod namer;
pub mod pattern;

pub const ROOT_MODULE_NAME: &str = "Root"; // This should be the main source file name
pub const BUILTIN_MODULE_NAME: &str = "__builtin__";
pub const STDLIB_MODULE_NAME: &str = "stdlib";

#[derive(Debug)]
pub struct CompilationUnit<A> {
    pub root_module: ModuleDeclaration<A>,
    pub compiler: compiler::Compiler,
}

#[derive(Debug)]
pub enum Declaration<A> {
    Value(A, ValueDeclaration<A>),
    Module(A, ModuleDeclaration<A>),
    Type(A, TypeDeclaration<A>),
    Use(A, UseDeclaration<A>),
    Signature(A, SignatureDeclaration<A>),
    Witness(A, WitnessDeclaration<A>),
    Foreign(A, ForeignDeclaration<A>),
}

#[derive(Debug, Clone)]
pub struct IdentifierPattern<A>(Pattern<A, IdentifierPath>);

impl<A> IdentifierPattern<A>
where
    A: Copy,
{
    pub fn from_atom(a: A, image: &str) -> Self {
        Self::from_path(a, IdentifierPath::new(image))
    }

    pub fn from_path(a: A, path: IdentifierPath) -> Self {
        Self(Pattern::Bind(a, path))
    }

    pub fn with_appended_path_segment(&self, segment: &str) -> Self {
        let Self(Pattern::Bind(a, path)) = self else {
            panic!("malaise")
        };
        Self::from_path(*a, path.clone().with_suffix(segment))
    }

    pub fn into_pattern(self) -> Pattern<A, IdentifierPath> {
        self.0
    }

    pub fn try_into_simple_bind(self) -> Option<IdentifierPath> {
        if let Pattern::Bind(_, id) = self.0 {
            Some(id)
        } else {
            None
        }
    }

    pub fn is_simple_bind(&self) -> bool {
        matches!(self, Self(Pattern::Bind(..)))
    }
}

impl<A> From<Pattern<A, IdentifierPath>> for IdentifierPattern<A> {
    fn from(value: Pattern<A, IdentifierPath>) -> Self {
        Self(value)
    }
}

#[derive(Debug)]
pub struct SignatureDeclaration<A> {
    pub name: parser::Identifier,
    pub type_parameters: Vec<TypeVariable>,
    /// Supersignature constraints (the `|-` context): signatures this one
    /// requires, the analog of Haskell superclasses. Empty for a plain signature.
    pub constraints: Vec<ConstraintExpression<A, parser::IdentifierPath>>,
    pub declarator: RecordDeclarator<A>,
}

#[derive(Debug)]
pub struct WitnessDeclaration<A> {
    pub type_signature: TypeSignature<A, parser::IdentifierPath>,
    pub implementation: ast::Expr<A, IdentifierPattern<A>>,
}

#[derive(Debug)]
pub struct ForeignDeclaration<A> {
    pub name: parser::Identifier,
    pub type_signature: TypeSignature<A, parser::IdentifierPath>,
}

#[derive(Debug)]
pub struct UseDeclaration<A> {
    pub qualified_binder: Option<parser::Identifier>,
    pub path: parser::IdentifierPath,
    _phase: std::marker::PhantomData<A>,
}

impl<A> UseDeclaration<A> {
    pub fn new(qualified_binder: Option<parser::Identifier>, path: parser::IdentifierPath) -> Self {
        Self {
            qualified_binder,
            path,
            _phase: std::marker::PhantomData,
        }
    }
}

#[derive(Debug)]
pub struct ValueDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ValueDeclarator<A>,
}

#[derive(Debug)]
pub struct ValueDeclarator<A> {
    pub type_signature: Option<TypeSignature<A, parser::IdentifierPath>>,
    pub body: ast::Expr<A, IdentifierPattern<A>>,
}

#[derive(Debug)]
pub struct ModuleDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ModuleDeclarator<A>,
}

#[derive(Debug)]
pub enum ModuleDeclarator<A> {
    Inline(Vec<Declaration<A>>),
    External(parser::Identifier),
}

#[derive(Debug)]
pub struct TypeDeclaration<A> {
    pub name: parser::Identifier,
    pub type_parameters: Vec<TypeVariable>,
    pub declarator: TypeDeclarator<A>,
    pub origin: TypeOrigin,
    pub opaque: bool,
    pub confinement: Option<ConfinementModifier>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ConfinementModifier {
    Confined,
    Unconfined,
}

impl fmt::Display for ConfinementModifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Confined => write!(f, "confined"),
            Self::Unconfined => write!(f, "unconfined"),
        }
    }
}

#[derive(Debug)]
pub enum TypeDeclarator<A> {
    Record(A, RecordDeclarator<A>),
    Coproduct(A, CoproductDeclarator<A>),
    Alias(A, TypeExpression<A, parser::IdentifierPath>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TypeVariable {
    pub name: parser::Identifier,
    pub kind: Kind,
}

impl TypeVariable {
    pub fn star(name: parser::Identifier) -> Self {
        Self::with_kind(name, Kind::default())
    }

    pub fn with_kind(name: parser::Identifier, kind: Kind) -> Self {
        Self { name, kind }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    Star(Confinement),
    Arrow(Box<Kind>, Box<Kind>),
}

impl Default for Kind {
    fn default() -> Self {
        Self::Star(Confinement::fresh())
    }
}

impl Kind {
    pub fn star() -> Self {
        Self::default()
    }

    pub fn unconfined() -> Self {
        Self::Star(Confinement::Unconfined)
    }

    pub fn confined() -> Self {
        Self::Star(Confinement::Confined)
    }

    pub fn is_star(&self) -> bool {
        matches!(self, Self::Star(_))
    }

    pub fn confinement(&self) -> Option<&Confinement> {
        match self {
            Self::Star(confinement) => Some(confinement),
            Self::Arrow(..) => None,
        }
    }

    pub fn result_confinement(&self) -> Option<&Confinement> {
        match self {
            Self::Star(confinement) => Some(confinement),
            Self::Arrow(_, codomain) => codomain.result_confinement(),
        }
    }

    pub fn with_result_confinement(&self, result: Confinement) -> Self {
        match self {
            Self::Star(_) => Self::Star(result),
            Self::Arrow(domain, codomain) => Self::Arrow(
                domain.clone(),
                codomain.with_result_confinement(result).into(),
            ),
        }
    }

    pub fn apply_confinement_substitutions(
        &self,
        substitutions: &BTreeMap<u32, Confinement>,
    ) -> Self {
        match self {
            Self::Star(confinement) => Self::Star(confinement.apply(substitutions)),
            Self::Arrow(domain, codomain) => Self::Arrow(
                domain.apply_confinement_substitutions(substitutions).into(),
                codomain
                    .apply_confinement_substitutions(substitutions)
                    .into(),
            ),
        }
    }

    /// Match a constructor-kind pattern against an argument kind. Capability
    /// variables in the pattern are local binders for this kind application.
    pub fn match_argument(
        &self,
        actual: &Self,
        substitutions: &mut BTreeMap<u32, Confinement>,
    ) -> bool {
        match (self, actual) {
            (Self::Star(expected), Self::Star(actual)) => {
                expected.bind_pattern(actual, substitutions)
            }
            (Self::Arrow(expected_a, expected_b), Self::Arrow(actual_a, actual_b)) => {
                expected_a.match_argument(actual_a, substitutions)
                    && expected_b.match_argument(actual_b, substitutions)
            }
            _ => false,
        }
    }

    pub fn is_compatible_with(&self, other: &Self) -> bool {
        match (self, other) {
            // Confinement is an index on inhabited types, not part of their
            // runtime shape identity. Type unification reconciles the shapes;
            // capability constraints are checked at capability ascriptions.
            (Self::Star(_), Self::Star(_)) => true,
            (Self::Arrow(lhs_a, lhs_b), Self::Arrow(rhs_a, rhs_b)) => {
                lhs_a.is_compatible_with(rhs_a) && lhs_b.is_compatible_with(rhs_b)
            }
            _ => false,
        }
    }

    /// Unify only the hidden confinement indices while requiring the ordinary
    /// kind-arrow shape to match. Type metavariables use this when they are bound
    /// to a concrete type, so a capability ascription such as `*unconfined`
    /// cannot silently accept a confined argument.
    pub fn unify_confinements(&self, other: &Self) -> Option<BTreeMap<u32, Confinement>> {
        fn merge(
            lhs: BTreeMap<u32, Confinement>,
            rhs: BTreeMap<u32, Confinement>,
        ) -> Option<BTreeMap<u32, Confinement>> {
            let mut combined = lhs;
            for (id, value) in rhs {
                if let Some(existing) = combined.get(&id).cloned() {
                    let reconciliation = existing.unify(&value)?;
                    for value in combined.values_mut() {
                        *value = value.apply(&reconciliation);
                    }
                    combined.extend(reconciliation);
                } else {
                    combined.insert(id, value);
                }
            }
            Some(combined)
        }

        match (self, other) {
            (Self::Star(lhs), Self::Star(rhs)) => lhs.unify(rhs),
            (Self::Arrow(lhs_domain, lhs_codomain), Self::Arrow(rhs_domain, rhs_codomain)) => {
                let domain = lhs_domain.unify_confinements(rhs_domain)?;
                let lhs_codomain = lhs_codomain.apply_confinement_substitutions(&domain);
                let rhs_codomain = rhs_codomain.apply_confinement_substitutions(&domain);
                merge(domain, lhs_codomain.unify_confinements(&rhs_codomain)?)
            }
            _ => None,
        }
    }

    pub fn freshen_confinement_variables(&self, fresh: &mut BTreeMap<u32, Confinement>) -> Self {
        match self {
            Self::Star(confinement) => Self::Star(confinement.freshen(fresh)),
            Self::Arrow(domain, codomain) => Self::Arrow(
                domain.freshen_confinement_variables(fresh).into(),
                codomain.freshen_confinement_variables(fresh).into(),
            ),
        }
    }

    pub fn confinement_variables(&self) -> BTreeSet<u32> {
        match self {
            Self::Star(confinement) => confinement.variables(),
            Self::Arrow(domain, codomain) => domain
                .confinement_variables()
                .into_iter()
                .chain(codomain.confinement_variables())
                .collect(),
        }
    }
}

/// The hidden index on an inhabited kind. `Join` is the two-point lattice join:
/// one confined component taints the complete applied type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Confinement {
    Unconfined,
    Confined,
    Variable(u32),
    Join(BTreeSet<Confinement>),
}

impl From<ConfinementModifier> for Confinement {
    fn from(value: ConfinementModifier) -> Self {
        match value {
            ConfinementModifier::Confined => Self::Confined,
            ConfinementModifier::Unconfined => Self::Unconfined,
        }
    }
}

static FRESH_CONFINEMENT_ID: AtomicU32 = AtomicU32::new(0);

impl Confinement {
    pub fn fresh() -> Self {
        Self::Variable(FRESH_CONFINEMENT_ID.fetch_add(1, AtomicOrdering::SeqCst))
    }

    pub fn join<I>(parts: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut joined = BTreeSet::new();
        for part in parts {
            match part {
                Self::Unconfined => {}
                Self::Confined => return Self::Confined,
                Self::Join(nested) => joined.extend(nested),
                variable => {
                    joined.insert(variable);
                }
            }
        }
        match joined.len() {
            0 => Self::Unconfined,
            1 => joined.into_iter().next().unwrap(),
            _ => Self::Join(joined),
        }
    }

    pub fn apply(&self, substitutions: &BTreeMap<u32, Self>) -> Self {
        match self {
            Self::Variable(id) => substitutions
                .get(id)
                .map(|replacement| replacement.apply(substitutions))
                .unwrap_or_else(|| self.clone()),
            Self::Join(parts) => Self::join(parts.iter().map(|part| part.apply(substitutions))),
            _ => self.clone(),
        }
    }

    pub fn variables(&self) -> BTreeSet<u32> {
        match self {
            Self::Variable(id) => BTreeSet::from([*id]),
            Self::Join(parts) => parts
                .iter()
                .flat_map(Self::variables)
                .collect::<BTreeSet<_>>(),
            _ => BTreeSet::new(),
        }
    }

    pub fn freshen(&self, fresh: &mut BTreeMap<u32, Self>) -> Self {
        match self {
            Self::Variable(id) => fresh.entry(*id).or_insert_with(Self::fresh).clone(),
            Self::Join(parts) => Self::join(parts.iter().map(|part| part.freshen(fresh))),
            _ => self.clone(),
        }
    }

    pub fn unify(&self, other: &Self) -> Option<BTreeMap<u32, Self>> {
        fn go(
            lhs: Confinement,
            rhs: Confinement,
            substitutions: &mut BTreeMap<u32, Confinement>,
        ) -> bool {
            let lhs = lhs.apply(substitutions);
            let rhs = rhs.apply(substitutions);
            if lhs == rhs {
                return true;
            }
            match (lhs, rhs) {
                (Confinement::Join(lhs), Confinement::Join(rhs)) => {
                    let common = lhs.intersection(&rhs).cloned().collect::<BTreeSet<_>>();
                    if common.is_empty() {
                        // Independently instantiated copies of the same symbolic
                        // join have disjoint variable ids. Pairing their normalized
                        // operands yields a deterministic alpha-renaming unifier.
                        return lhs.len() == rhs.len()
                            && lhs
                                .into_iter()
                                .zip(rhs)
                                .all(|(lhs, rhs)| go(lhs, rhs, substitutions));
                    }
                    let lhs = Confinement::join(lhs.difference(&common).cloned());
                    let rhs = Confinement::join(rhs.difference(&common).cloned());
                    go(lhs, rhs, substitutions)
                }
                (Confinement::Variable(id), Confinement::Join(parts))
                | (Confinement::Join(parts), Confinement::Variable(id))
                    if parts.contains(&Confinement::Variable(id)) =>
                {
                    // κ = κ ⊔ rest. Capability inference chooses the least
                    // solution, so every additional component is bottom.
                    let rest = Confinement::join(
                        parts
                            .into_iter()
                            .filter(|part| *part != Confinement::Variable(id)),
                    );
                    let Some(required) = rest.require(Confinement::Unconfined) else {
                        return false;
                    };
                    for (id, value) in required {
                        substitutions.insert(id, value);
                    }
                    true
                }
                (Confinement::Variable(id), value) | (value, Confinement::Variable(id))
                    if !value.variables().contains(&id) =>
                {
                    substitutions.insert(id, value);
                    true
                }
                _ => false,
            }
        }

        let mut substitutions = BTreeMap::new();
        go(self.clone(), other.clone(), &mut substitutions).then_some(substitutions)
    }

    /// Solve an exact capability ascription. The bottom requirement distributes
    /// through joins: `κ1 ⊔ κ2 = unconfined` implies both operands are
    /// unconfined. The corresponding confined equation is disjunctive, so a join
    /// of unresolved variables is deliberately rejected rather than guessed.
    pub fn require(&self, required: Self) -> Option<BTreeMap<u32, Self>> {
        fn require_unconfined(
            actual: Confinement,
            substitutions: &mut BTreeMap<u32, Confinement>,
        ) -> bool {
            match actual.apply(substitutions) {
                Confinement::Unconfined => true,
                Confinement::Confined => false,
                Confinement::Variable(id) => {
                    substitutions.insert(id, Confinement::Unconfined);
                    true
                }
                Confinement::Join(parts) => parts
                    .into_iter()
                    .all(|part| require_unconfined(part, substitutions)),
            }
        }

        if required == Self::Unconfined {
            let mut substitutions = BTreeMap::new();
            require_unconfined(self.clone(), &mut substitutions).then_some(substitutions)
        } else {
            self.unify(&required)
        }
    }

    fn bind_pattern(&self, actual: &Self, substitutions: &mut BTreeMap<u32, Self>) -> bool {
        match self.apply(substitutions) {
            Self::Variable(id) => {
                let actual = actual.apply(substitutions);
                if actual != Self::Variable(id) {
                    substitutions.insert(id, actual);
                }
                true
            }
            expected => expected == actual.apply(substitutions),
        }
    }
}

#[derive(Debug)]
pub struct RecordDeclarator<A> {
    pub fields: Vec<FieldDeclarator<A>>,
}

#[derive(Debug)]
pub struct CoproductDeclarator<A> {
    pub constructors: Vec<CoproductConstructor<A>>,
}

#[derive(Debug)]
pub struct CoproductConstructor<A> {
    pub name: parser::Identifier,
    pub signature: Vec<TypeExpression<A, parser::IdentifierPath>>,
}

#[derive(Debug)]
pub struct FieldDeclarator<A> {
    pub name: parser::Identifier,
    pub type_signature: TypeSignature<A, parser::IdentifierPath>,
}

#[derive(Debug, Clone)]
pub struct ConstraintExpression<A, TypeId> {
    pub annotation: A,
    pub class: TypeId,
    pub parameters: Vec<TypeExpression<A, TypeId>>,
}

impl<A, TypeId> ConstraintExpression<A, TypeId> {
    fn map_names<F, B>(self, f: &F) -> ConstraintExpression<A, B>
    where
        F: Fn(TypeId) -> B,
    {
        let Self {
            annotation,
            class,
            parameters,
        } = self;
        ConstraintExpression {
            annotation,
            class: f(class),
            parameters: parameters.into_iter().map(|p| p.map_name(f)).collect(),
        }
    }

    pub fn into_type_expression(self) -> TypeExpression<A, TypeId>
    where
        A: Clone,
    {
        let Self {
            annotation,
            class,
            parameters,
        } = self;
        parameters.into_iter().fold(
            TypeExpression::Constructor(annotation.clone(), class),
            |f, x| {
                TypeExpression::Apply(
                    annotation.clone(),
                    ApplyTypeExpr {
                        function: f.into(),
                        argument: x.into(),
                        phase: PhantomData,
                    },
                )
            },
        )
    }
}

#[derive(Debug, Clone)]
pub struct TypeSignature<A, TypeId> {
    pub universal_quantifiers: Vec<TypeVariable>,
    pub constraints: Vec<ConstraintExpression<A, TypeId>>,
    pub body: TypeExpression<A, TypeId>,
    pub phase: PhantomData<A>,
}

impl<A, TypeId> TypeSignature<A, TypeId> {
    pub fn map_names<F, B>(self, f: &F) -> TypeSignature<A, B>
    where
        F: Fn(TypeId) -> B,
    {
        let Self {
            universal_quantifiers,
            constraints,
            body,
            phase,
        } = self;
        TypeSignature {
            universal_quantifiers,
            constraints: constraints.into_iter().map(|c| c.map_names(f)).collect(),
            body: body.map_name(f),
            phase,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeExpression<A, TypeId> {
    Constructor(A, TypeId),
    Parameter(A, parser::Identifier),
    Apply(A, ApplyTypeExpr<A, TypeId>),
    ConfinementAscription(A, Box<TypeExpression<A, TypeId>>, ConfinementModifier),
    Arrow(A, ArrowTypeExpr<A, TypeId>),
    Tuple(A, TupleTypeExpr<A, TypeId>),
}

impl<A, TypeId> Default for TypeExpression<A, TypeId>
where
    A: Default,
{
    fn default() -> Self {
        Self::Tuple(A::default(), TupleTypeExpr(vec![]))
    }
}

impl<A, TypeId> TypeExpression<A, TypeId> {
    pub fn annotation(&self) -> &A {
        match self {
            Self::Constructor(a, _)
            | Self::Parameter(a, _)
            | Self::Apply(a, _)
            | Self::ConfinementAscription(a, _, _)
            | Self::Arrow(a, _)
            | Self::Tuple(a, _) => a,
        }
    }

    pub fn arrow_arity(&self) -> usize {
        match self {
            Self::Arrow(_, arrow) => 1 + arrow.codomain.arrow_arity(),
            _ => 0,
        }
    }

    fn map_name<F, B>(self, f: &F) -> TypeExpression<A, B>
    where
        F: Fn(TypeId) -> B,
    {
        match self {
            Self::Constructor(a, name) => TypeExpression::Constructor(a, f(name)),
            Self::Parameter(a, id) => TypeExpression::Parameter(a, id),
            Self::Apply(
                a,
                ApplyTypeExpr {
                    function, argument, ..
                },
            ) => TypeExpression::Apply(
                a,
                ApplyTypeExpr {
                    function: function.map_name(f).into(),
                    argument: argument.map_name(f).into(),
                    phase: PhantomData,
                },
            ),
            Self::ConfinementAscription(a, body, confinement) => {
                TypeExpression::ConfinementAscription(a, body.map_name(f).into(), confinement)
            }
            Self::Arrow(
                a,
                ArrowTypeExpr {
                    capture,
                    domain,
                    codomain,
                },
            ) => TypeExpression::Arrow(
                a,
                ArrowTypeExpr {
                    capture,
                    domain: domain.map_name(f).into(),
                    codomain: codomain.map_name(f).into(),
                },
            ),
            Self::Tuple(a, TupleTypeExpr(elements)) => TypeExpression::Tuple(
                a,
                TupleTypeExpr(elements.into_iter().map(|e| e.map_name(f)).collect()),
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TupleTypeExpr<A, TypeId>(pub Vec<TypeExpression<A, TypeId>>);

#[derive(Debug, Clone)]
pub struct ApplyTypeExpr<A, TypeId> {
    pub function: Box<TypeExpression<A, TypeId>>,
    pub argument: Box<TypeExpression<A, TypeId>>,
    pub phase: PhantomData<TypeId>,
}

#[derive(Debug, Clone)]
pub struct ArrowTypeExpr<A, TypeId> {
    /// Hidden confinement index of the function value's closure environment.
    pub capture: Confinement,
    pub domain: Box<TypeExpression<A, TypeId>>,
    pub codomain: Box<TypeExpression<A, TypeId>>,
}

pub type Tree<A, Id> = Rc<Expr<A, Id>>;

#[derive(Debug, Clone)]
pub enum Expr<A, Id> {
    Variable(A, Id),
    InvokeBridge(A, Bridge),
    Constant(A, Literal),
    RecursiveLambda(A, SelfReferential<A, Id>),
    Lambda(A, Lambda<A, Id>),
    Apply(A, Apply<A, Id>),
    Let(A, Binding<A, Id>),
    Tuple(A, Tuple<A, Id>),
    Record(A, Record<A, Id>),
    RecordUpdate(A, RecordUpdate<A, Id>),
    Inject(A, Injection<A, Id>),
    Array(A, Array<A, Id>),
    Project(A, Projection<A, Id>),
    Sequence(A, Sequence<A, Id>),
    Deconstruct(A, Deconstruct<A, Id>),
    If(A, IfThenElse<A, Id>),
    Interpolate(A, Interpolate<A, Id>),
    Ascription(A, TypeAscription<A, Id>),
    MakeClosure(A, lambda_lift::ClosureInfo),
}

impl<A, Id> Expr<A, Id> {
    pub fn annotation(&self) -> &A {
        match self {
            Self::Variable(a, ..)
            | Self::InvokeBridge(a, ..)
            | Self::Constant(a, ..)
            | Self::RecursiveLambda(a, ..)
            | Self::Lambda(a, ..)
            | Self::Apply(a, ..)
            | Self::Let(a, ..)
            | Self::Record(a, ..)
            | Self::RecordUpdate(a, ..)
            | Self::Tuple(a, ..)
            | Self::Inject(a, ..)
            | Self::Array(a, ..)
            | Self::Project(a, ..)
            | Self::Sequence(a, ..)
            | Self::Deconstruct(a, ..)
            | Self::If(a, ..)
            | Self::Interpolate(a, ..)
            | Self::Ascription(a, ..)
            | Self::MakeClosure(a, ..) => a,
        }
    }

    pub fn erase_annotation(&self) -> Expr<Erased, Id>
    where
        Self: Annotated<A, Erased, Id, Output = Expr<Erased, Id>>,
    {
        self.map_annotation(&|_| Erased)
    }

    /// Visit an expression tree by reference without rebuilding it. This is the
    /// read-only counterpart to `map`; analyses such as closure-capture inference
    /// should not clone a complete nested lambda body merely to inspect it.
    pub fn walk<F>(&self, visitor: &mut F)
    where
        F: FnMut(&Expr<A, Id>),
    {
        visitor(self);
        let mut walk_tree = |tree: &Tree<A, Id>| tree.as_ref().walk(visitor);
        match self {
            Self::RecursiveLambda(_, recursive) => walk_tree(&recursive.lambda.body),
            Self::Lambda(_, lambda) => walk_tree(&lambda.body),
            Self::Apply(_, apply) => {
                walk_tree(&apply.function);
                walk_tree(&apply.argument);
            }
            Self::Let(_, binding) => {
                walk_tree(&binding.bound);
                walk_tree(&binding.body);
            }
            Self::Tuple(_, tuple) => tuple.elements.iter().for_each(&mut walk_tree),
            Self::Record(_, record) => record.fields.iter().for_each(|(_, value)| walk_tree(value)),
            Self::RecordUpdate(_, update) => {
                walk_tree(&update.base);
                update
                    .fields
                    .iter()
                    .for_each(|field| walk_tree(&field.value));
            }
            Self::Inject(_, injection) => injection.arguments.iter().for_each(&mut walk_tree),
            Self::Array(_, array) => array.elements.iter().for_each(&mut walk_tree),
            Self::Project(_, projection) => walk_tree(&projection.base),
            Self::Sequence(_, sequence) => {
                walk_tree(&sequence.this);
                walk_tree(&sequence.and_then);
            }
            Self::Deconstruct(_, deconstruct) => {
                walk_tree(&deconstruct.scrutinee);
                deconstruct
                    .match_clauses
                    .iter()
                    .for_each(|clause| walk_tree(&clause.consequent));
            }
            Self::If(_, conditional) => {
                walk_tree(&conditional.predicate);
                walk_tree(&conditional.consequent);
                walk_tree(&conditional.alternate);
            }
            Self::Interpolate(_, Interpolate(segments)) => {
                segments.iter().for_each(|segment| {
                    if let Segment::Expression(expression) = segment {
                        walk_tree(expression);
                    }
                });
            }
            Self::Ascription(_, ascription) => walk_tree(&ascription.ascribed_tree),
            Self::Variable(..)
            | Self::InvokeBridge(..)
            | Self::Constant(..)
            | Self::MakeClosure(..) => {}
        }
    }

    pub fn map<F>(self, f: &mut F) -> Expr<A, Id>
    where
        F: FnMut(Expr<A, Id>) -> Expr<A, Id>,
        A: Clone,
        Id: Clone,
    {
        fn go<A, Id, F>(tree: Tree<A, Id>, f: &mut F) -> Tree<A, Id>
        where
            F: FnMut(Expr<A, Id>) -> Expr<A, Id>,
            A: Clone,
            Id: Clone,
        {
            let owned = Rc::unwrap_or_clone(tree);
            Rc::new(owned.map(f))
        }

        let rebuilt = match self {
            Expr::RecursiveLambda(a, the) => Expr::RecursiveLambda(
                a,
                SelfReferential {
                    own_name: the.own_name,
                    lambda: Lambda {
                        parameter: the.lambda.parameter,
                        body: go(the.lambda.body, f),
                    },
                },
            ),

            Expr::Lambda(a, the) => Expr::Lambda(
                a,
                Lambda {
                    parameter: the.parameter,
                    body: go(the.body, f),
                },
            ),

            Expr::Apply(a, the) => Expr::Apply(
                a,
                Apply {
                    function: go(the.function, f),
                    argument: go(the.argument, f),
                },
            ),

            Expr::Let(a, the) => Expr::Let(
                a,
                Binding {
                    binder: the.binder,
                    operator: the.operator,
                    bound: go(the.bound, f),
                    body: go(the.body, f),
                },
            ),

            Expr::Tuple(a, the) => Expr::Tuple(
                a,
                Tuple {
                    elements: the.elements.into_iter().map(|e| go(e, f)).collect(),
                },
            ),

            Expr::Record(a, the) => Expr::Record(
                a,
                Record {
                    fields: the.fields.into_iter().map(|(k, v)| (k, go(v, f))).collect(),
                },
            ),

            Expr::RecordUpdate(a, the) => Expr::RecordUpdate(
                a,
                RecordUpdate {
                    base: go(the.base, f),
                    fields: the
                        .fields
                        .into_iter()
                        .map(|field| RecordUpdateField {
                            path: field.path,
                            indices: field.indices,
                            arities: field.arities,
                            value: go(field.value, f),
                        })
                        .collect(),
                    field_order: the.field_order,
                },
            ),

            Expr::Inject(a, the) => Expr::Inject(
                a,
                Injection {
                    constructor: the.constructor,
                    arguments: the.arguments.into_iter().map(|e| go(e, f)).collect(),
                },
            ),

            Expr::Project(a, the) => Expr::Project(
                a,
                Projection {
                    base: go(the.base, f),
                    select: the.select,
                },
            ),

            Expr::Sequence(a, the) => Expr::Sequence(
                a,
                Sequence {
                    this: go(the.this, f),
                    and_then: go(the.and_then, f),
                },
            ),

            Expr::Deconstruct(a, the) => Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee: go(the.scrutinee, f),
                    match_clauses: the
                        .match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern,
                            consequent: go(clause.consequent, f),
                        })
                        .collect(),
                },
            ),

            Expr::If(a, the) => Expr::If(
                a,
                IfThenElse {
                    predicate: go(the.predicate, f),
                    consequent: go(the.consequent, f),
                    alternate: go(the.alternate, f),
                },
            ),

            Expr::Interpolate(a, the) => Expr::Interpolate(
                a,
                Interpolate(
                    the.0
                        .into_iter()
                        .map(|s| match s {
                            Segment::Expression(expr) => Segment::Expression(go(expr, f)),
                            other => other,
                        })
                        .collect(),
                ),
            ),

            Expr::Ascription(a, the) => Expr::Ascription(
                a,
                TypeAscription {
                    ascribed_tree: go(the.ascribed_tree, f),
                    type_signature: the.type_signature,
                },
            ),

            simple => simple,
        };

        f(rebuilt)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Erased;

#[derive(Debug, Clone)]
pub struct Interpolate<A, Id>(pub Vec<Segment<A, Id>>);

#[derive(Debug, Clone)]
pub enum Segment<A, Id> {
    Literal(A, Literal),
    Expression(Tree<A, Id>),
}

#[derive(Debug, Clone)]
pub struct TypeAscription<A, Id> {
    pub ascribed_tree: Tree<A, Id>,
    pub type_signature: TypeSignature<A, QualifiedName>,
}

#[derive(Debug, Clone)]
pub struct Deconstruct<A, Id> {
    pub scrutinee: Tree<A, Id>,
    pub match_clauses: Vec<pattern::MatchClause<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct IfThenElse<A, Id> {
    pub predicate: Tree<A, Id>,
    pub consequent: Tree<A, Id>,
    pub alternate: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct Record<A, Id> {
    pub fields: Vec<(parser::Identifier, Tree<A, Id>)>,
}

#[derive(Debug, Clone)]
pub struct RecordUpdate<A, Id> {
    pub base: Tree<A, Id>,
    pub fields: Vec<RecordUpdateField<A, Id>>,
    /// Canonical field order, filled by the typer once the nominal record type
    /// of the base is known. Empty in parsed and named trees.
    pub field_order: Vec<parser::Identifier>,
}

#[derive(Debug, Clone)]
pub struct RecordUpdateField<A, Id> {
    pub path: Vec<parser::Identifier>,
    /// Positional selector and containing-record arity for every path segment;
    /// populated by the typer and empty in parsed/named trees.
    pub indices: Vec<usize>,
    pub arities: Vec<usize>,
    pub value: Tree<A, Id>,
}

impl<A, Id> Record<A, Id> {
    pub fn from_fields(fields: &[(parser::Identifier, Tree<A, Id>)]) -> Self {
        let mut fields = fields.to_vec();
        fields.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self { fields }
    }
}

#[derive(Debug, Clone)]
pub struct Tuple<A, Id> {
    pub elements: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Text(String),
    Bool(bool),
    Unit,
    Char(char),
}

impl Literal {
    fn variant_rank(&self) -> u8 {
        match self {
            Self::Int(..) => 0,
            Self::Float(..) => 1,
            Self::Text(..) => 2,
            Self::Bool(..) => 3,
            Self::Unit => 4,
            Self::Char(..) => 5,
        }
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Literal {}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Int(lhs), Self::Int(rhs)) => lhs.cmp(rhs),

            (Self::Float(lhs), Self::Float(rhs)) => lhs.total_cmp(rhs),

            (Self::Text(lhs), Self::Text(rhs)) => lhs.cmp(rhs),

            (Self::Bool(lhs), Self::Bool(rhs)) => lhs.cmp(rhs),

            (Self::Unit, Self::Unit) => Ordering::Equal,

            (Self::Char(lhs), Self::Char(rhs)) => lhs.cmp(rhs),

            _ => self.variant_rank().cmp(&other.variant_rank()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Binding<A, Id> {
    pub binder: Id,
    pub operator: BindingOperator,
    pub bound: Tree<A, Id>,
    pub body: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct SelfReferential<A, Id> {
    pub own_name: Id,
    pub lambda: Lambda<A, Id>,
}

impl<A, Id> SelfReferential<A, Id> {
    pub fn annotation(&self) -> &A {
        self.lambda.annotation()
    }
}

#[derive(Debug, Clone)]
pub struct Lambda<A, Id> {
    pub parameter: Id,
    pub body: Tree<A, Id>,
}

impl<A, Id> Lambda<A, Id> {
    pub fn annotation(&self) -> &A {
        self.body.annotation()
    }
}

#[derive(Debug, Clone)]
pub struct Apply<A, Id> {
    pub function: Tree<A, Id>,
    pub argument: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct Projection<A, Id> {
    pub base: Tree<A, Id>,
    pub select: ProductElement,
}

#[derive(Debug, Clone)]
pub enum ProductElement {
    Ordinal(usize),
    Name(parser::Identifier),
}

#[derive(Debug, Clone)]
pub struct Injection<A, Id> {
    pub constructor: QualifiedName,
    pub arguments: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct Array<A, Id> {
    pub elements: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct Sequence<A, Id> {
    pub this: Tree<A, Id>,
    pub and_then: Tree<A, Id>,
}

impl<A, Id> fmt::Display for Expr<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(_, x) => write!(f, "{x}"),
            Self::InvokeBridge(_, x) => write!(f, "bridge_{}", x),
            Self::Constant(_, x) => write!(f, "{x}"),
            Self::RecursiveLambda(_, x) => write!(f, "{} := {}", x.own_name, x.lambda),
            Self::Lambda(_, x) => write!(f, "{}", x),
            Self::Apply(_, x) => write!(f, "({} {})", x.function, x.argument),
            Self::Let(_, x) => write!(f, "let {} = {} in {}", x.binder, x.bound, x.body),
            Self::Record(_, x) => write!(f, "{x}"),
            Self::RecordUpdate(_, x) => {
                write!(f, "{{ {}: ", x.base)?;
                for (i, field) in x.fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    for (j, name) in field.path.iter().enumerate() {
                        if j > 0 {
                            write!(f, ".")?;
                        }
                        write!(f, "{name}")?;
                    }
                    write!(f, " := {}", field.value)?;
                }
                write!(f, " }}")
            }
            Self::Tuple(_, x) => write!(f, "{x}"),
            Self::Inject(_, x) => {
                write!(
                    f,
                    "{} {}",
                    x.constructor,
                    Tuple {
                        elements: x.arguments.clone()
                    }
                )
            }
            Self::Array(_, x) => write!(f, "[{x}]"),
            Self::Project(_, x) => write!(f, "{}.{}", x.base, x.select),
            Self::Sequence(_, x) => write!(f, "{}; {}", x.this, x.and_then),
            Self::Deconstruct(_, x) => write!(f, "{x}"),
            Self::If(_, x) => write!(f, "{x}"),
            Self::Interpolate(_, x) => write!(f, "{x}"),
            Self::Ascription(_, x) => write!(f, "{}::{}", x.ascribed_tree, x.type_signature),
            Self::MakeClosure(_, x) => write!(f, "mk_clo {x}."),
        }
    }
}

impl<A, Id> fmt::Display for Array<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Array { elements } = self;
        writeln!(f, "[")?;
        for element in elements {
            writeln!(f, "{element}")?;
        }
        writeln!(f, "]")
    }
}

impl<A, Id> fmt::Display for Interpolate<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(segments) = self;
        let segments = segments.iter().map(|s| s.to_string()).collect::<Vec<_>>();

        write!(f, "{}", segments.join(" "))
    }
}

impl<A, Id> fmt::Display for Segment<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Segment::Literal(_, literal) => write!(f, "<{literal}>"),
            Segment::Expression(expr) => write!(f, "<{expr}>"),
        }
    }
}

impl fmt::Display for Erased {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
}

impl<A, Id> fmt::Display for Projection<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { base, select } = self;
        write!(f, "{base}.{select}")
    }
}

impl<A, Id> fmt::Display for Deconstruct<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            scrutinee,
            match_clauses,
        } = self;
        write!(f, "deconstruct {scrutinee}:")?;

        for clause in match_clauses {
            write!(f, "| {} -> {}", clause.pattern, clause.consequent)?;
        }

        Ok(())
    }
}

impl<A, Id> fmt::Display for IfThenElse<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            predicate,
            consequent,
            alternate,
        } = self;
        write!(f, "if {predicate} then {consequent} else {alternate}")
    }
}

impl fmt::Display for ProductElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ordinal(id) => write!(f, "&{id}"),
            Self::Name(id) => write!(f, "\"{id}\""),
        }
    }
}

impl<A, Id> fmt::Display for Lambda<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { parameter, body } = self;
        write!(f, "λ{parameter}. {body}")
    }
}

impl<A, Id> fmt::Display for Record<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let record_rendering = self
            .fields
            .iter()
            .map(|(label, e)| format!("{label}: {e}"))
            .collect::<Vec<_>>()
            .join("; ");
        write!(f, "{{ {record_rendering} }}")
    }
}

impl<A, Id> fmt::Display for Tuple<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tuple_rendering = self
            .elements
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "({tuple_rendering})")
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(x) => write!(f, "{x}"),
            Self::Float(x) => write!(f, "{x:?}"),
            Self::Text(x) => write!(f, "{x}"),
            Self::Bool(x) => write!(f, "{x}"),
            Self::Unit => write!(f, "()"),
            Self::Char(x) => write!(f, "{x}"),
        }
    }
}

impl<A> fmt::Display for CompilationUnit<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.root_module)
    }
}

impl<A> fmt::Display for UseDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            qualified_binder,
            path,
            _phase,
        } = self;
        write!(f, "{path}")?;
        if let Some(qualifier) = qualified_binder {
            write!(f, " at {qualifier}")?;
        }

        Ok(())
    }
}

impl<A> fmt::Display for Declaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(_, decl) => write!(f, "value {decl}"),
            Self::Module(_, decl) => write!(f, "module {decl}"),
            Self::Type(_, decl) => write!(f, "type {decl}"),
            Self::Use(_, decl) => write!(f, "use {decl}"),
            Self::Signature(_, decl) => write!(f, "constraint {decl}"),
            Self::Witness(_, decl) => write!(f, "witness {decl}"),
            Self::Foreign(_, decl) => write!(f, "foreign {}::{}", decl.name, decl.type_signature),
        }
    }
}

impl<A> fmt::Display for SignatureDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            type_parameters,
            constraints,
            declarator,
        } = self;

        write!(f, "∀{}. {name} ::= ", display_list(" ", type_parameters))?;
        if !constraints.is_empty() {
            write!(f, "{} |- ", display_list(" + ", constraints))?;
        }
        write!(f, "{declarator}")
    }
}

impl<A> fmt::Display for IdentifierPattern<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(p) = self;
        write!(f, "{p}")
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { name, kind } = self;
        write!(f, "{name}:{kind}")
    }
}

impl<A> fmt::Display for WitnessDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            type_signature,
            implementation: body,
        } = self;

        write!(f, "witness :: {type_signature} ::= {body}")
    }
}

impl<A> fmt::Display for ValueDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { name, declarator } = self;
        write!(f, "{name} is {declarator}")
    }
}

impl<A> fmt::Display for ValueDeclarator<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            type_signature,
            body,
        } = self;
        write!(f, "{body}")?;
        if let Some(ts) = type_signature {
            write!(f, ":: {ts}")?;
        }

        Ok(())
    }
}

impl<A> fmt::Display for ModuleDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { name, declarator } = self;
        write!(f, "module {name}:")?;
        write!(f, "{declarator}")
    }
}

impl<A> fmt::Display for ModuleDeclarator<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inline(declarations) => {
                for m in declarations {
                    writeln!(f, "{m}")?
                }
            }

            Self::External(identifier) => write!(f, "external module {identifier}")?,
        };

        Ok(())
    }
}

impl<A> fmt::Display for TypeDeclaration<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            type_parameters,
            declarator,
            origin,
            opaque,
            confinement,
        } = self;
        if let Some(confinement) = confinement {
            match confinement {
                ConfinementModifier::Confined => write!(f, "confined ")?,
                ConfinementModifier::Unconfined => write!(f, "unconfined ")?,
            }
        }
        if matches!(origin, TypeOrigin::Foreign) {
            return write!(f, "foreign {name}");
        }
        if *opaque {
            write!(f, "opaque ")?;
        }
        write!(f, "{name} ::= ")?;
        if !type_parameters.is_empty() {
            write!(f, "forall")?;
            for p in type_parameters {
                write!(f, " {p}")?;
            }
            write!(f, ".")?;
        }
        write!(f, "{declarator}")
    }
}

impl<A> fmt::Display for TypeDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Record(_, decl) => write!(f, "{decl}"),
            Self::Coproduct(_, decl) => write!(f, "{decl}"),
            Self::Alias(_, body) => write!(f, "{body}"),
        }
    }
}

impl<A> fmt::Display for RecordDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for field in &self.fields {
            writeln!(f, "{field}")?;
        }
        Ok(())
    }
}

impl<A> fmt::Display for CoproductDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut constructors = self.constructors.iter();

        if let Some(constructor) = constructors.next() {
            write!(f, "{}", constructor)?;

            for c in constructors {
                write!(f, " | {c}")?;
            }
        }

        Ok(())
    }
}

impl<A> fmt::Display for CoproductConstructor<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        let mut signature = self.signature.iter();

        if let Some(ty_expr) = signature.next() {
            write!(f, "({ty_expr})")?;

            for ty_expr in signature {
                write!(f, " ({ty_expr})")?;
            }
        }

        Ok(())
    }
}

impl<A> fmt::Display for FieldDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            type_signature,
        } = self;
        write!(f, "{name} :: {type_signature}")
    }
}

impl<A, TypeId> fmt::Display for TypeSignature<A, TypeId>
where
    TypeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            universal_quantifiers,
            body,
            constraints,
            ..
        } = self;
        if !universal_quantifiers.is_empty() {
            write!(f, "forall")?;
            for q in universal_quantifiers {
                write!(f, " {q}")?;
            }
            write!(f, ". ")?;
        }

        if !constraints.is_empty() {
            write!(f, "{} |- ", display_list(" + ", constraints))?;
        }

        write!(f, "{body}")?;

        Ok(())
    }
}

impl<A, TypeId> fmt::Display for ConstraintExpression<A, TypeId>
where
    TypeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            class, parameters, ..
        } = self;

        write!(f, "{class}")?;

        if !parameters.is_empty() {
            write!(f, " {}", display_list(" ", parameters))?;
        }

        Ok(())
    }
}

impl<A, TypeId> fmt::Display for TypeExpression<A, TypeId>
where
    TypeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constructor(_, name) => write!(f, "{name}"),

            Self::Parameter(_, name) => write!(f, "{name}"),

            Self::Apply(
                _,
                ApplyTypeExpr {
                    function, argument, ..
                },
            ) => write!(f, "({function} {argument})"),

            Self::ConfinementAscription(_, body, confinement) => {
                write!(f, "({body}) : {confinement}")
            }

            Self::Arrow(
                _,
                ArrowTypeExpr {
                    domain, codomain, ..
                },
            ) => {
                write!(f, "({domain} -> {codomain})")
            }

            Self::Tuple(_, TupleTypeExpr(elements)) => {
                let body = elements
                    .iter()
                    .map(|elt| elt.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({body})")
            }
        }
    }
}
