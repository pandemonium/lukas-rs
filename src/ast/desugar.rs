use std::{
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::{
        self, Apply, Binding, Deconstruct, IdentifierPattern, IfThenElse, Injection, Interpolate,
        Lambda, Projection, Record, SelfReferential, Sequence, Tree, Tuple, TypeAscription,
        namer::{Symbol, SymbolTable, TermSymbol},
        pattern::MatchClause,
    },
    lexer::BindingOperator,
    parser::{IdentifierPath, ParseInfo, Parsed},
    phase::{self, Phase},
};

pub struct Desugared;

impl phase::Phase for Desugared {
    type Annotation = ParseInfo;
    type TermId = IdentifierPath;
    type TypeId = IdentifierPath;
}

type Expr = phase::Expr<Desugared>;

static FRESH_NAME_ID: AtomicU32 = AtomicU32::new(0);

fn fresh_identifier_path() -> IdentifierPath {
    IdentifierPath::new(&format!(
        "pat_id_{}",
        FRESH_NAME_ID.fetch_add(1, Ordering::Relaxed)
    ))
}

impl phase::Expr<Parsed> {
    pub fn lower_binding_operators(self) -> phase::Expr<Parsed> {
        self.map(&mut |e| match e {
            ast::Expr::Let(a, binding) => match binding.operator {
                BindingOperator::Identity => ast::Expr::Let(a, binding),
                BindingOperator::Monadic => {
                    /* let* x = foo in bar x
                     *
                     * bind (lambda x. bar x) foo
                     *
                     */
                    let lambda = ast::Expr::Lambda(
                        a,
                        Lambda {
                            parameter: binding.binder,
                            body: binding.body,
                        },
                    );
                    let apply = ast::Expr::Apply(
                        a,
                        Apply {
                            function: ast::Expr::Variable(
                                a,
                                IdentifierPattern::from_atom(a, "bind"),
                            )
                            .into(),
                            argument: lambda.into(),
                        },
                    );
                    ast::Expr::Apply(
                        a,
                        Apply {
                            function: apply.into(),
                            argument: binding.bound,
                        },
                    )
                }
                BindingOperator::Applicative => {
                    /* let+ x = foo in bar x
                     *
                     * map (lambda x. bar x) foo
                     *
                     */
                    let lambda = ast::Expr::Lambda(
                        a,
                        Lambda {
                            parameter: binding.binder,
                            body: binding.body,
                        },
                    );
                    let apply = ast::Expr::Apply(
                        a,
                        Apply {
                            function: ast::Expr::Variable(
                                a,
                                IdentifierPattern::from_atom(a, "fmap"),
                            )
                            .into(),
                            argument: lambda.into(),
                        },
                    );
                    ast::Expr::Apply(
                        a,
                        Apply {
                            function: apply.into(),
                            argument: binding.bound,
                        },
                    )
                }
            },
            otherwise => otherwise,
        })
    }

    fn recurse(
        tree: Tree<ParseInfo, <Parsed as Phase>::TermId>,
    ) -> Tree<ParseInfo, <Desugared as Phase>::TermId> {
        let owned = Rc::unwrap_or_clone(tree);
        Rc::new(owned.lower_inline_patterns())
    }

    // It cannot be map because it changes the Id type and map
    // does not have that capability at this point.
    pub fn lower_inline_patterns(self) -> phase::Expr<Desugared> {
        match self {
            ast::Expr::Variable(a, the) => Expr::Variable(
                a,
                the.try_into_simple_bind()
                    .expect("pattern in eliminator position"),
            ),
            ast::Expr::InvokeBridge(a, the) => ast::Expr::InvokeBridge(a, the),
            ast::Expr::Constant(a, the) => ast::Expr::Constant(a, the),
            ast::Expr::RecursiveLambda(a, the) => Expr::RecursiveLambda(
                a,
                SelfReferential {
                    own_name: the
                        .own_name
                        .try_into_simple_bind()
                        .expect("pattern in eliminator position"),
                    lambda: if !the.lambda.parameter.is_simple_bind() {
                        Self::insert_deconstruction_shim(a, the.lambda)
                    } else {
                        Lambda {
                            parameter: the.lambda.parameter.try_into_simple_bind().unwrap(),
                            body: Self::recurse(the.lambda.body),
                        }
                    },
                },
            ),
            ast::Expr::Lambda(a, the) => Expr::Lambda(
                a,
                if !the.parameter.is_simple_bind() {
                    Self::insert_deconstruction_shim(a, the)
                } else {
                    Lambda {
                        parameter: the.parameter.try_into_simple_bind().unwrap(),
                        body: Self::recurse(the.body),
                    }
                },
            ),
            ast::Expr::Apply(a, the) => Expr::Apply(
                a,
                Apply {
                    function: Self::recurse(the.function),
                    argument: Self::recurse(the.argument),
                },
            ),
            ast::Expr::Let(a, the) => {
                if !the.binder.is_simple_bind() {
                    Expr::Deconstruct(
                        a,
                        Deconstruct {
                            scrutinee: Self::recurse(the.bound),
                            match_clauses: vec![MatchClause {
                                pattern: the.binder.into_pattern(),
                                consequent: Self::recurse(the.body),
                            }],
                        },
                    )
                } else {
                    Expr::Let(
                        a,
                        Binding {
                            binder: the.binder.try_into_simple_bind().unwrap(),
                            operator: the.operator,
                            bound: Self::recurse(the.bound),
                            body: Self::recurse(the.body),
                        },
                    )
                }
            }
            ast::Expr::Tuple(a, the) => Expr::Tuple(
                a,
                Tuple {
                    elements: the.elements.into_iter().map(Self::recurse).collect(),
                },
            ),
            ast::Expr::Record(a, the) => Expr::Record(
                a,
                Record {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| (label, Self::recurse(e)))
                        .collect(),
                },
            ),
            ast::Expr::Inject(a, the) => Expr::Inject(
                a,
                Injection {
                    constructor: the.constructor,
                    arguments: the.arguments.into_iter().map(Self::recurse).collect(),
                },
            ),
            ast::Expr::Project(a, the) => Expr::Project(
                a,
                Projection {
                    base: Self::recurse(the.base),
                    select: the.select,
                },
            ),
            ast::Expr::Sequence(a, the) => Expr::Sequence(
                a,
                Sequence {
                    this: Self::recurse(the.this),
                    and_then: Self::recurse(the.and_then),
                },
            ),
            ast::Expr::Deconstruct(a, the) => Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee: Self::recurse(the.scrutinee),
                    match_clauses: the
                        .match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern.map_id(&|id| {
                                id.try_into_simple_bind()
                                    .expect("pattern in eliminator position")
                            }),
                            consequent: Self::recurse(clause.consequent),
                        })
                        .collect(),
                },
            ),
            ast::Expr::If(a, the) => Expr::If(
                a,
                IfThenElse {
                    predicate: Self::recurse(the.predicate),
                    consequent: Self::recurse(the.consequent),
                    alternate: Self::recurse(the.alternate),
                },
            ),
            ast::Expr::Interpolate(a, the) => Expr::Interpolate(
                a,
                Interpolate(
                    the.0
                        .into_iter()
                        .map(|s| match s {
                            ast::Segment::Expression(expr) => {
                                ast::Segment::Expression(Self::recurse(expr))
                            }
                            ast::Segment::Literal(a, literal) => ast::Segment::Literal(a, literal),
                        })
                        .collect(),
                ),
            ),
            ast::Expr::Ascription(a, the) => Expr::Ascription(
                a,
                TypeAscription {
                    ascribed_tree: Self::recurse(the.ascribed_tree),
                    type_signature: the.type_signature,
                },
            ),
            ast::Expr::MakeClosure(..) => panic!("illegal AST form"),
        }
    }

    pub fn desugar(&self) -> Expr {
        self.clone()
            .lower_binding_operators()
            .lower_inline_patterns()
    }

    fn insert_deconstruction_shim(
        a: ParseInfo,
        the: Lambda<ParseInfo, ast::IdentifierPattern<ParseInfo>>,
    ) -> Lambda<ParseInfo, IdentifierPath> {
        tracing::trace!("lower_inline_patterns: lowering!");
        let binder = fresh_identifier_path();
        Lambda {
            parameter: binder.clone(),
            // Only do this stuff when there is an actual pattern match
            body: Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee: Expr::Variable(a, binder).into(),
                    match_clauses: vec![MatchClause {
                        pattern: the.parameter.into_pattern(),
                        consequent: Self::recurse(the.body),
                    }],
                },
            )
            .into(),
        }
    }
}

impl phase::SymbolTable<Parsed> {
    // Can't I just rewrite the whole table like with resolve_names?
    // This way I could probably remove the annoying TermSymbol::body
    pub fn desugar_expressions(&self) -> phase::SymbolTable<Desugared> {
        SymbolTable {
            module_members: self.module_members.clone(),
            member_modules: self.member_modules.clone(),
            symbols: self
                .symbols
                .iter()
                .map(|(name, symbol)| {
                    (
                        name.clone(),
                        match symbol {
                            Symbol::Term(symbol) => Symbol::Term(TermSymbol {
                                name: symbol.name.clone(),
                                type_signature: symbol.type_signature.clone(),
                                body: symbol.body.desugar().into(),
                            }),
                            Symbol::Type(symbol) => Symbol::Type(symbol.clone()),
                        },
                    )
                })
                .collect(),
            imports: self.imports.clone(),
            foreign_terms: self.foreign_terms.clone(),
            signatures: self.signatures.clone(),
            witnesses: self.witnesses.clone(),
            constructor_opacity: self.constructor_opacity.clone(),
            member_visibility: self.member_visibility.clone(),
        }
    }

    pub fn desugar(&self) -> phase::SymbolTable<Desugared> {
        tracing::debug!("desugar: running");
        self.desugar_expressions()
    }
}
