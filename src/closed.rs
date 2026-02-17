use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{
        self,
        annotation::Annotated,
        namer::{self, QualifiedName},
    },
    typer::{self, TypeInfo},
};

pub type Expr = ast::Expr<CaptureInfo, Identifier>;
pub type SelfReferential = ast::SelfReferential<CaptureInfo, Identifier>;
pub type Lambda = ast::Lambda<CaptureInfo, Identifier>;
pub type Apply = ast::Apply<CaptureInfo, Identifier>;
pub type Binding = ast::Binding<CaptureInfo, Identifier>;
pub type Tuple = ast::Tuple<CaptureInfo, Identifier>;
pub type Record = ast::Record<CaptureInfo, Identifier>;
pub type Injection = ast::Injection<CaptureInfo, Identifier>;
pub type Projection = ast::Projection<CaptureInfo, Identifier>;
pub type Sequence = ast::Sequence<CaptureInfo, Identifier>;
pub type MatchClause = ast::pattern::MatchClause<CaptureInfo, Identifier>;
pub type Deconstruct = ast::Deconstruct<CaptureInfo, Identifier>;
pub type IfThenElse = ast::IfThenElse<CaptureInfo, Identifier>;
pub type Interpolate = ast::Interpolate<CaptureInfo, Identifier>;
pub type Segment = ast::Segment<CaptureInfo, Identifier>;
pub type TypeAscription = ast::TypeAscription<CaptureInfo, Identifier>;
pub type Pattern = ast::pattern::Pattern<CaptureInfo, Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<CaptureInfo, Identifier>;
pub type TuplePattern = ast::pattern::TuplePattern<CaptureInfo, Identifier>;
pub type StructPattern = ast::pattern::StructPattern<CaptureInfo, Identifier>;
type Tree<Id> = ast::Tree<CaptureInfo, Id>;

pub enum Identifier {
    Local(LexicalLevel),
    Captured(CaptureIndex),
    Global(Box<QualifiedName>),
}

#[derive(Debug, Default)]
struct CaptureLayout {
    by_level: HashMap<LexicalLevel, CaptureIndex>,
    by_index: Vec<LexicalLevel>,
    next: CaptureIndex,
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
struct LexicalLevel(usize);

impl LexicalLevel {
    fn rebase(self, scope: Self) -> Self {
        assert!(self.0 >= scope.0);
        Self(self.0 - scope.0)
    }

    fn is_outside_of(&self, scope: &LexicalLevel) -> bool {
        self.0 < scope.0
    }
}

#[derive(Copy, Clone, Debug, Default)]
struct CaptureIndex(usize);

impl CaptureIndex {
    fn update(&mut self) {
        self.0 += 1;
    }
}

impl CaptureLayout {
    fn resolve(&mut self, scope: LexicalLevel, level: LexicalLevel) -> Identifier {
        if level.is_outside_of(&scope) {
            let index = self.by_level.get(&level).copied().unwrap_or_else(|| {
                let slot = self.next;
                self.by_level.insert(level, slot);
                self.by_index.push(level);
                self.next.update();
                slot
            });
            Identifier::Captured(index)
        } else {
            Identifier::Local(level.rebase(scope))
        }
    }
}

#[derive(Debug)]
struct CaptureInfo {
    type_info: TypeInfo,
    layout: Option<CaptureLayout>,
}

impl TypeInfo {
    fn empty_capture(self) -> CaptureInfo {
        CaptureInfo {
            type_info: self,
            layout: None,
        }
    }

    fn with_capture_layout(self, layout: CaptureLayout) -> CaptureInfo {
        CaptureInfo {
            type_info: self,
            layout: Some(layout),
        }
    }
}

impl typer::Pattern {
    fn rewrite_tree(self, lambda_level: LexicalLevel, capture_map: &mut CaptureLayout) -> Pattern {
        match self {
            ast::pattern::Pattern::Coproduct(
                ti,
                ast::pattern::ConstructorPattern {
                    constructor: namer::Identifier::Free(name),
                    arguments,
                },
            ) => Pattern::Coproduct(
                ti.empty_capture(),
                ConstructorPattern {
                    constructor: Identifier::Global(name),
                    arguments: arguments
                        .into_iter()
                        .map(|e| e.rewrite_tree(lambda_level, capture_map))
                        .collect(),
                },
            ),

            ast::pattern::Pattern::Tuple(ti, the) => Pattern::Tuple(
                ti.empty_capture(),
                TuplePattern {
                    elements: the
                        .elements
                        .into_iter()
                        .map(|e| e.rewrite_tree(lambda_level, capture_map))
                        .collect(),
                },
            ),

            ast::pattern::Pattern::Struct(ti, the) => Pattern::Struct(
                ti.empty_capture(),
                StructPattern {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| (label, e.rewrite_tree(lambda_level, capture_map)))
                        .collect(),
                },
            ),

            ast::pattern::Pattern::Literally(ti, the) => {
                Pattern::Literally(ti.empty_capture(), the)
            }

            ast::pattern::Pattern::Bind(ti, namer::Identifier::Bound(binding_level)) => {
                Pattern::Bind(
                    ti.empty_capture(),
                    Identifier::Local(LexicalLevel(binding_level).rebase(lambda_level)),
                )
            }

            otherwise => panic!("illegal AST {otherwise:?}"),
        }
    }
}

impl typer::Expr {
    pub fn closure_conversion(self) -> Expr {
        self.rewrite_tree(LexicalLevel(0), &mut CaptureLayout::default())
    }

    fn go(
        tree: ast::Tree<TypeInfo, namer::Identifier>,
        lambda_level: LexicalLevel,
        capture_map: &mut CaptureLayout,
    ) -> Tree<Identifier> {
        let owned = Rc::unwrap_or_clone(tree);
        Rc::new(owned.rewrite_tree(lambda_level, capture_map))
    }

    fn rewrite_tree(self, lambda_level: LexicalLevel, layout: &mut CaptureLayout) -> Expr {
        match self {
            Self::Variable(ti, namer::Identifier::Bound(level)) => Expr::Variable(
                ti.empty_capture(),
                layout.resolve(lambda_level, LexicalLevel(level)),
            ),

            Self::Variable(ti, namer::Identifier::Free(name)) => {
                Expr::Variable(ti.empty_capture(), Identifier::Global(name))
            }

            Self::InvokeBridge(ti, the) => Expr::InvokeBridge(ti.empty_capture(), the),

            Self::Constant(ti, the) => Expr::Constant(ti.empty_capture(), the),

            Self::RecursiveLambda(
                ti,
                typer::SelfReferential {
                    own_name: namer::Identifier::Bound(own_name),
                    lambda,
                },
            ) => {
                let mut layout = CaptureLayout::default();
                let lambda = Lambda {
                    parameter: Identifier::Local(LexicalLevel(1)),
                    body: Self::go(lambda.body, LexicalLevel(own_name), &mut layout).into(),
                };

                Expr::RecursiveLambda(
                    ti.with_capture_layout(layout),
                    SelfReferential {
                        own_name: Identifier::Local(LexicalLevel(0)),
                        lambda,
                    },
                )
            }

            Self::Lambda(
                ti,
                typer::Lambda {
                    parameter: namer::Identifier::Bound(param_level),
                    body,
                },
            ) => {
                let mut layout = CaptureLayout::default();
                let lambda = Lambda {
                    parameter: Identifier::Local(LexicalLevel(0)),
                    body: Self::go(body, LexicalLevel(param_level), &mut layout),
                };
                Expr::Lambda(ti.with_capture_layout(layout), lambda)
            }

            Self::Apply(ti, the) => Expr::Apply(
                ti.empty_capture(),
                Apply {
                    function: Self::go(the.function, lambda_level, layout),
                    argument: Self::go(the.argument, lambda_level, layout),
                },
            ),

            Self::Let(
                ti,
                ast::Binding {
                    binder: namer::Identifier::Bound(binder_level),
                    bound,
                    body,
                },
            ) => Expr::Let(
                ti.empty_capture(),
                Binding {
                    binder: Identifier::Local(LexicalLevel(binder_level).rebase(lambda_level)),
                    bound: Self::go(bound, lambda_level, layout),
                    body: Self::go(body, lambda_level, layout),
                },
            ),

            Self::Tuple(ti, the) => Expr::Tuple(
                ti.empty_capture(),
                Tuple {
                    elements: the
                        .elements
                        .into_iter()
                        .map(|e| Self::go(e, lambda_level, layout))
                        .collect(),
                },
            ),

            Self::Record(ti, the) => Expr::Record(
                ti.empty_capture(),
                Record {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| (label, Self::go(e, lambda_level, layout)))
                        .collect(),
                },
            ),

            Self::Inject(ti, the) => Expr::Inject(
                ti.empty_capture(),
                Injection {
                    constructor: the.constructor,
                    arguments: the
                        .arguments
                        .into_iter()
                        .map(|e| Self::go(e, lambda_level, layout))
                        .collect(),
                },
            ),

            Self::Project(ti, the) => Expr::Project(
                ti.empty_capture(),
                Projection {
                    base: Self::go(the.base, lambda_level, layout),
                    select: the.select,
                },
            ),

            Self::Sequence(ti, the) => Expr::Sequence(
                ti.empty_capture(),
                Sequence {
                    this: Self::go(the.this, lambda_level, layout),
                    and_then: Self::go(the.and_then, lambda_level, layout),
                },
            ),

            Self::Deconstruct(ti, the) => Expr::Deconstruct(
                ti.empty_capture(),
                Deconstruct {
                    scrutinee: Self::go(the.scrutinee, lambda_level, layout),
                    match_clauses: the
                        .match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern.rewrite_tree(lambda_level, layout),
                            consequent: Self::go(clause.consequent, lambda_level, layout),
                        })
                        .collect(),
                },
            ),

            Self::If(ti, the) => Expr::If(
                ti.empty_capture(),
                IfThenElse {
                    predicate: Self::go(the.predicate, lambda_level, layout),
                    consequent: Self::go(the.consequent, lambda_level, layout),
                    alternate: Self::go(the.alternate, lambda_level, layout),
                },
            ),

            Self::Interpolate(ti, ast::Interpolate(segments)) => Expr::Interpolate(
                ti.empty_capture(),
                ast::Interpolate(
                    segments
                        .into_iter()
                        .map(|s| match s {
                            ast::Segment::Literal(ti, literal) => {
                                Segment::Literal(ti.empty_capture(), literal)
                            }
                            ast::Segment::Expression(expr) => {
                                Segment::Expression(Self::go(expr, lambda_level, layout))
                            }
                        })
                        .collect(),
                ),
            ),

            Self::Ascription(ti, the) => Expr::Ascription(
                ti.empty_capture(),
                TypeAscription {
                    ascribed_tree: Self::go(the.ascribed_tree, lambda_level, layout),
                    type_signature: the
                        .type_signature
                        .map_annotation(&|ti| ti.clone().empty_capture()),
                },
            ),

            otherwise => panic!("Bad medicin {otherwise:?}"),
        }
    }
}
