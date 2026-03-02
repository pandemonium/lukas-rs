use std::{collections::HashMap, fmt, rc::Rc};

use crate::{
    ast::{
        self, Apply, Binding, Deconstruct, IfThenElse, Injection, Lambda, Projection, Record,
        Segment, SelfReferential, Sequence, Tuple, TypeAscription,
        annotation::Annotated,
        namer::{self, QualifiedName, Symbol, TermSymbol},
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    parser::ParseInfo,
    phase,
    typer::{Type, TypeInfo, Types},
};

pub struct Closed;

impl phase::Phase for Closed {
    type Annotation = CaptureInfo;
    type TermId = Identifier;
    type TypeId = QualifiedName;
}

pub type SymbolTable = namer::SymbolTable<CaptureInfo, QualifiedName, Identifier>;

pub type Expr = ast::Expr<CaptureInfo, Identifier>;
type Tree<Id> = ast::Tree<CaptureInfo, Id>;

impl phase::SymbolTable<Types> {
    pub fn closure_conversion(self) -> phase::SymbolTable<Closed> {
        let mut symbols = HashMap::with_capacity(self.symbols.len());

        for t in self.symbols {
            let (name, symbol) = match t {
                (name, Symbol::Type(symbol)) => (name, Symbol::Type(symbol)),
                (name, Symbol::Term(symbol)) => {
                    let closed = symbol.body.close_closures();
                    let closed = TermSymbol {
                        name: symbol.name,
                        body: closed,
                        type_signature: symbol.type_signature,
                    };
                    (name, Symbol::Term(closed))
                }
            };
            symbols.insert(name, symbol);
        }

        SymbolTable {
            symbols,
            module_members: self.module_members,
            member_modules: self.member_modules,
            imports: self.imports,
            signatures: self.signatures,
            witnesses: self.witnesses,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Identifier {
    Local(LexicalLevel),
    Captured(CaptureIndex),
    Global(Box<QualifiedName>),
}

#[derive(Debug, Clone, Default)]
pub struct CaptureLayout {
    by_level: HashMap<LexicalLevel, CaptureIndex>,
    by_index: Vec<LexicalLevel>,
    next: CaptureIndex,
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub struct LexicalLevel(pub usize);

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
pub struct CaptureIndex(usize);

impl CaptureIndex {
    pub fn index(&self) -> usize {
        self.0
    }

    fn update(&mut self) {
        self.0 += 1;
    }
}

impl CaptureLayout {
    fn next_capture_index(&mut self) -> CaptureIndex {
        let slot = self.next;
        self.next.update();
        slot
    }

    fn resolve(&mut self, scope: LexicalLevel, level: LexicalLevel) -> Identifier {
        if level.is_outside_of(&scope) {
            let index = self.by_level.get(&level).copied().unwrap_or_else(|| {
                let slot = self.next_capture_index();
                self.by_level.insert(level, slot);
                self.by_index.push(level);
                slot
            });
            Identifier::Captured(index)
        } else {
            Identifier::Local(level.rebase(scope))
        }
    }
}

#[derive(Debug, Clone)]
pub struct CaptureInfo {
    pub type_info: TypeInfo,
    pub layout: Option<CaptureLayout>,
}

impl CaptureInfo {
    pub fn dummy() -> Self {
        ParseInfo::default()
            .with_inferred_type(Type::fresh())
            .empty_capture()
    }

    pub fn make_environment_tuple(&self) -> Expr {
        let ci = Self::dummy();
        Expr::Tuple(
            ci.clone(),
            Tuple {
                elements: if let Some(captures) = &self.layout {
                    captures
                        .by_index
                        .iter()
                        .map(|level| Expr::Variable(ci.clone(), Identifier::Local(*level)).into())
                        .collect()
                } else {
                    vec![]
                },
            },
        )
    }
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

impl phase::Pattern<Types> {
    fn rewrite_tree(
        self,
        lambda_level: LexicalLevel,
        is_recursive: bool,
        capture_map: &mut CaptureLayout,
    ) -> phase::Pattern<Closed> {
        match self {
            Pattern::Coproduct(
                ti,
                ConstructorPattern {
                    constructor: namer::Identifier::Free(name),
                    arguments,
                },
            ) => Pattern::Coproduct(
                ti.empty_capture(),
                ConstructorPattern {
                    constructor: Identifier::Global(name),
                    arguments: arguments
                        .into_iter()
                        .map(|e| e.rewrite_tree(lambda_level, is_recursive, capture_map))
                        .collect(),
                },
            ),

            Pattern::Tuple(ti, the) => Pattern::Tuple(
                ti.empty_capture(),
                TuplePattern {
                    elements: the
                        .elements
                        .into_iter()
                        .map(|e| e.rewrite_tree(lambda_level, is_recursive, capture_map))
                        .collect(),
                },
            ),

            Pattern::Struct(ti, the) => Pattern::Struct(
                ti.empty_capture(),
                StructPattern {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| {
                            (
                                label,
                                e.rewrite_tree(lambda_level, is_recursive, capture_map),
                            )
                        })
                        .collect(),
                },
            ),

            Pattern::Literally(ti, the) => Pattern::Literally(ti.empty_capture(), the),

            Pattern::Bind(ti, namer::Identifier::Bound(binding_level)) => Pattern::Bind(
                ti.empty_capture(),
                Identifier::Local(LexicalLevel(binding_level).rebase(lambda_level)),
            ),

            otherwise => panic!("illegal AST {otherwise:?}"),
        }
    }
}

impl phase::Expr<Types> {
    pub fn close_closures(self) -> Expr {
        // really: map self name to Global before closing the tree
        self.rewrite_tree(LexicalLevel(0), false, &mut CaptureLayout::default())
    }

    fn go(
        tree: ast::Tree<TypeInfo, namer::Identifier>,
        lambda_level: LexicalLevel,
        is_recursive: bool,
        capture_map: &mut CaptureLayout,
    ) -> Tree<Identifier> {
        let owned = Rc::unwrap_or_clone(tree);
        Rc::new(owned.rewrite_tree(lambda_level, is_recursive, capture_map))
    }

    fn rewrite_tree(
        self,
        lambda_level: LexicalLevel,
        is_recursive: bool,
        layout: &mut CaptureLayout,
    ) -> Expr {
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
                SelfReferential {
                    own_name: namer::Identifier::Bound(own_name),
                    lambda,
                },
            ) => {
                let mut layout = CaptureLayout::default();
                let lambda = Lambda {
                    parameter: Identifier::Local(LexicalLevel(1)),
                    body: Self::go(lambda.body, LexicalLevel(own_name), true, &mut layout).into(),
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
                Lambda {
                    parameter: namer::Identifier::Bound(param_level),
                    body,
                },
            ) => {
                let mut layout = CaptureLayout::default();
                let lambda = Lambda {
                    parameter: Identifier::Local(LexicalLevel(0)),
                    body: Self::go(body, LexicalLevel(param_level), false, &mut layout),
                };
                Expr::Lambda(ti.with_capture_layout(layout), lambda)
            }

            Self::Apply(ti, the) => Expr::Apply(
                ti.empty_capture(),
                Apply {
                    function: Self::go(the.function, lambda_level, is_recursive, layout),
                    argument: Self::go(the.argument, lambda_level, is_recursive, layout),
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
                    bound: Self::go(bound, lambda_level, is_recursive, layout),
                    body: Self::go(body, lambda_level, is_recursive, layout),
                },
            ),

            Self::Tuple(ti, the) => Expr::Tuple(
                ti.empty_capture(),
                Tuple {
                    elements: the
                        .elements
                        .into_iter()
                        .map(|e| Self::go(e, lambda_level, is_recursive, layout))
                        .collect(),
                },
            ),

            Self::Record(ti, the) => Expr::Record(
                ti.empty_capture(),
                Record {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(label, e)| (label, Self::go(e, lambda_level, is_recursive, layout)))
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
                        .map(|e| Self::go(e, lambda_level, is_recursive, layout))
                        .collect(),
                },
            ),

            Self::Project(ti, the) => Expr::Project(
                ti.empty_capture(),
                Projection {
                    base: Self::go(the.base, lambda_level, is_recursive, layout),
                    select: the.select,
                },
            ),

            Self::Sequence(ti, the) => Expr::Sequence(
                ti.empty_capture(),
                Sequence {
                    this: Self::go(the.this, lambda_level, is_recursive, layout),
                    and_then: Self::go(the.and_then, lambda_level, is_recursive, layout),
                },
            ),

            Self::Deconstruct(ti, the) => Expr::Deconstruct(
                ti.empty_capture(),
                Deconstruct {
                    scrutinee: Self::go(the.scrutinee, lambda_level, is_recursive, layout),
                    match_clauses: the
                        .match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern.rewrite_tree(
                                lambda_level,
                                is_recursive,
                                layout,
                            ),
                            consequent: Self::go(
                                clause.consequent,
                                lambda_level,
                                is_recursive,
                                layout,
                            ),
                        })
                        .collect(),
                },
            ),

            Self::If(ti, the) => Expr::If(
                ti.empty_capture(),
                IfThenElse {
                    predicate: Self::go(the.predicate, lambda_level, is_recursive, layout),
                    consequent: Self::go(the.consequent, lambda_level, is_recursive, layout),
                    alternate: Self::go(the.alternate, lambda_level, is_recursive, layout),
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
                            ast::Segment::Expression(expr) => Segment::Expression(Self::go(
                                expr,
                                lambda_level,
                                is_recursive,
                                layout,
                            )),
                        })
                        .collect(),
                ),
            ),

            Self::Ascription(ti, the) => Expr::Ascription(
                ti.empty_capture(),
                TypeAscription {
                    ascribed_tree: Self::go(the.ascribed_tree, lambda_level, is_recursive, layout),
                    type_signature: the
                        .type_signature
                        .map_annotation(&|ti| ti.clone().empty_capture()),
                },
            ),

            otherwise => panic!("Bad medicin {otherwise:?}"),
        }
    }
}

impl fmt::Display for CaptureInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { .. } = self;
        write!(f, "<<capture-info>>")
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(lexical_level) => write!(f, "Local({lexical_level})"),
            Self::Captured(capture_index) => write!(f, "Captured({capture_index})"),
            Self::Global(qualified_name) => write!(f, "Global({qualified_name})"),
        }
    }
}

impl fmt::Display for LexicalLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(level) = self;
        write!(f, "{level}")
    }
}

impl fmt::Display for CaptureIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(index) = self;
        write!(f, "{index}")
    }
}
