// Think about this module and where it lives. Maybe in compiler.rs or phase.rs or something?

use crate::ast;

pub trait Phase {
    type Annotation;
    type TermId;
    type TypeId;
}

pub type Expr<P> = ast::Expr<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type SelfReferential<P> = ast::SelfReferential<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Lambda<P> = ast::Lambda<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Apply<P> = ast::Apply<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Binding<P> = ast::Binding<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Record<P> = ast::Record<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Tuple<P> = ast::Tuple<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Projection<P> = ast::Projection<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Injection<P> = ast::Injection<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Sequence<P> = ast::Sequence<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Deconstruct<P> = ast::Deconstruct<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type IfThenElse<P> = ast::IfThenElse<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Interpolate<P> = ast::Interpolate<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type TypeAscription<P> = ast::TypeAscription<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type RecordDeclarator<P> = ast::RecordDeclarator<<P as Phase>::Annotation>;
pub type CoproductDeclarator<P> = ast::CoproductDeclarator<<P as Phase>::Annotation>;

pub type Segment<P> = ast::Segment<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type Pattern<P> = ast::pattern::Pattern<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type MatchClause<P> = ast::pattern::MatchClause<<P as Phase>::Annotation, <P as Phase>::TermId>;

pub type ConstructorPattern<P> =
    ast::pattern::ConstructorPattern<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type TuplePattern<P> =
    ast::pattern::TuplePattern<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type StructPattern<P> =
    ast::pattern::StructPattern<<P as Phase>::Annotation, <P as Phase>::TermId>;
pub type TypeExpression<P> = ast::TypeExpression<<P as Phase>::Annotation, <P as Phase>::TypeId>;
pub type TypeSignature<P> = ast::TypeSignature<<P as Phase>::Annotation, <P as Phase>::TypeId>;

pub type ConstraintExpression<P> =
    ast::ConstraintExpression<<P as Phase>::Annotation, <P as Phase>::TypeId>;
