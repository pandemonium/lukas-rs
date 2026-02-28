use crate::{
    parser::{IdentifierPath, ParseInfo, Parsed},
    phase,
};

pub struct Desugared;

impl phase::Phase for Desugared {
    type Annotation = ParseInfo;
    type TermId = IdentifierPath;
    type TypeId = IdentifierPath;
}

type Expr = phase::Expr<Desugared>;

impl phase::Expr<Parsed> {
    pub fn desugar(&self) -> Expr {
        todo!()
    }
}
