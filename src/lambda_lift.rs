use std::fmt;

use crate::{
    ast::namer::QualifiedName,
    closed::{CaptureIndex, CaptureLayout, Expr, Tuple},
    typer,
};

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub environment: Tuple,
    pub lifted_name: QualifiedName,
}

#[derive(Debug, Clone)]
pub struct Program {
    functions: Vec<LiftedFunction>,
    start: Expr,
}

#[derive(Debug, Clone)]
pub struct LiftedFunction {
    name: QualifiedName,
    code: Expr,
    layout: CaptureLayout,
    own_name_slot: Option<CaptureIndex>,
}

impl fmt::Display for ClosureInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}
