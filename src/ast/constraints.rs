use std::collections::HashMap;

use crate::{
    ast::namer::TypeSignature,
    typer::{self, Constraint},
};

#[derive(Debug)]
pub struct Witness {
    pub signature: TypeSignature,
    pub dictionary: typer::Expr,
}

pub struct WitnessIndex {
    store: HashMap<String, Vec<Witness>>,
}

impl WitnessIndex {
    // This has to change with premises
    pub fn insert(&mut self, signature: TypeSignature, implementation: typer::Expr) {}

    pub fn find_witness(&self, constraint: &Constraint) -> Option<&Witness> {
        todo!()
    }
}
