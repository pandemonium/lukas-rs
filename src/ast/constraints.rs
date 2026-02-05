use std::collections::HashMap;

use crate::{
    ast::namer::{QualifiedName, TypeSignature},
    parser,
    typer::{self, Constraint, Type, TypeEnvironment, TypeError},
};

pub struct ConstraintSignature {
    pub name: QualifiedName,
    pub methods: Vec<parser::Identifier>,
}

impl Constraint {
    pub fn signature(&self, env: &TypeEnvironment) -> Result<ConstraintSignature, TypeError> {
        let type_constructor = env
            .lookup(&self.class)
            .ok_or_else(|| TypeError::UndefinedSignature(self.class.clone()))?;

        if let Type::Record(record) = type_constructor.structure().map_err(|e| e.error)? {
            Ok(ConstraintSignature {
                name: self.class.clone(),
                methods: record.shape().fields().to_vec(),
            })
        } else {
            Err(TypeError::InternalAssertion("expected a record".to_owned()))
        }
    }
}

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
