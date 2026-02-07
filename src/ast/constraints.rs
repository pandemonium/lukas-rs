use std::collections::HashMap;

use crate::{
    ast::namer::QualifiedName,
    typer::{self, Constraint, RecordShape, Type, TypeEnvironment, TypeError},
};

pub struct ConstraintSignature {
    pub name: QualifiedName,
    pub shape: RecordShape,
}

impl Constraint {
    pub fn signature(&self, env: &TypeEnvironment) -> Result<ConstraintSignature, TypeError> {
        let type_constructor = env
            .lookup(&self.name())
            .ok_or_else(|| TypeError::UndefinedSignature(self.name().clone()))?;

        if let Type::Record(record) = type_constructor.structure().map_err(|e| e.error)? {
            Ok(ConstraintSignature {
                name: self.name().clone(),
                shape: record.shape(),
            })
        } else {
            Err(TypeError::InternalAssertion("expected a record".to_owned()))
        }
    }
}

#[derive(Debug)]
pub struct Witness {
    // Perhaps this should have the instantiated type? I mean: why not?
    pub ty: Type,
    pub dictionary: typer::Expr,
}

#[derive(Debug, Default)]
pub struct WitnessIndex {
    store: HashMap<Type, Witness>,
}

impl WitnessIndex {
    // This has to change with premises
    pub fn insert(&mut self, witness: Witness) {
        self.store.insert(witness.ty.clone(), witness);
    }

    pub fn witness(&self, constraint: &Constraint) -> Option<&Witness> {
        self.store.get(&constraint.constraint_type)
    }
}
