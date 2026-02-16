use std::collections::HashMap;

use crate::{
    ast::namer::{self, Identifier, QualifiedName},
    parser::ParseInfo,
    typer::{
        Apply, Constraint, Expr, RecordShape, Substitutions, Type, TypeEnvironment, TypeError,
        Typing, TypingContext,
    },
};

pub struct ConstraintSignature {
    pub name: QualifiedName,
    pub shape: RecordShape,
}

impl Constraint {
    pub fn signature(&self, env: &TypeEnvironment) -> Result<ConstraintSignature, TypeError> {
        let type_constructor = env
            .lookup(self.name())
            .ok_or_else(|| TypeError::UndefinedSignature(self.name().clone()))?;

        if let Type::Record(record) = type_constructor.structure().map_err(|e| *e.error)? {
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
    pub head: Constraint,
    pub premises: Vec<Constraint>,
    pub name: QualifiedName,
}

impl Witness {
    pub fn from_type_signature(
        name: QualifiedName,
        witness: namer::TypeSignature,
        ctx: &TypingContext,
    ) -> Typing<Self> {
        let witness_signature = witness.type_scheme(&mut HashMap::default(), ctx)?;
        let witness_type = witness_signature.instantiate();

        Ok(Self {
            head: Constraint::from_assumed_spine(witness_type.underlying),
            premises: witness_type.constraints.iter().cloned().collect(),
            name,
        })
    }

    pub fn apply(&self, subst: &Substitutions) -> Self {
        Self {
            head: self.head.apply(subst),
            premises: self.premises.iter().map(|c| c.apply(subst)).collect(),
            name: self.name.clone(),
        }
    }
}

#[derive(Debug, Default)]
pub struct WitnessIndex {
    store: HashMap<QualifiedName, Vec<Witness>>,
}

impl WitnessIndex {
    pub fn register(&mut self, witness: Witness) {
        self.store
            .entry(witness.head.name().clone())
            .or_default()
            .push(witness);
    }

    pub fn resolve_witness(&self, constraint: &Constraint) -> Result<Expr, TypeError> {
        //println!(
        //    "resolve_witness: {constraint} -- {}",
        //    display_list(
        //        ", ",
        //        &self
        //            .store
        //            .iter()
        //            .map(|(p, q)| format!("{p} -> {q:?}"))
        //            .collect::<Vec<_>>()
        //    )
        //);

        let candidates = self
            .store
            .get(constraint.name())
            .ok_or_else(|| TypeError::NoWitness(constraint.clone()))?;

        //println!("resolve_witness: candidates {candidates:?}");

        for witness in candidates {
            let subst = constraint
                .constraint_type
                .unified_with(&witness.head.constraint_type);

            if subst.is_err() {
                continue;
            }

            let subst = subst?;

            //println!(
            //    "resolve_witness: {constraint} subst {subst} head {} premises `{}`",
            //    witness.head.constraint_type,
            //    display_list(", ", &witness.premises),
            //);

            let witness = witness.apply(&subst);

            let solution = witness
                .premises
                .iter()
                .map(|c| self.resolve_witness(c))
                .collect::<Result<Vec<_>, _>>();

            // Compute some honest type info to insert?
            if let Ok(solution) = solution {
                //println!("resolve_witness: solution {solution:?}");

                // surely the witness can contain this.
                let pi = ParseInfo::default();
                return Ok(solution.into_iter().fold(
                    Expr::Variable(
                        pi.with_inferred_type(Type::fresh()),
                        Identifier::Free(witness.name.clone().into()),
                    ),
                    |f, x| {
                        Expr::Apply(
                            pi.with_inferred_type(Type::fresh()),
                            Apply {
                                function: f.into(),
                                argument: x.into(),
                            },
                        )
                    },
                ));
            }
        }

        Err(TypeError::NoWitness(constraint.clone()))
    }
}
