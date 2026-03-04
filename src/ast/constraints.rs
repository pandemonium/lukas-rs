use std::{
    collections::{HashMap, HashSet},
    fmt, panic,
};

use crate::{
    ast::{
        Apply, Expr,
        namer::{self, DependencyMatrix, Identifier, Named, QualifiedName, TermSymbol},
    },
    parser::ParseInfo,
    phase,
    typer::{
        Constraint, RecordShape, Substitutions, Type, TypeEnvironment, TypeError, TypeInfo,
        TypeStructure, Types, Typing, TypingContext, display_list,
    },
};

pub struct ConstraintSignature {
    pub name: QualifiedName,
    pub interface: RecordShape,
}

impl Constraint {
    pub fn signature(&self, env: &TypeEnvironment) -> Result<ConstraintSignature, TypeError> {
        let type_constructor = env
            .lookup(self.name())
            .ok_or_else(|| TypeError::UndefinedSignature(self.name().clone()))?;

        if let TypeStructure::PolyRecord(record) =
            type_constructor.structure().map_err(|e| *e.error)?
        {
            Ok(ConstraintSignature {
                name: self.name().clone(),
                interface: record.shape(),
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
        witness: phase::TypeSignature<Named>,
        ctx: &TypingContext,
    ) -> Typing<Self> {
        let witness_signature = witness.type_scheme(&HashMap::default(), ctx)?;
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
        println!("register: {} :: {}", witness.name, witness.head);

        self.store
            .entry(witness.head.name().clone())
            .or_default()
            .push(witness);
    }

    pub fn dependency_matrix(
        &self,
        ctx: &TypeEnvironment,
    ) -> Result<DependencyMatrix<QualifiedName>, TypeError> {
        let mut graph = HashMap::default();
        let mut deps = DependencyMatrix::default();

        for witness in self.store.values().flatten() {
            match self.resolve_witness_dependencies(witness, &mut graph, ctx) {
                Ok(()) => println!("resolve: {witness}"),
                Err(e) => println!("resolve: {e}"),
            }
        }

        for (k, v) in graph {
            println!(
                "resolve: {k} -> {}",
                display_list(", ", &v.iter().collect::<Vec<_>>())
            );
            deps.add_edge(k, v.into_iter().collect());
        }

        Ok(deps)
    }

    fn resolve_witness_dependencies(
        &self,
        witness: &Witness,
        graph: &mut HashMap<QualifiedName, HashSet<QualifiedName>>,
        ctx: &TypeEnvironment,
    ) -> Result<(), TypeError> {
        self.resolve_constraint_witness_dependencies(&witness.head, &witness.name, graph, ctx)?;
        Ok(())
    }

    fn resolve_term_witness_dependencies(
        &self,
        term: TermSymbol<TypeInfo, QualifiedName, namer::Identifier>,
    ) -> Result<(), TypeError> {
        todo!()
    }

    fn resolve_constraint_witness_dependencies(
        &self,
        constraint: &Constraint,
        source: &QualifiedName,
        graph: &mut HashMap<QualifiedName, HashSet<QualifiedName>>,
        ctx: &TypeEnvironment,
    ) -> Result<QualifiedName, TypeError> {
        let candidates = self
            .store
            .get(&constraint.name())
            .ok_or_else(|| TypeError::NoWitness(constraint.clone()))?;

        for witness in candidates {
            let subst = constraint
                .constraint_type
                .unified_with(&witness.head.constraint_type, ctx);

            if subst.is_err() {
                continue;
            }

            let subst = subst?;
            let witness = witness.apply(&subst);

            let mut graph_candidate = HashMap::default();

            println!(
                "resolve_and_record: {} has {} premises.",
                witness.name,
                display_list(", ", &witness.premises)
            );

            let solution = witness
                .premises
                .iter()
                .map(|c| {
                    self.resolve_constraint_witness_dependencies(
                        c,
                        &witness.name,
                        &mut graph_candidate,
                        ctx,
                    )
                })
                .collect::<Result<Vec<_>, TypeError>>();

            if let Ok(solution) = solution {
                println!(
                    "resolve_and_record: witness {} solution {} source {source}.",
                    witness.name,
                    display_list(", ", &solution)
                );

                for (k, v) in graph_candidate {
                    graph.entry(k).or_default().extend(v);
                }

                graph.entry(source.clone()).or_default().extend(solution);
                return Ok(witness.name);
            }
        }

        Err(TypeError::NoWitness(constraint.clone()))
    }

    pub fn resolve_witness(
        &self,
        constraint: &Constraint,
        ctx: &TypeEnvironment,
    ) -> Result<phase::Expr<Types>, TypeError> {
        let candidates = self
            .store
            .get(constraint.name())
            .ok_or_else(|| TypeError::NoWitness(constraint.clone()))?;

        for witness in candidates {
            let subst = constraint
                .constraint_type
                .unified_with(&witness.head.constraint_type, ctx);

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
                .map(|c| self.resolve_witness(c, ctx))
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

        println!("resolve_witness: index {self:?}");
        Err(TypeError::NoWitness(constraint.clone()))
    }
}

impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            head,
            premises,
            name,
        } = self;
        write!(
            f,
            "witness {name} {} |- {head}",
            display_list(" + ", premises)
        )
    }
}
