use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use crate::{
    ast::{
        Apply, Expr,
        namer::{DependencyMatrix, Identifier, Named, QualifiedName},
    },
    parser::ParseInfo,
    phase,
    typer::{
        Constraint, RecordShape, Substitutions, Type, TypeEnvironment, TypeError, TypeStructure,
        Types, Typing, TypingContext, display_list,
    },
};

pub struct ConstraintSignature {
    pub name: QualifiedName,
    pub vtable: RecordShape,
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
                vtable: record.shape(),
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
pub struct WitnessEnvironment {
    store: HashMap<QualifiedName, Vec<Witness>>,
}

impl WitnessEnvironment {
    pub fn register(&mut self, witness: Witness) {
        self.store
            .entry(witness.head.name().clone())
            .or_default()
            .push(witness);
    }

    /// The registered witness a given symbol name elaborates to, if any. Used by
    /// constraint discharge to bind a witness's dictionary parameters in the same
    /// order `resolve_witness` supplies its premises (see `premises`).
    pub fn witness_named(&self, name: &QualifiedName) -> Option<&Witness> {
        self.store.values().flatten().find(|w| &w.name == name)
    }

    pub fn dependency_matrix(
        &self,
        ctx: &TypeEnvironment,
    ) -> Result<DependencyMatrix<QualifiedName>, TypeError> {
        let mut graph = HashMap::default();
        let mut deps = DependencyMatrix::default();

        for witness in self.store.values().flatten() {
            self.resolve_witness_dependencies(witness, &mut graph, ctx)?;
        }

        for (k, v) in graph {
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

            //tracing::trace!(
            //    "resolve_and_record: {} has {} premises.",
            //    witness.name,
            //    display_list(", ", &witness.premises)
            //);

            let solution = witness
                .premises
                .iter()
                // A parametric premise (variable-headed, e.g. `Applicative m`) is
                // satisfied by a dictionary *parameter*, not by another witness -- so
                // it has no witness dependency. Resolving it against instances is both
                // wrong and non-terminating: it unifies with a transformer head like
                // `Applicative (ExceptT m e)` (m := ExceptT ...) and recurses forever.
                .filter(|c| !c.is_parametric())
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
                //tracing::trace!(
                //    "resolve_and_record: witness {} solution {} source {source}.",
                //    witness.name,
                //    display_list(", ", &solution)
                //);

                for (k, v) in graph_candidate {
                    graph.entry(k).or_default().extend(v);
                }

                graph.entry(source.clone()).or_default().extend(solution);
                return Ok(witness.name);
            }
        }

        Err(TypeError::NoWitness(constraint.clone()))
    }

    #[tracing::instrument(skip_all)]
    pub fn resolve_witness(
        &self,
        constraint: &Constraint,
        ctx: &TypeEnvironment,
        assumptions: &HashMap<Constraint, phase::Expr<Types>>,
    ) -> Result<phase::Expr<Types>, TypeError> {
        tracing::trace!("{constraint}");

        // A constraint we already hold as evidence -- a dictionary parameter of
        // the enclosing declaration, e.g. the `Eq α` premise threaded into an
        // `Eq (List α)` instance -- is discharged directly by that evidence.
        // This is what lets a recursive derived instance tie its own knot: the
        // instance's `Eq (List α)` premise resolves to the instance applied to
        // the `Eq α` parameter it already has in scope.
        if let Some(evidence) = assumptions.get(constraint) {
            return Ok(evidence.clone());
        }

        // A variable-headed constraint (`Functor m`, `m` abstract) can only be
        // discharged by an assumption -- a dictionary parameter of the enclosing
        // declaration. No concrete witness applies: unifying one here would ground
        // the abstract variable against the witness head, fabricating a nonsensical
        // (often self-nested) dictionary. Fail instead, so the caller's param logic
        // is forced to bind the parameter this premise needs.
        if constraint.is_parametric() {
            return Err(TypeError::NoWitness(constraint.clone()));
        }

        // `Memory_Layout τ` is compiler-derived, never user-written: a ground query
        // is discharged by synthesised evidence -- a reference to the `memory_layout`
        // marker carrying the ground `Memory_Layout τ` as its type, so the backend
        // recovers `τ` and emits the layout dictionary. (A parametric `Memory_Layout α`
        // took the early return above, becoming a forwarded dictionary parameter --
        // ML1's "dyn" fallback -- so a caller who knows the concrete type fills it in.)
        if *constraint.name() == crate::typer::memory_layout_class() {
            // A still-abstract obligation whose SHAPE depends on those variables
            // (`Memory_Layout (Perhaps (Entry α β))` inside a polymorphic wrapper)
            // reaches here only when it was NOT held as an assumption -- the
            // enclosing declaration does not carry the component layouts needed to
            // build it. We cannot synthesise a shape for such a type: the backend
            // would emit a garbage/empty descriptor that the callee then trusts,
            // segfaulting at ground use. Reject instead, so the caller must declare
            // the component layout constraints (which composition below discharges).
            //
            // A non-ground shape that does NOT depend on the variables (e.g.
            // `Memory_Layout (Raw_State α β)`, whose fields all sit behind one-word
            // boundaries) is safe: element-zero discovery / boxing is identical
            // whether the parameters are ground or abstract, so synthesise it. A
            // ground query likewise synthesises the marker the backend lowers.
            if !constraint.constraint_type.variables().is_empty()
                && crate::typer::memory_layout_requires_parameter(constraint, ctx)
            {
                return Err(TypeError::NoWitness(constraint.clone()));
            }
            let pi = ParseInfo::default();
            return Ok(Expr::Variable(
                pi.with_inferred_type(constraint.constraint_type.clone()),
                Identifier::Free(crate::typer::memory_layout_evidence_name().into()),
            ));
        }

        let candidates = self
            .store
            .get(constraint.name())
            .ok_or_else(|| TypeError::NoWitness(constraint.clone()))?;

        for witness in candidates {
            // Unify witness-head-against-query (not the reverse) so the
            // witness's own quantifier variables are substituted *into the
            // query's* variables. That keeps a resolved premise (e.g. `Eq α`)
            // expressed in the same variable as the surrounding dictionary
            // parameters, so the `assumptions` lookup above can find it. For a
            // ground query the concrete type forces the same substitution either
            // way.
            let subst = witness
                .head
                .constraint_type
                .unified_with(&constraint.constraint_type, ctx);

            if subst.is_err() {
                continue;
            }

            let subst = subst?;

            //tracing::trace!(
            //    "resolve_witness: {constraint} subst {subst} head {} premises `{}`",
            //    witness.head.constraint_type,
            //    display_list(", ", &witness.premises),
            //);

            let witness = witness.apply(&subst);

            let solution = witness
                .premises
                .iter()
                .map(|c| self.resolve_witness(c, ctx, assumptions))
                .collect::<Result<Vec<_>, _>>();

            // Compute some honest type info to insert?
            if let Ok(solution) = solution {
                //tracing::trace!("solution {solution:?}");

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

    /// The premises a witness for `constraint` would require, with the witness's
    /// quantifier variables substituted to match the query. Lets the discharge
    /// logic surface a resolvable constraint's *parametric* premises (e.g. the
    /// `Functor m` behind `Functor (ExceptT m e)`) so the enclosing declaration
    /// binds a dictionary parameter for them rather than having `resolve_witness`
    /// ground the abstract premise. Empty if no witness head matches.
    pub fn premises_of(&self, constraint: &Constraint, ctx: &TypeEnvironment) -> Vec<Constraint> {
        let Some(candidates) = self.store.get(constraint.name()) else {
            return Vec::new();
        };
        candidates
            .iter()
            .find_map(|witness| {
                witness
                    .head
                    .constraint_type
                    .unified_with(&constraint.constraint_type, ctx)
                    .ok()
                    .map(|subst| witness.premises.iter().map(|c| c.apply(&subst)).collect())
            })
            .unwrap_or_default()
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
