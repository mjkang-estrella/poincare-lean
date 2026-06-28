import Poincare.TopologyExtraction

open scoped Manifold ContDiff

namespace Poincare

universe u

/--
The exact first-field API needed by `ExtinctionTopologyExtractionPackage`: for
each fixed finite-extinction witness, supply the post-extinction topology
decomposition attached to that witness.
-/
def ExtinctionTopologyDecompositionWitnessStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      HasExtinctionTopologyDecomposition M extinction

/--
The decomposition witness statement is exactly the first field shape of
`ExtinctionTopologyExtractionPackage`.
-/
theorem extinctionTopologyDecompositionWitnessStatement_eq :
    ExtinctionTopologyDecompositionWitnessStatement.{u} =
      (∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [SimplyConnectedSpace M] [CompactSpace M]
        (extinction : FiniteExtinctionByRicciFlowWithSurgery M),
          HasExtinctionTopologyDecomposition M extinction) :=
  rfl

/--
A full fixed-extinction topology derivation necessarily contains the
post-extinction topology decomposition as its first witness.
-/
theorem extinction_decomposition_of_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    HasExtinctionTopologyDecomposition M extinction := by
  rcases derivationStatement with ⟨decomposition, _⟩
  exact decomposition

/-- The derivation-statement projection is the first existential projection. -/
theorem extinction_decomposition_of_derivation_statement_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (derivationStatement :
      ExtinctionTopologyDerivationStatement M extinction homeomorphism) :
    extinction_decomposition_of_derivation_statement
        M extinction homeomorphism derivationStatement =
      (by
        rcases derivationStatement with ⟨decomposition, _⟩
        exact decomposition) := by
  apply Subsingleton.elim

/--
The theorem-shaped extraction statement supplies the decomposition witness by
first selecting its fixed-extinction homeomorphism and derivation certificate.
-/
theorem extinction_decomposition_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionTopologyDecomposition M extinction := by
  rcases topologyStatement M extinction with
    ⟨homeomorphism, derivationStatement⟩
  exact extinction_decomposition_of_derivation_statement
    M extinction homeomorphism derivationStatement

/-- The extraction-statement projection goes through its fixed-extinction derivation. -/
theorem extinction_decomposition_of_extraction_statement_eq
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    extinction_decomposition_of_extraction_statement
        topologyStatement M extinction =
      (by
        rcases topologyStatement M extinction with
          ⟨homeomorphism, derivationStatement⟩
        exact extinction_decomposition_of_derivation_statement
          M extinction homeomorphism derivationStatement) := by
  apply Subsingleton.elim

/--
A derivation certificate for a chosen extractor supplies the same
fixed-extinction decomposition witness.
-/
theorem extinction_decomposition_of_derivation_for_extraction_statement
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivationForExtraction :
      ExtinctionTopologyDerivationForExtractionStatement extractSphere)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    HasExtinctionTopologyDecomposition M extinction :=
  extinction_decomposition_of_derivation_statement M extinction
    (extractSphere M extinction) (derivationForExtraction M extinction)

/--
A lifted homeomorphism-derivation statement also exposes the same first
decomposition witness.
-/
theorem extinction_decomposition_of_lifted_homeomorphism_derivation_statement
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (homeomorphism : Nonempty (M ≃ₜ ThreeSphere))
    (liftedDerivation :
      ExtinctionTopologyLiftedHomeomorphismDerivationStatement
        M extinction homeomorphism) :
    HasExtinctionTopologyDecomposition M extinction := by
  rcases liftedDerivation with ⟨decomposition, _⟩
  exact decomposition

/--
The theorem-shaped extraction statement is sufficient to discharge exactly the
first topology-package field, without asserting the remaining package fields.
-/
theorem extinctionTopologyDecompositionWitnessStatement_of_extraction_statement
    (topologyStatement : ExtinctionTopologyExtractionStatement.{u}) :
    ExtinctionTopologyDecompositionWitnessStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  exact extinction_decomposition_of_extraction_statement
    topologyStatement M extinction

/--
The derivation-for-extraction statement is sufficient to discharge exactly the
first topology-package field.
-/
theorem extinctionTopologyDecompositionWitnessStatement_of_derivation_for_extraction_statement
    (extractSphere : ExtinctionImpliesSphereStatement.{u})
    (derivationForExtraction :
      ExtinctionTopologyDerivationForExtractionStatement extractSphere) :
    ExtinctionTopologyDecompositionWitnessStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  exact extinction_decomposition_of_derivation_for_extraction_statement
    extractSphere derivationForExtraction M extinction

/--
A completed topology package exposes its first field as the standalone
decomposition witness statement.
-/
theorem extinctionTopologyDecompositionWitnessStatement_of_topology_package
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    ExtinctionTopologyDecompositionWitnessStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  exact extinction_decomposition_of_topology_package package M extinction

/--
The package bridge is definitionally the package's stored decomposition field.
-/
theorem extinctionTopologyDecompositionWitnessStatement_of_topology_package_eq
    (package : ExtinctionTopologyExtractionPackage.{u}) :
    extinctionTopologyDecompositionWitnessStatement_of_topology_package package =
      (by
        intro M _top _t2 _charted _simple _compact extinction
        exact extinction_decomposition_of_topology_package
          package M extinction) := by
  rfl

end Poincare
