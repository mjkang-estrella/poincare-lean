import Poincare.Global.CoveringSkeleton
import Poincare.ProofProgress.GroundedFiniteExtinctionCertificate
import Poincare.ProofProgress.TopologyProductionPackageNextField

/-!
# Topology extraction from a spherical covering projection

A covering projection `ThreeSphere → M` is a non-circular recognition
interface after finite extinction.  When the target is simply connected,
covering-space theory upgrades that projection to a homeomorphism.  This file
records both the direct post-extinction statement and its form after a fixed
topological decomposition.

Unlike the existing long spherical-space-form package, the new premise does
not contain a homeomorphism, inverse map, trivial quotient, or final
recognition payload.
-/

open scoped Manifold ContDiff

namespace Poincare

universe u

/-- The direct post-extinction topology frontier: finite extinction produces
an actual covering projection from the standard three-sphere. -/
def ExtinctionThreeSphereCoveringProjectionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (_extinction : FiniteExtinctionByRicciFlowWithSurgery M),
      ∃ p : ThreeSphere → M, IsCoveringMap p

/-- A spherical covering projection over a simply connected manifold is the
post-extinction sphere homeomorphism. -/
theorem extinctionImpliesSphereStatement_of_threeSphereCoveringProjection
    (hCover : ExtinctionThreeSphereCoveringProjectionStatement.{u}) :
    ExtinctionImpliesSphereStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  rcases hCover M extinction with ⟨p, hp⟩
  let e : ThreeSphere ≃ₜ M :=
    GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected hp
  exact ⟨e.symm⟩

/-- Grounded universal finite extinction and the spherical-covering theorem
prove the project-level Poincare statement without passing through a package
that already stores the final homeomorphism. -/
theorem poincare_statement_of_grounded_and_threeSphereCoveringProjection
    (grounded : GroundedUniversalFiniteExtinctionStatement.{u})
    (hCover : ExtinctionThreeSphereCoveringProjectionStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_extinction_and_extraction
    (universalFiniteExtinctionStatement_of_grounded grounded)
    (extinctionImpliesSphereStatement_of_threeSphereCoveringProjection hCover)

/-- The same spherical-covering frontier after a concrete extinction
decomposition has been selected. -/
def ExtinctionThreeSphereCoveringProjectionAfterDecompositionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (extinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (_decomposition : HasExtinctionTopologyDecomposition M extinction),
      ∃ p : ThreeSphere → M, IsCoveringMap p

/-- The direct covering-projection statement supplies its
decomposition-indexed form. -/
theorem threeSphereCoveringProjectionAfterDecomposition_of_direct
    (hCover : ExtinctionThreeSphereCoveringProjectionStatement.{u}) :
    ExtinctionThreeSphereCoveringProjectionAfterDecompositionStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction _decomposition
  exact hCover M extinction

/-- A spherical covering projection after decomposition gives recognition by
the one-point compactification of three-dimensional Euclidean space. -/
theorem onePointCompactificationRecognitionAfterDecompositionStatement_of_threeSphereCoveringProjection
    (hCover :
      ExtinctionThreeSphereCoveringProjectionAfterDecompositionStatement.{u}) :
    OnePointCompactificationRecognitionAfterDecompositionStatement.{u} := by
  intro M _top _t2 _charted _simple _compact extinction decomposition
  letI : LocPathConnectedSpace M :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  rcases hCover M extinction decomposition with ⟨p, hp⟩
  let e : ThreeSphere ≃ₜ M :=
    GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected hp
  exact
    homeomorph_to_onePoint_threeSpace_of_homeomorph_to_threeSphere ⟨e.symm⟩

/-- Once the two honest surgery-trace prefix fields are supplied, the
spherical covering projection fills the recognition side of the existing
topology-extraction package. -/
theorem extinction_topology_extraction_statement_of_surgeryTracePrefix_and_threeSphereCoveringProjection
    (surgeryTracePrefix : ExtinctionTopologySurgeryTracePrefixPackage.{u})
    (hCover :
      ExtinctionThreeSphereCoveringProjectionAfterDecompositionStatement.{u}) :
    ExtinctionTopologyExtractionStatement.{u} :=
  extinction_topology_extraction_statement_of_surgeryTracePrefix_and_onePointCompactificationRecognition
    surgeryTracePrefix
    (onePointCompactificationRecognitionAfterDecompositionStatement_of_threeSphereCoveringProjection
      hCover)

end Poincare
