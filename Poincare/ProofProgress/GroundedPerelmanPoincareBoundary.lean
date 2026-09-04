import Poincare.ProofProgress.ExtinctionThreeSphereCoveringProjection
import Poincare.ProofProgress.GroundedPerelmanFiniteExtinctionBridge

/-!
# Poincare boundary with grounded Perelman control

The strengthened Ricci-flow premise below retains grounded Perelman
singularity control for every candidate manifold. It still does not prove the
topological extraction step. The final theorem therefore keeps the independent
spherical covering-projection premise explicit.
-/

open scoped Manifold ContDiff

namespace Poincare

universe u

/-- Every compact simply connected charted 3-manifold carries a finite-
extinction certificate that retains its nonvacuous Perelman source. -/
def GroundedPerelmanUniversalFiniteExtinctionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      GroundedPerelmanFiniteExtinctionProductionCertificate M

/-- Forgetting the retained Perelman sources gives the existing grounded
universal finite-extinction statement. -/
theorem groundedUniversalFiniteExtinctionStatement_of_groundedPerelman
    (grounded : GroundedPerelmanUniversalFiniteExtinctionStatement.{u}) :
    GroundedUniversalFiniteExtinctionStatement.{u} := by
  intro M _top _t2 _charted _simple _compact
  exact groundedFiniteExtinctionProductionCertificate_of_groundedPerelman
    (grounded M)

/-- The strengthened universal statement also projects to the legacy
finite-extinction statement. -/
theorem universalFiniteExtinctionStatement_of_groundedPerelman
    (grounded : GroundedPerelmanUniversalFiniteExtinctionStatement.{u}) :
    UniversalFiniteExtinctionStatement.{u} :=
  universalFiniteExtinctionStatement_of_grounded
    (groundedUniversalFiniteExtinctionStatement_of_groundedPerelman grounded)

/-- Grounded Perelman finite extinction and an independent spherical covering
projection after extinction imply the project statement. This remains a
conditional boundary theorem; the covering-projection premise is not supplied
here and no stored homeomorphism is used. -/
theorem poincare_statement_of_groundedPerelman_and_threeSphereCoveringProjection
    (grounded : GroundedPerelmanUniversalFiniteExtinctionStatement.{u})
    (hCover : ExtinctionThreeSphereCoveringProjectionStatement.{u}) :
    PoincareConjectureStatement.{u} :=
  poincare_statement_of_grounded_and_threeSphereCoveringProjection
    (groundedUniversalFiniteExtinctionStatement_of_groundedPerelman grounded)
    hCover

end Poincare
