import Poincare.Global.SphereTheorem
import Poincare.Global.ScalarRegularity

/-!
# Shrunk Hamilton pinched-limit interface

Scalar-curvature differentiability is now supplied by closed smooth metric
regularity, so the Hamilton limit interface can expose only the genuine
pinched-limit payload: vanishing traceless Ricci and positive scalar curvature.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
The reduced Hamilton-convergence payload after scalar regularity has been
made unconditional for closed smooth metrics.
-/
def HamiltonConvergencePinchedLimit3Core (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ g : ClosedSmoothRiemannianMetric 3 M,
    (∀ x : M, g.tracelessRicciNormSqAt x = 0) ∧
    (∃ x : M, 0 < g.scalarAt x)

/--
The original Hamilton-convergence interface is equivalent to the reduced core:
the omitted scalar-regularity conjunct is supplied by
`scalarAt_mdifferentiableAt`.
-/
theorem hamiltonConvergencePinchedLimit3_iff_core :
    HamiltonConvergencePinchedLimit3 M ↔
      HamiltonConvergencePinchedLimit3Core M := by
  constructor
  · intro hHamilton
    rcases hHamilton with ⟨g, _hScalarDiff, htr, hpos⟩
    exact ⟨g, htr, hpos⟩
  · intro hCore
    rcases hCore with ⟨g, htr, hpos⟩
    exact ⟨g, (fun x ↦ scalarAt_mdifferentiableAt (g := g) x), htr, hpos⟩

/--
Minimal-interface statement-chain composition using the reduced Hamilton core
and unit-curvature sphere recognition.
-/
theorem poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (hUnit :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitConstantCurvatureSphereRecognition3 N) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    (fun N _ _ _ _ _ _ _ _ =>
      (hamiltonConvergencePinchedLimit3_iff_core (M := N)).mpr
        (hHamilton N))
    hUnit

end Poincare
