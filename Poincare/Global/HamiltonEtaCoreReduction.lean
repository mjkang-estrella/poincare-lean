import Poincare.Global.HamiltonInitialPinchingReactionCoreReduction
import Poincare.Global.HamiltonStokesFreeReactionCore

/-!
# Hamilton convergence from a uniform normalization gap

The gap supplies both the positive mean floor and the reaction rate.
Existence of a flow and compact realization with this gap remains an input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonEtaCoreReduction
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Eta bounds the mean scalar from below on every positive-scalar slice.
The arithmetic only needs `d ≤ 2`, hence applies to the core's `0 < d ≤ 1`. -/
theorem meanFloorFromEta
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
    (hd : d ≤ 2) (heta : 0 < eta)
    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
  classical
  constructor
  · positivity
  · intro t
    let x : M := Classical.choice (inferInstance : Nonempty M)
    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
      norm_num at hU
      exact (div_nonneg (by positivity) (by norm_num)).trans hU
    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
    have h := hgap t.1 t.2 x
    linarith

end Poincare.HamiltonEtaCoreReduction
