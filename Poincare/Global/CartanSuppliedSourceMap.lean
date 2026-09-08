import Poincare.Global.CartanSourceExponentialFamily

/-!
# Cartan germs with supplied source and target charts

The source normal chart and target exponential family determine a local map
for any continuous linear equivalence of the model space. The anchor laws
give source membership without joint regularity or curvature assumptions.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanSuppliedSourceMap

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Compose supplied normal coordinates, a linear equivalence, and the target chart. -/
def germ (S : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E) : OpenPartialHomeomorph M RoundSphere3 :=
  (S.normal x).trans
    (K.toHomeomorph.toOpenPartialHomeomorph.trans
      ((F.chart p).trans (chartAt E p).symm))

/-- The supplied source anchor lies in the source of the composite germ. -/
theorem anchor_mem_source (S : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E) : x ∈ (germ S F x p K).source := by
  have hp : (chartAt E p) p = (0 : E) := by
    simpa [extChartAt_coe] using
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p
  have hptarget := (chartAt E p).map_source (mem_chart_source E p)
  simpa [germ, S.anchor_mem_source x, S.normal_anchor x,
    F.zero_mem_source p, F.chart_zero p, hp] using hptarget

/-- The supplied germ sends its source anchor to its target anchor. -/
theorem germ_anchor (S : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E) : germ S F x p K x = p := by
  have hp : (chartAt E p) p = (0 : E) := by
    simpa [extChartAt_coe] using
      RoundSphereTargetAnchorUniformity.extChartAt_roundSphere_self_eq_zero p
  change (chartAt E p).symm (F.chart p (K (S.normal x x))) = p
  rw [S.normal_anchor, map_zero, F.chart_zero, ← hp]
  exact (chartAt E p).left_inv (mem_chart_source E p)

/-- The forward map is the stated composition, including its total extension. -/
theorem germ_apply (S : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E) :
    (germ S F x p K : M → RoundSphere3) =
      fun z => (chartAt E p).symm (F.chart p (K (S.normal x z))) :=
  rfl

end CartanSuppliedSourceMap
end Poincare
