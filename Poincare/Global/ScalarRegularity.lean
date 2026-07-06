import Poincare.Global.ScalarVariation

/-!
# Scalar-curvature regularity for closed smooth metrics

This module packages the now-unconditional first-order regularity of scalar
curvature.  The proof uses the existing Gram-frame trace route: scalar
curvature is the metric trace of the Ricci tensor, Ricci entries are
differentiable in canonical extension slots, and the metric trace of a
differentiable `(0,2)` tensor is differentiable.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Scalar curvature of a closed smooth Riemannian metric is differentiable at
every point.
-/
theorem scalarAt_mdifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ g.scalarAt y) x := by
  have hTrace :
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y) x :=
    traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := ricciVariationField g) (x := x)
      (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
        (g := g) x)
      (ricciVariationBilinForm g)
      (by intro y p q; rfl)
  have hfun :
      (fun y : M ↦ traceMetricVariationAt g (ricciVariationField g) y) =
        fun y : M ↦ g.scalarAt y := by
    funext y
    exact traceMetricVariationAt_ricci g y
  simpa [hfun] using hTrace

end Poincare
