import Poincare.Global.MetricRescaleCurvature
import Poincare.Global.Laplacian

/-!
# Scalar-gradient scaling under constant metric rescaling

Raising a scalar differential with `c g` multiplies its gradient by `c⁻¹`.
Scalar curvature itself gains another factor `c⁻¹`, so its squared gradient
norm gains three inverse factors after pairing with the rescaled metric.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare.MetricRescaleScalarGradient

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Raising the same scalar differential with the rescaled metric. -/
theorem constSMul_gradientAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (f : M → ℝ) (x : M) :
    (g.constSMul c hc).gradientAt f x = c⁻¹ • g.gradientAt f x := by
  apply sub_eq_zero.mp
  refine LeviCivitaExistence.metric_nondegenerate (g.constSMul c hc) x _ ?_
  intro w
  rw [map_sub, ContinuousLinearMap.sub_apply,
    ClosedSmoothRiemannianMetric.inner_gradientAt,
    ClosedSmoothRiemannianMetric.constSMul_inner]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ClosedSmoothRiemannianMetric.inner_gradientAt]
  field_simp [ne_of_gt hc]
  ring

/-- At a point without a scalar differential, the chosen gradient is zero. -/
theorem gradientAt_zero_of_not_mdifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M) {f : M → ℝ} {x : M}
    (hf : ¬ MDifferentiableAt I 𝓘(ℝ) f x) :
    g.gradientAt f x = 0 := by
  have hdf : (extDerivFun f x : TM x →L[ℝ] ℝ) = 0 := by
    unfold extDerivFun
    rw [mfderiv_zero_of_not_mdifferentiableAt hf]
    ext v
    simp
  unfold ClosedSmoothRiemannianMetric.gradientAt
  rw [hdf]
  simp

/-- A nonzero constant commutes with the gradient, including the zero-derivative case. -/
theorem gradientAt_const_smul_of_ne_zero
    (g : ClosedSmoothRiemannianMetric n M) (a : ℝ) (ha : a ≠ 0)
    (f : M → ℝ) (x : M) :
    g.gradientAt (a • f) x = a • g.gradientAt f x := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ) f x
  · exact g.gradientAt_const_smul a hf
  · have hscaled : ¬ MDifferentiableAt I 𝓘(ℝ) (a • f) x := by
      intro hs
      apply hf
      simpa only [inv_smul_smul₀ ha] using hs.const_smul a⁻¹
    rw [gradientAt_zero_of_not_mdifferentiableAt g hscaled,
      gradientAt_zero_of_not_mdifferentiableAt g hf, smul_zero]

/-- The scalar-curvature gradient acquires one inverse factor from each source. -/
theorem constSMul_scalarGradientAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (g.constSMul c hc).leviCivita 1]
    (x : M) :
    (g.constSMul c hc).gradientAt (fun y ↦ (g.constSMul c hc).scalarAt y) x =
      (c⁻¹) ^ 2 • g.gradientAt (fun y ↦ g.scalarAt y) x := by
  have hscalar : (fun y ↦ (g.constSMul c hc).scalarAt y) =
      c⁻¹ • (fun y ↦ g.scalarAt y) := by
    funext y
    exact g.constSMul_scalarAt c hc y
  rw [hscalar, constSMul_gradientAt,
    gradientAt_const_smul_of_ne_zero g c⁻¹ (inv_ne_zero (ne_of_gt hc)),
    smul_smul, pow_two]

/-- Squared scalar-gradient norms scale by `c⁻³` under positive constant metric rescaling. -/
theorem constSMul_scalarGradNormSqAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    [CovariantDerivative.ContMDiffCovariantDerivative (g.constSMul c hc).leviCivita 1]
    (x : M) :
    (g.constSMul c hc).scalarGradNormSqAt x =
      (c⁻¹) ^ 3 * g.scalarGradNormSqAt x := by
  unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
  rw [constSMul_scalarGradientAt,
    ClosedSmoothRiemannianMetric.constSMul_inner]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hc]

end Poincare.MetricRescaleScalarGradient
