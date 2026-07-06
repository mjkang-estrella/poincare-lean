import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Poincare.Global.Curvature

/-!
# Constant rescaling of a closed smooth Riemannian metric

For `c > 0`, the rescaled family `x ↦ c • g.inner x` is again a smooth
Riemannian metric.  This is the construction underlying the
curvature-normalization step of the sphere-recognition endgame: rescaling a
metric of constant positive sectional curvature `κ` by `c = κ` produces a
metric of constant sectional curvature `1`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

universe u

namespace Poincare

namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace (closedSmoothModelWithCorners n) : M → Type _)

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/--
Constant conformal rescaling of a closed smooth Riemannian metric: the metric
whose fiberwise inner product is `c` times that of `g`, for a fixed `c > 0`.
-/
def constSMul (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c) :
    ClosedSmoothRiemannianMetric n M where
  inner x := c • g.inner x
  symm x v w := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact congrArg (c * ·) (g.symm x v w)
  pos x v hv := by
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using
      mul_pos hc (g.pos x v hv)
  isVonNBounded x := by
    have hbase := g.isVonNBounded x
    have himg :=
      hbase.image ((Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (TM x))
    have hsq : Real.sqrt c * Real.sqrt c = c :=
      Real.mul_self_sqrt hc.le
    have hcne : c ≠ 0 := ne_of_gt hc
    have hsqrtpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hsqrtne : Real.sqrt c ≠ 0 := ne_of_gt hsqrtpos
    have hset :
        {v : TM x | (c • g.inner x) v v < 1} =
          ((Real.sqrt c)⁻¹ • ContinuousLinearMap.id ℝ (TM x)) ''
            {v : TM x | g.inner x v v < 1} := by
      ext v
      constructor
      · intro hv
        refine ⟨Real.sqrt c • v, ?_, ?_⟩
        · have hv' : c * g.inner x v v < 1 := by
            simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hv
          have heq : g.inner x (Real.sqrt c • v) (Real.sqrt c • v)
              = c * g.inner x v v := by
            simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
            calc Real.sqrt c * (Real.sqrt c * g.inner x v v)
                = (Real.sqrt c * Real.sqrt c) * g.inner x v v := by ring
              _ = c * g.inner x v v := by rw [hsq]
          show g.inner x (Real.sqrt c • v) (Real.sqrt c • v) < 1
          rw [heq]
          exact hv'
        · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
          rw [smul_smul, inv_mul_cancel₀ hsqrtne, one_smul]
      · rintro ⟨w, hw, rfl⟩
        have hw' : g.inner x w w < 1 := hw
        simp only [Set.mem_setOf_eq, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
        have hr : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = c⁻¹ := by
          rw [← mul_inv]
          exact congrArg (·⁻¹) hsq
        calc c * ((Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * g.inner x w w))
            = c * (((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹) * g.inner x w w) := by ring
          _ = c * (c⁻¹ * g.inner x w w) := by rw [hr]
          _ = g.inner x w w := by field_simp
          _ < 1 := hw'
    rw [hset]
    exact himg
  contMDiff := ContMDiff.const_smul_section (s := g.inner) (a := c) g.contMDiff

@[simp]
theorem constSMul_inner (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c) (x : M) (v w : TM x) :
    (g.constSMul c hc).inner x v w = c * g.inner x v w := by
  simp [constSMul, ContinuousLinearMap.smul_apply, smul_eq_mul]

end ClosedSmoothRiemannianMetric

end Poincare

namespace Poincare

namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I'" => closedSmoothModelWithCorners n
local notation "TM'" => (TangentSpace (closedSmoothModelWithCorners n) : M → Type _)

private theorem rescale_extDerivFun_const {c : ℝ} {x : M} :
    (extDerivFun (I := I') (fun _ : M ↦ c) x : TM' x →L[ℝ] ℝ) = 0 := by
  unfold extDerivFun
  rw [(hasMFDerivAt_const c x).mfderiv]
  ext v
  simp

private theorem rescale_extDerivFun_const_mul {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I' 𝓘(ℝ) f x) (c : ℝ) (v : TM' x) :
    extDerivFun (I := I') (fun y : M ↦ c * f y) x v =
      c * extDerivFun (I := I') f x v := by
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun _ : M ↦ c) (q := f) (x := x) mdifferentiableAt_const hf v
  simpa [rescale_extDerivFun_const] using hmul

/--
The Levi-Civita connection of the base metric is compatible with any constant
positive rescaling of the metric: both sides of the compatibility identity
scale linearly by the constant.
-/
theorem constSMul_metricCompatible_base_leviCivita
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c) :
    IsMetricCompatible (g.constSMul c hc) g.leviCivita := by
  intro x X Y hX hY v
  have hpair := LeviCivitaExistence.metric_pairing_mdiffAt g hX hY
  have hg := g.leviCivita_metricCompatible hX hY v
  have hfun :
      (fun y : M ↦ (g.constSMul c hc).inner y (X y) (Y y)) =
        (fun y : M ↦ c * g.inner y (X y) (Y y)) := by
    funext y
    simp [constSMul_inner]
  calc extDerivFun (I := I')
        (fun y : M ↦ (g.constSMul c hc).inner y (X y) (Y y)) x v
      = extDerivFun (I := I')
          (fun y : M ↦ c * g.inner y (X y) (Y y)) x v := by rw [hfun]
    _ = c * extDerivFun (I := I')
          (fun y : M ↦ g.inner y (X y) (Y y)) x v :=
        rescale_extDerivFun_const_mul hpair c v
    _ = c * (g.inner x (g.leviCivita X x v) (Y x)
          + g.inner x (X x) (g.leviCivita Y x v)) := by rw [hg]
    _ = (g.constSMul c hc).inner x (g.leviCivita X x v) (Y x)
          + (g.constSMul c hc).inner x (X x) (g.leviCivita Y x v) := by
        simp [constSMul_inner]
        ring

/--
Levi-Civita invariance under constant rescaling: at any point, on any tangent
field differentiable there, the Levi-Civita connection of `c • g` agrees with
that of `g`.  Both are torsion-free and compatible with `c • g`, so uniqueness
applies.
-/
theorem constSMul_leviCivita_apply
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    {x : M} {X : ∀ y : M, TangentSpace (closedSmoothModelWithCorners n) y}
    (hX : MDiffAtTangentField X x) :
    (g.constSMul c hc).leviCivita X x = g.leviCivita X x :=
  levi_civita_unique (g.constSMul c hc)
    ((g.constSMul c hc).leviCivita_metricCompatible)
    (constSMul_metricCompatible_base_leviCivita g c hc)
    ((g.constSMul c hc).leviCivita_torsion)
    (g.leviCivita_torsion) hX

end ClosedSmoothRiemannianMetric

end Poincare
