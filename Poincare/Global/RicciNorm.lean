import Poincare.Global.Curvature
import Poincare.ModelLaplacian

/-!
# Pointwise Ricci norm for closed smooth Riemannian metrics

This module raises one index of the canonical Ricci tensor, defines the
pointwise squared Ricci norm as `tr(Rc o Rc)`, and ports the model trace
Cauchy-Schwarz pinching inequality to tangent fibers.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare
namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

section RicciNorm

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- The metric bilinear form at a point is symmetric. -/
theorem metricBilinAt_isSymm (x : M) :
    LinearMap.IsSymm (g.metricBilinAt x) := by
  rw [LinearMap.isSymm_def]
  intro v w
  exact g.inner_symm x v w

/-- The metric bilinear form at a point is positive-definite on nonzero vectors. -/
theorem metricBilinAt_pos (x : M) {v : TM x} (hv : v ≠ 0) :
    0 < g.metricBilinAt x v v := by
  simpa [metricBilinAt] using g.inner_pos x hv

/-- The Ricci endomorphism, obtained by raising one index of `ricciAt`. -/
noncomputable def ricciEndoAt (x : M) : TM x →ₗ[ℝ] TM x :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)).symm.toLinearMap) ∘ₗ
    CovariantDerivative.ricciDualAt g.leviCivita x

/-- Pairing the raised Ricci endomorphism with the metric recovers `ricciAt`. -/
theorem inner_ricciEndoAt (x : M) (u w : TM x) :
    g.inner x (g.ricciEndoAt x u) w = g.ricciAt x u w := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  change g.metricBilinAt x (g.ricciEndoAt x u) w =
    (CovariantDerivative.ricciDualAt g.leviCivita x u) w
  simpa [ricciEndoAt] using
    (LinearMap.BilinForm.apply_toDual_symm_apply
      (B := g.metricBilinAt x) (hB := g.metricBilinAt_nondegenerate x)
      (CovariantDerivative.ricciDualAt g.leviCivita x u) w)

/-- The Ricci endomorphism is self-adjoint with respect to the metric. -/
theorem ricciEndoAt_selfAdjoint (x : M) (u w : TM x) :
    g.inner x (g.ricciEndoAt x u) w =
      g.inner x u (g.ricciEndoAt x w) := by
  rw [inner_ricciEndoAt, g.inner_symm x u (g.ricciEndoAt x w),
    inner_ricciEndoAt, g.ricciAt_symm x w u]

/-- The pointwise squared Ricci norm, defined as `tr(Rc o Rc)`. -/
noncomputable def ricciNormSqAt (x : M) : ℝ :=
  LinearMap.trace ℝ (TM x) (g.ricciEndoAt x ∘ₗ g.ricciEndoAt x)

/-- The definition of `ricciNormSqAt` as the trace of `Rc o Rc`. -/
theorem ricciNormSqAt_eq_trace (x : M) :
    g.ricciNormSqAt x =
      LinearMap.trace ℝ (TM x) (g.ricciEndoAt x ∘ₗ g.ricciEndoAt x) :=
  rfl

/-- Scalar curvature is the trace of the Ricci endomorphism. -/
theorem scalarAt_eq_trace_ricciEndoAt (x : M) :
    g.scalarAt x = LinearMap.trace ℝ (TM x) (g.ricciEndoAt x) := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  rfl

/-- The tangent fiber has the same real dimension as the closed smooth model. -/
theorem finrank_tangentSpace_eq (x : M) :
    Module.finrank ℝ (TM x) = n := by
  rw [show Module.finrank ℝ (TM x) = Module.finrank ℝ E from rfl,
    finrank_euclideanSpace_fin]

/-- The pointwise Ricci pinching inequality `R^2 <= n |Ric|^2`. -/
theorem scalarAt_sq_le_nat_mul_ricciNormSqAt (x : M) :
    g.scalarAt x ^ 2 ≤ n * g.ricciNormSqAt x := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsa : ∀ p q : TM x,
      g.metricBilinAt x (g.ricciEndoAt x p) q =
        g.metricBilinAt x p (g.ricciEndoAt x q) := by
    intro p q
    simpa [metricBilinAt] using g.ricciEndoAt_selfAdjoint x p q
  have h := RicciFlow.trace_sq_le_card_mul_trace_comp_self
    (b := g.metricBilinAt x)
    (hbs := g.metricBilinAt_isSymm x)
    (hbpos := fun v hv => g.metricBilinAt_pos x hv)
    (A := g.ricciEndoAt x) hsa
  rw [← scalarAt_eq_trace_ricciEndoAt, ← ricciNormSqAt_eq_trace] at h
  simpa [finrank_tangentSpace_eq (n := n) (M := M) x] using h

/-- Equality in the Ricci pinching inequality forces the Ricci endomorphism to be scalar. -/
theorem ricciEndoAt_eq_smul_id_of_scalarAt_sq_eq (x : M)
    (hn : 0 < (n : ℝ))
    (heq : g.scalarAt x ^ 2 = n * g.ricciNormSqAt x) :
    g.ricciEndoAt x = (g.scalarAt x / n) • LinearMap.id := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hsa : ∀ p q : TM x,
      g.metricBilinAt x (g.ricciEndoAt x p) q =
        g.metricBilinAt x p (g.ricciEndoAt x q) := by
    intro p q
    simpa [metricBilinAt] using g.ricciEndoAt_selfAdjoint x p q
  have hdim : (Module.finrank ℝ (TM x) : ℝ) = n := by
    exact_mod_cast finrank_tangentSpace_eq (n := n) (M := M) x
  have hfin : 0 < (Module.finrank ℝ (TM x) : ℝ) := by
    simpa [hdim] using hn
  have heq' :
      (LinearMap.trace ℝ (TM x) (g.ricciEndoAt x)) ^ 2 =
        (Module.finrank ℝ (TM x) : ℝ) *
          LinearMap.trace ℝ (TM x) (g.ricciEndoAt x ∘ₗ g.ricciEndoAt x) := by
    simpa [scalarAt_eq_trace_ricciEndoAt, ricciNormSqAt_eq_trace, hdim] using heq
  have hres := RicciFlow.RicciFlow.eq_smul_id_of_trace_sq_eq
    (b := g.metricBilinAt x)
    (hbs := g.metricBilinAt_isSymm x)
    (hbpos := fun v hv => g.metricBilinAt_pos x hv)
    (A := g.ricciEndoAt x) hsa hfin heq'
  simpa [scalarAt_eq_trace_ricciEndoAt, hdim] using hres

/-- A scalar Ricci endomorphism saturates the Ricci pinching inequality. -/
theorem scalarAt_sq_eq_nat_mul_ricciNormSqAt_of_ricciEndoAt_eq_smul_id
    (x : M) (hn : 0 < (n : ℝ))
    (hEin : g.ricciEndoAt x = (g.scalarAt x / n) • LinearMap.id) :
    g.scalarAt x ^ 2 = n * g.ricciNormSqAt x := by
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hdim : (Module.finrank ℝ (TM x) : ℝ) = n := by
    exact_mod_cast finrank_tangentSpace_eq (n := n) (M := M) x
  rw [ricciNormSqAt_eq_trace, hEin, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, smul_smul, map_smul, LinearMap.trace_id, smul_eq_mul]
  rw [hdim]
  field_simp [ne_of_gt hn]

/-- Equality in `R^2 <= n |Ric|^2` is equivalent to the Einstein operator condition. -/
theorem ricciEndoAt_eq_smul_id_iff_scalarAt_sq_eq (x : M)
    (hn : 0 < (n : ℝ)) :
    g.ricciEndoAt x = (g.scalarAt x / n) • LinearMap.id
      ↔ g.scalarAt x ^ 2 = n * g.ricciNormSqAt x :=
  ⟨g.scalarAt_sq_eq_nat_mul_ricciNormSqAt_of_ricciEndoAt_eq_smul_id x hn,
    g.ricciEndoAt_eq_smul_id_of_scalarAt_sq_eq x hn⟩

end RicciNorm

end ClosedSmoothRiemannianMetric
end Poincare
