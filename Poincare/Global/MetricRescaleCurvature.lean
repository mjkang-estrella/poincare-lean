import Poincare.Global.MetricRescale
import Poincare.Global.RicciNorm

/-!
# Curvature functional transport under constant metric rescaling

For a constant positive rescaling `g.constSMul c hc`, the Levi-Civita
connection and hence the `(0,2)` Ricci tensor are unchanged.  Raising one index
uses the inverse metric, so the Ricci endomorphism gains one factor `c⁻¹`.
Taking traces gives scalar curvature a factor `c⁻¹`, while quadratic
trace-form quantities gain `(c⁻¹)^2`.
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
local notation "TM" => (TangentSpace I : M → Type _)

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

omit [T2Space M] in
theorem constSMul_metricBilinAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    (g.constSMul c hc).metricBilinAt x = c • g.metricBilinAt x := by
  ext v w
  simp [metricBilinAt, constSMul_inner, smul_eq_mul]

private theorem BilinForm.toDual_const_smul_symm_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (b : LinearMap.BilinForm ℝ V) (hb : b.Nondegenerate)
    {c : ℝ} (hc : c ≠ 0) (hb' : (c • b).Nondegenerate)
    (ψ : Module.Dual ℝ V) :
    (LinearMap.BilinForm.toDual (c • b) hb').symm ψ =
      c⁻¹ • (LinearMap.BilinForm.toDual b hb).symm ψ := by
  rw [LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro w
  rw [LinearMap.BilinForm.toDual_def]
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
  have hbw : b ((LinearMap.BilinForm.toDual b hb).symm ψ) w = ψ w := by
    have h := LinearEquiv.apply_symm_apply
      (LinearMap.BilinForm.toDual b hb) ψ
    have h2 := congrArg (fun L : Module.Dual ℝ V ↦ L w) h
    simpa [LinearMap.BilinForm.toDual_def] using h2
  rw [hbw]
  field_simp [hc]

theorem constSMul_ricciAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) (u w : TM x) :
    (g.constSMul c hc).ricciAt x u w = g.ricciAt x u w := by
  rw [ricciAt, ricciAt]
  exact CovariantDerivative.ricciBilinearAt_eq_of_agree
    (cov := (g.constSMul c hc).leviCivita) (cov' := g.leviCivita)
    (fun y Y hY ↦
      constSMul_leviCivita_apply g c hc
        (by simpa [MDiffAtTangentField] using hY))
    x u w

theorem constSMul_ricciDualAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    CovariantDerivative.ricciDualAt (g.constSMul c hc).leviCivita x =
      CovariantDerivative.ricciDualAt g.leviCivita x := by
  ext u w
  exact constSMul_ricciAt g c hc x u w

theorem constSMul_ricciEndoAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    (g.constSMul c hc).ricciEndoAt x = c⁻¹ • g.ricciEndoAt x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel n))
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsharp :
      ∀ ψ : Module.Dual ℝ (TM x),
        (LinearMap.BilinForm.toDual ((g.constSMul c hc).metricBilinAt x)
            ((g.constSMul c hc).metricBilinAt_nondegenerate x)).symm ψ =
          c⁻¹ • (LinearMap.BilinForm.toDual (g.metricBilinAt x)
            (g.metricBilinAt_nondegenerate x)).symm ψ := by
    intro ψ
    rw [LinearEquiv.symm_apply_eq]
    apply LinearMap.ext
    intro w
    rw [LinearMap.BilinForm.toDual_def, constSMul_metricBilinAt]
    simp only [LinearMap.smul_apply, smul_eq_mul, map_smul]
    have hbw : g.metricBilinAt x
        ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
          (g.metricBilinAt_nondegenerate x)).symm ψ) w = ψ w := by
      have h := LinearEquiv.apply_symm_apply
        (LinearMap.BilinForm.toDual (g.metricBilinAt x)
          (g.metricBilinAt_nondegenerate x)) ψ
      have h2 := congrArg (fun L : Module.Dual ℝ (TM x) ↦ L w) h
      simpa [LinearMap.BilinForm.toDual_def] using h2
    rw [hbw]
    field_simp [hcne]
  unfold ricciEndoAt
  apply LinearMap.ext
  intro u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
  rw [constSMul_ricciDualAt g c hc x]
  exact hsharp (CovariantDerivative.ricciDualAt g.leviCivita x u)

theorem constSMul_scalarAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    (g.constSMul c hc).scalarAt x = c⁻¹ * g.scalarAt x := by
  calc
    (g.constSMul c hc).scalarAt x =
        LinearMap.trace ℝ (TM x) ((g.constSMul c hc).ricciEndoAt x) := by
          rw [scalarAt_eq_trace_ricciEndoAt]
    _ = LinearMap.trace ℝ (TM x) (c⁻¹ • g.ricciEndoAt x) := by
          rw [constSMul_ricciEndoAt]
    _ = c⁻¹ * LinearMap.trace ℝ (TM x) (g.ricciEndoAt x) := by
          rw [map_smul]
          rfl
    _ = c⁻¹ * g.scalarAt x := by
          rw [scalarAt_eq_trace_ricciEndoAt]

theorem constSMul_ricciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    (g.constSMul c hc).ricciNormSqAt x =
      (c⁻¹) ^ 2 * g.ricciNormSqAt x := by
  let A : TM x →ₗ[ℝ] TM x := g.ricciEndoAt x
  have hcomp : (c⁻¹ • A) ∘ₗ (c⁻¹ • A) = (c⁻¹) ^ 2 • (A ∘ₗ A) := by
    ext v
    simp [A, LinearMap.comp_apply, smul_smul, pow_two]
  calc
    (g.constSMul c hc).ricciNormSqAt x =
        LinearMap.trace ℝ (TM x)
          ((g.constSMul c hc).ricciEndoAt x ∘ₗ
            (g.constSMul c hc).ricciEndoAt x) := rfl
    _ = LinearMap.trace ℝ (TM x) ((c⁻¹ • A) ∘ₗ (c⁻¹ • A)) := by
          rw [constSMul_ricciEndoAt]
    _ = LinearMap.trace ℝ (TM x) ((c⁻¹) ^ 2 • (A ∘ₗ A)) := by
          rw [hcomp]
    _ = (c⁻¹) ^ 2 * LinearMap.trace ℝ (TM x) (A ∘ₗ A) := by
          rw [map_smul]
          simp [smul_eq_mul]
    _ = (c⁻¹) ^ 2 * g.ricciNormSqAt x := rfl

theorem constSMul_tracelessRicciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) :
    (g.constSMul c hc).tracelessRicciNormSqAt x =
      (c⁻¹) ^ 2 * g.tracelessRicciNormSqAt x := by
  unfold tracelessRicciNormSqAt
  rw [constSMul_ricciNormSqAt, constSMul_scalarAt]
  ring

end ClosedSmoothRiemannianMetric

namespace ClosedSmoothRiemannianMetric

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

theorem constSMul_pinchedLimitPayload
    (g : ClosedSmoothRiemannianMetric 3 M) {c : ℝ} (hc : 0 < c)
    (htr : ∀ x, g.tracelessRicciNormSqAt x = 0)
    (hpos : ∃ x, 0 < g.scalarAt x) :
    (∀ x, (g.constSMul c hc).tracelessRicciNormSqAt x = 0) ∧
      (∃ x, 0 < (g.constSMul c hc).scalarAt x) := by
  constructor
  · intro x
    rw [constSMul_tracelessRicciNormSqAt, htr x, mul_zero]
  · rcases hpos with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [constSMul_scalarAt]
    exact mul_pos (inv_pos.mpr hc) hx

end ClosedSmoothRiemannianMetric
end Poincare
