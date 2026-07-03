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

/-- The scalar-normalized Ricci pinching quotient `|Ric|^2 / R^2`. -/
noncomputable def pinchingQuotientAt (x : M) : ℝ :=
  g.ricciNormSqAt x / (g.scalarAt x) ^ 2

/-- The definition of the scalar-normalized Ricci pinching quotient. -/
theorem pinchingQuotientAt_eq (x : M) :
    g.pinchingQuotientAt x = g.ricciNormSqAt x / (g.scalarAt x) ^ 2 :=
  rfl

/-- The Cauchy-Schwarz pinching gap `n |Ric|^2 - R^2`. -/
noncomputable def pinchingGapAt (x : M) : ℝ :=
  n * g.ricciNormSqAt x - (g.scalarAt x) ^ 2

/-- The squared traceless-Ricci norm in scalar trace form: `|Ric|^2 - R^2/n`. -/
noncomputable def tracelessRicciNormSqAt (x : M) : ℝ :=
  g.ricciNormSqAt x - (g.scalarAt x) ^ 2 / n

/-- The pinching gap is `n` times the trace-form traceless-Ricci norm. -/
theorem pinchingGapAt_eq_nat_mul_tracelessRicciNormSqAt
    (x : M) (hn : (n : ℝ) ≠ 0) :
    g.pinchingGapAt x = n * g.tracelessRicciNormSqAt x := by
  unfold pinchingGapAt tracelessRicciNormSqAt
  field_simp [hn]

/-- The trace-form traceless-Ricci norm is the pinching gap divided by `n`. -/
theorem tracelessRicciNormSqAt_eq_pinchingGapAt_div
    (x : M) (hn : (n : ℝ) ≠ 0) :
    g.tracelessRicciNormSqAt x = g.pinchingGapAt x / n := by
  rw [g.pinchingGapAt_eq_nat_mul_tracelessRicciNormSqAt x hn]
  field_simp [hn]

/-- The closed-manifold pinching gap is nonnegative. -/
theorem pinchingGapAt_nonneg (x : M) :
    0 ≤ g.pinchingGapAt x := by
  have h := g.scalarAt_sq_le_nat_mul_ricciNormSqAt x
  unfold pinchingGapAt
  linarith

/-- The trace-form traceless-Ricci norm is nonnegative in positive dimension. -/
theorem tracelessRicciNormSqAt_nonneg (x : M) (hn : 0 < (n : ℝ)) :
    0 ≤ g.tracelessRicciNormSqAt x := by
  have hgap := g.pinchingGapAt_nonneg x
  rw [g.tracelessRicciNormSqAt_eq_pinchingGapAt_div x hn.ne']
  exact div_nonneg hgap (le_of_lt hn)

/-- Positive scalar curvature is the natural nonzero-denominator domain for the quotient. -/
theorem scalarAt_sq_ne_zero_of_pos {x : M} (hR : 0 < g.scalarAt x) :
    (g.scalarAt x) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (ne_of_gt hR)

/-- On the positive-scalar domain, the pinching quotient is strictly positive. -/
theorem pinchingQuotientAt_pos_of_scalarAt_pos
    (x : M) (hR : 0 < g.scalarAt x) :
    0 < g.pinchingQuotientAt x := by
  have hpin := g.scalarAt_sq_le_nat_mul_ricciNormSqAt x
  have hR2 : 0 < (g.scalarAt x) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hR)
  have hnorm : 0 < g.ricciNormSqAt x := by
    have hmul : 0 < (n : ℝ) * g.ricciNormSqAt x := lt_of_lt_of_le hR2 hpin
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hmul) hn_nonneg
  exact div_pos hnorm hR2

/--
Concrete signed damping term built from the traceless-Ricci gap on the
positive-scalar domain.  This is the coefficient-pinned placeholder for the
negative quadratic term in the later 3D Hamilton pinching inequality.
-/
noncomputable def pinchingTracelessDampingAt (x : M) : ℝ :=
  -(2 / g.scalarAt x) * g.tracelessRicciNormSqAt x

/-- The traceless damping term is nonpositive when `R > 0`. -/
theorem pinchingTracelessDampingAt_nonpos
    (x : M) (hn : 0 < (n : ℝ)) (hR : 0 < g.scalarAt x) :
    g.pinchingTracelessDampingAt x ≤ 0 := by
  have htr : 0 ≤ g.tracelessRicciNormSqAt x :=
    g.tracelessRicciNormSqAt_nonneg x hn
  have hcoef : 0 ≤ 2 / g.scalarAt x := le_of_lt (div_pos (by norm_num) hR)
  unfold pinchingTracelessDampingAt
  nlinarith [mul_nonneg hcoef htr]

/-- A saturated pinching equality gives quotient `1/n` on the nonzero-scalar domain. -/
theorem pinchingQuotientAt_eq_inv_nat_of_scalarAt_sq_eq
    (x : M) (hn : (n : ℝ) ≠ 0) (hR : g.scalarAt x ≠ 0)
    (heq : g.scalarAt x ^ 2 = n * g.ricciNormSqAt x) :
    g.pinchingQuotientAt x = 1 / n := by
  have hR2 : (g.scalarAt x) ^ 2 ≠ 0 := pow_ne_zero 2 hR
  unfold pinchingQuotientAt
  rw [eq_div_iff hn]
  field_simp [hR2]
  linarith

/-- Einstein points have the quotient value `1/n` when the scalar curvature is nonzero. -/
theorem pinchingQuotientAt_eq_inv_nat_of_ricciEndoAt_eq_smul_id
    (x : M) (hnpos : 0 < (n : ℝ)) (hR : g.scalarAt x ≠ 0)
    (hEin : g.ricciEndoAt x = (g.scalarAt x / n) • LinearMap.id) :
    g.pinchingQuotientAt x = 1 / n :=
  g.pinchingQuotientAt_eq_inv_nat_of_scalarAt_sq_eq x hnpos.ne' hR
    (g.scalarAt_sq_eq_nat_mul_ricciNormSqAt_of_ricciEndoAt_eq_smul_id x hnpos hEin)

/-- Fiberwise Kulkarni-Nomizu product for two bilinear forms at one point. -/
noncomputable def tensorKulkarniNomizuAt (x : M)
    (h k : TM x → TM x → ℝ) (u w a b : TM x) : ℝ :=
  h u a * k w b + h w b * k u a - h u b * k w a - h w a * k u b

/--
The dimension-three Riemann-from-Ricci algebraic candidate in this project's
curvature sign convention: `Rm = (R/4) (g ⊘ g) - (Ric ⊘ g)`.
-/
noncomputable def riemannFromRicci3At (x : M) (u w a b : TM x) : ℝ :=
  (g.scalarAt x / 4) *
      tensorKulkarniNomizuAt (n := n) (M := M) x
        (fun p q ↦ g.inner x p q) (fun p q ↦ g.inner x p q) u w a b
    - tensorKulkarniNomizuAt (n := n) (M := M) x
        (fun p q ↦ g.ricciAt x p q) (fun p q ↦ g.inner x p q) u w a b

/-- A concrete Riemann tensor candidate is determined by Ricci in dimension three. -/
def RiemannDeterminedByRicci3At
    (x : M) (Rm : TM x → TM x → TM x → TM x → ℝ) : Prop :=
  ∀ u w a b : TM x, Rm u w a b = g.riemannFromRicci3At x u w a b

/--
Space-form coefficient validation for the 3D Ricci-to-Riemann candidate:
if `Ric = lambda g` and `R = 3 lambda`, then
`Rm_from_Ric = -(lambda/4) (g ⊘ g)`.
-/
theorem riemannFromRicci3At_spaceForm_coeff
    {x : M} {lam : ℝ}
    (hRic : ∀ u w : TM x, g.ricciAt x u w = lam * g.inner x u w)
    (hScal : g.scalarAt x = 3 * lam) (u w a b : TM x) :
    g.riemannFromRicci3At x u w a b =
      -(lam / 4) *
        tensorKulkarniNomizuAt (n := n) (M := M) x
          (fun p q ↦ g.inner x p q) (fun p q ↦ g.inner x p q) u w a b := by
  unfold riemannFromRicci3At tensorKulkarniNomizuAt
  simp only [hScal, hRic, mul_assoc]
  ring_nf

end RicciNorm

end ClosedSmoothRiemannianMetric

namespace PinchingAlgebra

/-- Squared Ricci norm for a diagonal 3D Ricci operator with entries `a,b,c`. -/
noncomputable def diagonalRicciNormSq3 (a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2

/-- Scalar curvature for a diagonal 3D Ricci operator with entries `a,b,c`. -/
noncomputable def diagonalScalar3 (a b c : ℝ) : ℝ :=
  a + b + c

/-- Scalar-normalized quotient for a diagonal 3D Ricci operator. -/
noncomputable def diagonalPinchingQuotient3 (a b c : ℝ) : ℝ :=
  diagonalRicciNormSq3 a b c / (diagonalScalar3 a b c) ^ 2

/-- Pinching gap for a diagonal 3D Ricci operator. -/
noncomputable def diagonalPinchingGap3 (a b c : ℝ) : ℝ :=
  3 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2

/-- Trace-form traceless-Ricci norm for a diagonal 3D Ricci operator. -/
noncomputable def diagonalTracelessRicciNormSq3 (a b c : ℝ) : ℝ :=
  diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2 / 3

/-- The 3D diagonal pinching gap is the sum of pairwise eigenvalue gaps. -/
theorem diagonalPinchingGap3_eq_pairwise (a b c : ℝ) :
    diagonalPinchingGap3 a b c =
      (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
  unfold diagonalPinchingGap3 diagonalRicciNormSq3 diagonalScalar3
  ring

/-- The diagonal traceless norm is one third of the pairwise eigenvalue gap sum. -/
theorem diagonalTracelessRicciNormSq3_eq_pairwise_div_three (a b c : ℝ) :
    diagonalTracelessRicciNormSq3 a b c =
      ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 3 := by
  unfold diagonalTracelessRicciNormSq3 diagonalRicciNormSq3 diagonalScalar3
  ring

/-- The 3D space-form diagonal quotient is exactly `1/3`. -/
theorem diagonalPinchingQuotient3_spaceForm {lam : ℝ} (hlam : lam ≠ 0) :
    diagonalPinchingQuotient3 lam lam lam = 1 / 3 := by
  unfold diagonalPinchingQuotient3 diagonalRicciNormSq3 diagonalScalar3
  field_simp [hlam]
  ring

/-- Non-Einstein diagonal test pattern `(1,1,2)`: quotient coefficient `3/8`. -/
theorem diagonalPinchingQuotient3_one_one_two :
    diagonalPinchingQuotient3 1 1 2 = 3 / 8 := by
  norm_num [diagonalPinchingQuotient3, diagonalRicciNormSq3, diagonalScalar3]

/-- Non-Einstein diagonal test pattern `(1,1,2)`: pinching gap coefficient `2`. -/
theorem diagonalPinchingGap3_one_one_two :
    diagonalPinchingGap3 1 1 2 = 2 := by
  norm_num [diagonalPinchingGap3, diagonalRicciNormSq3, diagonalScalar3]

/-- Non-Einstein diagonal test pattern `(1,1,2)`: traceless norm coefficient `2/3`. -/
theorem diagonalTracelessRicciNormSq3_one_one_two :
    diagonalTracelessRicciNormSq3 1 1 2 = 2 / 3 := by
  norm_num [diagonalTracelessRicciNormSq3, diagonalRicciNormSq3, diagonalScalar3]

/-- The 3D Ricci-to-Riemann candidate on an orthonormal diagonal frame, sectional `12`. -/
noncomputable def diagonalRiemannFromRicci3Section12 (a b c : ℝ) : ℝ :=
  (a + b + c) / 2 - (a + b)

/-- The 3D Ricci-to-Riemann candidate on an orthonormal diagonal frame, sectional `13`. -/
noncomputable def diagonalRiemannFromRicci3Section13 (a b c : ℝ) : ℝ :=
  (a + b + c) / 2 - (a + c)

/-- The 3D Ricci-to-Riemann candidate on an orthonormal diagonal frame, sectional `23`. -/
noncomputable def diagonalRiemannFromRicci3Section23 (a b c : ℝ) : ℝ :=
  (a + b + c) / 2 - (b + c)

theorem diagonalRiemannFromRicci3Section12_eq (a b c : ℝ) :
    diagonalRiemannFromRicci3Section12 a b c = (c - a - b) / 2 := by
  unfold diagonalRiemannFromRicci3Section12
  ring

theorem diagonalRiemannFromRicci3Section13_eq (a b c : ℝ) :
    diagonalRiemannFromRicci3Section13 a b c = (b - a - c) / 2 := by
  unfold diagonalRiemannFromRicci3Section13
  ring

theorem diagonalRiemannFromRicci3Section23_eq (a b c : ℝ) :
    diagonalRiemannFromRicci3Section23 a b c = (a - b - c) / 2 := by
  unfold diagonalRiemannFromRicci3Section23
  ring

/-- Space-form diagonal validation: every sectional entry is `-lambda/2`. -/
theorem diagonalRiemannFromRicci3Section_spaceForm (lam : ℝ) :
    diagonalRiemannFromRicci3Section12 lam lam lam = -lam / 2 ∧
      diagonalRiemannFromRicci3Section13 lam lam lam = -lam / 2 ∧
      diagonalRiemannFromRicci3Section23 lam lam lam = -lam / 2 := by
  simp [diagonalRiemannFromRicci3Section12, diagonalRiemannFromRicci3Section13,
    diagonalRiemannFromRicci3Section23]
  ring_nf

/-- Non-Einstein diagonal validation for `(1,1,2)`: sectional coefficients `0,-1,-1`. -/
theorem diagonalRiemannFromRicci3Section_one_one_two :
    diagonalRiemannFromRicci3Section12 1 1 2 = 0 ∧
      diagonalRiemannFromRicci3Section13 1 1 2 = -1 ∧
      diagonalRiemannFromRicci3Section23 1 1 2 = -1 := by
  norm_num [diagonalRiemannFromRicci3Section12, diagonalRiemannFromRicci3Section13,
    diagonalRiemannFromRicci3Section23]

/--
Diagonal `2 Rm(Ric,.)` entry in the first Ricci eigendirection, computed from
the pinned 3D curvature decomposition.
-/
noncomputable def diagonalTwoLichnerowiczFromRicci3Entry1 (a b c : ℝ) : ℝ :=
  2 * (b * (-diagonalRiemannFromRicci3Section12 a b c)
    + c * (-diagonalRiemannFromRicci3Section13 a b c))

/--
Diagonal `2 Rm(Ric,.)` entry in the second Ricci eigendirection, computed from
the pinned 3D curvature decomposition.
-/
noncomputable def diagonalTwoLichnerowiczFromRicci3Entry2 (a b c : ℝ) : ℝ :=
  2 * (a * (-diagonalRiemannFromRicci3Section12 a b c)
    + c * (-diagonalRiemannFromRicci3Section23 a b c))

/--
Diagonal `2 Rm(Ric,.)` entry in the third Ricci eigendirection, computed from
the pinned 3D curvature decomposition.
-/
noncomputable def diagonalTwoLichnerowiczFromRicci3Entry3 (a b c : ℝ) : ℝ :=
  2 * (a * (-diagonalRiemannFromRicci3Section13 a b c)
    + b * (-diagonalRiemannFromRicci3Section23 a b c))

/-- Pure 3D Ricci-quadratic formula for the first `2 Rm(Ric,.)` entry. -/
noncomputable def diagonalTwoLichnerowiczPure3Entry1 (a b c : ℝ) : ℝ :=
  3 * diagonalScalar3 a b c * a - 4 * a ^ 2
    + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2

/-- Pure 3D Ricci-quadratic formula for the second `2 Rm(Ric,.)` entry. -/
noncomputable def diagonalTwoLichnerowiczPure3Entry2 (a b c : ℝ) : ℝ :=
  3 * diagonalScalar3 a b c * b - 4 * b ^ 2
    + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2

/-- Pure 3D Ricci-quadratic formula for the third `2 Rm(Ric,.)` entry. -/
noncomputable def diagonalTwoLichnerowiczPure3Entry3 (a b c : ℝ) : ℝ :=
  3 * diagonalScalar3 a b c * c - 4 * c ^ 2
    + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2

theorem diagonalTwoLichnerowiczFromRicci3Entry1_eq_pure (a b c : ℝ) :
    diagonalTwoLichnerowiczFromRicci3Entry1 a b c =
      diagonalTwoLichnerowiczPure3Entry1 a b c := by
  unfold diagonalTwoLichnerowiczFromRicci3Entry1 diagonalTwoLichnerowiczPure3Entry1
    diagonalRiemannFromRicci3Section12 diagonalRiemannFromRicci3Section13
    diagonalRicciNormSq3 diagonalScalar3
  ring

theorem diagonalTwoLichnerowiczFromRicci3Entry2_eq_pure (a b c : ℝ) :
    diagonalTwoLichnerowiczFromRicci3Entry2 a b c =
      diagonalTwoLichnerowiczPure3Entry2 a b c := by
  unfold diagonalTwoLichnerowiczFromRicci3Entry2 diagonalTwoLichnerowiczPure3Entry2
    diagonalRiemannFromRicci3Section12 diagonalRiemannFromRicci3Section23
    diagonalRicciNormSq3 diagonalScalar3
  ring

theorem diagonalTwoLichnerowiczFromRicci3Entry3_eq_pure (a b c : ℝ) :
    diagonalTwoLichnerowiczFromRicci3Entry3 a b c =
      diagonalTwoLichnerowiczPure3Entry3 a b c := by
  unfold diagonalTwoLichnerowiczFromRicci3Entry3 diagonalTwoLichnerowiczPure3Entry3
    diagonalRiemannFromRicci3Section13 diagonalRiemannFromRicci3Section23
    diagonalRicciNormSq3 diagonalScalar3
  ring

/--
After subtracting `2 Ric^2`, the diagonal Ricci-evolution reaction in the
first eigendirection is `3 R Ric - 6 Ric^2 + (2 |Ric|^2 - R^2) g`.
-/
noncomputable def diagonalRicciEvolutionReaction3Entry1 (a b c : ℝ) : ℝ :=
  diagonalTwoLichnerowiczPure3Entry1 a b c - 2 * a ^ 2

/--
After subtracting `2 Ric^2`, the diagonal Ricci-evolution reaction in the
second eigendirection is `3 R Ric - 6 Ric^2 + (2 |Ric|^2 - R^2) g`.
-/
noncomputable def diagonalRicciEvolutionReaction3Entry2 (a b c : ℝ) : ℝ :=
  diagonalTwoLichnerowiczPure3Entry2 a b c - 2 * b ^ 2

/--
After subtracting `2 Ric^2`, the diagonal Ricci-evolution reaction in the
third eigendirection is `3 R Ric - 6 Ric^2 + (2 |Ric|^2 - R^2) g`.
-/
noncomputable def diagonalRicciEvolutionReaction3Entry3 (a b c : ℝ) : ℝ :=
  diagonalTwoLichnerowiczPure3Entry3 a b c - 2 * c ^ 2

theorem diagonalRicciEvolutionReaction3Entry1_eq (a b c : ℝ) :
    diagonalRicciEvolutionReaction3Entry1 a b c =
      3 * diagonalScalar3 a b c * a - 6 * a ^ 2
        + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2 := by
  unfold diagonalRicciEvolutionReaction3Entry1 diagonalTwoLichnerowiczPure3Entry1
  ring

theorem diagonalRicciEvolutionReaction3Entry2_eq (a b c : ℝ) :
    diagonalRicciEvolutionReaction3Entry2 a b c =
      3 * diagonalScalar3 a b c * b - 6 * b ^ 2
        + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2 := by
  unfold diagonalRicciEvolutionReaction3Entry2 diagonalTwoLichnerowiczPure3Entry2
  ring

theorem diagonalRicciEvolutionReaction3Entry3_eq (a b c : ℝ) :
    diagonalRicciEvolutionReaction3Entry3 a b c =
      3 * diagonalScalar3 a b c * c - 6 * c ^ 2
        + 2 * diagonalRicciNormSq3 a b c - (diagonalScalar3 a b c) ^ 2 := by
  unfold diagonalRicciEvolutionReaction3Entry3 diagonalTwoLichnerowiczPure3Entry3
  ring

/-- Space-form validation: `2 Rm(Ric,.) = 2 lambda^2 g`. -/
theorem diagonalTwoLichnerowiczFromRicci3_spaceForm (lam : ℝ) :
    diagonalTwoLichnerowiczFromRicci3Entry1 lam lam lam = 2 * lam ^ 2 ∧
      diagonalTwoLichnerowiczFromRicci3Entry2 lam lam lam = 2 * lam ^ 2 ∧
      diagonalTwoLichnerowiczFromRicci3Entry3 lam lam lam = 2 * lam ^ 2 := by
  simp [diagonalTwoLichnerowiczFromRicci3Entry1,
    diagonalTwoLichnerowiczFromRicci3Entry2, diagonalTwoLichnerowiczFromRicci3Entry3,
    diagonalRiemannFromRicci3Section12, diagonalRiemannFromRicci3Section13,
    diagonalRiemannFromRicci3Section23]
  ring_nf

/-- Space-form validation: the Ricci-evolution reaction vanishes. -/
theorem diagonalRicciEvolutionReaction3_spaceForm (lam : ℝ) :
    diagonalRicciEvolutionReaction3Entry1 lam lam lam = 0 ∧
      diagonalRicciEvolutionReaction3Entry2 lam lam lam = 0 ∧
      diagonalRicciEvolutionReaction3Entry3 lam lam lam = 0 := by
  simp [diagonalRicciEvolutionReaction3Entry1, diagonalRicciEvolutionReaction3Entry2,
    diagonalRicciEvolutionReaction3Entry3, diagonalTwoLichnerowiczPure3Entry1,
    diagonalTwoLichnerowiczPure3Entry2, diagonalTwoLichnerowiczPure3Entry3,
    diagonalRicciNormSq3, diagonalScalar3]
  ring_nf

/-- Non-Einstein `(1,1,2)` validation: every `2 Rm(Ric,.)` diagonal entry is `4`. -/
theorem diagonalTwoLichnerowiczFromRicci3_one_one_two :
    diagonalTwoLichnerowiczFromRicci3Entry1 1 1 2 = 4 ∧
      diagonalTwoLichnerowiczFromRicci3Entry2 1 1 2 = 4 ∧
      diagonalTwoLichnerowiczFromRicci3Entry3 1 1 2 = 4 := by
  norm_num [diagonalTwoLichnerowiczFromRicci3Entry1,
    diagonalTwoLichnerowiczFromRicci3Entry2, diagonalTwoLichnerowiczFromRicci3Entry3,
    diagonalRiemannFromRicci3Section12, diagonalRiemannFromRicci3Section13,
    diagonalRiemannFromRicci3Section23]

/-- Non-Einstein `(1,1,2)` validation: the reaction entries are `2,2,-4`. -/
theorem diagonalRicciEvolutionReaction3_one_one_two :
    diagonalRicciEvolutionReaction3Entry1 1 1 2 = 2 ∧
      diagonalRicciEvolutionReaction3Entry2 1 1 2 = 2 ∧
      diagonalRicciEvolutionReaction3Entry3 1 1 2 = -4 := by
  norm_num [diagonalRicciEvolutionReaction3Entry1, diagonalRicciEvolutionReaction3Entry2,
    diagonalRicciEvolutionReaction3Entry3, diagonalTwoLichnerowiczPure3Entry1,
    diagonalTwoLichnerowiczPure3Entry2, diagonalTwoLichnerowiczPure3Entry3,
    diagonalRicciNormSq3, diagonalScalar3]

end PinchingAlgebra

end Poincare
