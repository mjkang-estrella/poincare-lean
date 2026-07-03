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

/-- The Euclidean three-dimensional fiber used by the algebraic Weyl-vanishing lemma. -/
abbrev Euclidean3 : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- A bundled four-linear real form on the standard three-dimensional Euclidean fiber. -/
abbrev FourLinearEuclidean3 : Type :=
  Euclidean3 →ₗ[ℝ] Euclidean3 →ₗ[ℝ] Euclidean3 →ₗ[ℝ] Euclidean3 →ₗ[ℝ] ℝ

/-- A bundled four-linear real form on a real vector space. -/
abbrev FourLinear (V : Type) [AddCommGroup V] [Module ℝ V] : Type :=
  V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ

/-- The standard orthonormal basis vector in the Euclidean three-dimensional fiber. -/
noncomputable def euclidean3Basis (i : Fin 3) : Euclidean3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ) i

/--
Four-linear forms on the standard three-dimensional Euclidean fiber are determined by
their values on the four standard basis slots.
-/
theorem fourLinearEuclidean3_basis_ext {F G : FourLinearEuclidean3}
    (h : ∀ i j k l : Fin 3,
      F (euclidean3Basis i) (euclidean3Basis j) (euclidean3Basis k) (euclidean3Basis l) =
        G (euclidean3Basis i) (euclidean3Basis j) (euclidean3Basis k)
          (euclidean3Basis l)) :
    F = G := by
  apply Module.Basis.ext (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro i
  apply Module.Basis.ext (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro j
  apply Module.Basis.ext (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro k
  apply Module.Basis.ext (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro l
  exact h i j k l

/-- A four-linear form is zero if all four-slot standard-basis coefficients vanish. -/
theorem fourLinearEuclidean3_eq_zero_of_basis (F : FourLinearEuclidean3)
    (h : ∀ i j k l : Fin 3,
      F (euclidean3Basis i) (euclidean3Basis j) (euclidean3Basis k) (euclidean3Basis l) =
        0) :
    F = 0 := by
  apply fourLinearEuclidean3_basis_ext
  intro i j k l
  simpa using h i j k l

set_option maxHeartbeats 5000000 in
/--
In dimension three, a four-linear form with the algebraic Riemann symmetries and
zero Ricci trace is identically zero.

The trace hypothesis is stated in the standard orthonormal basis of
`Euclidean3`: `sum_i W(e_i, u, e_i, w) = 0`.
-/
theorem fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace
    (W : FourLinearEuclidean3)
    (hFirstPair : ∀ x y z t : Euclidean3, W x y z t = -W y x z t)
    (hSecondPair : ∀ x y z t : Euclidean3, W x y z t = -W x y t z)
    (hPairExchange : ∀ x y z t : Euclidean3, W x y z t = W z t x y)
    (hBianchi : ∀ x y z t : Euclidean3, W x y z t + W y z x t + W z x y t = 0)
    (hRicciTrace : ∀ u w : Euclidean3,
      (∑ i : Fin 3, W (euclidean3Basis i) u (euclidean3Basis i) w) = 0) :
    W = 0 := by
  let e0 := euclidean3Basis (0 : Fin 3)
  let e1 := euclidean3Basis (1 : Fin 3)
  let e2 := euclidean3Basis (2 : Fin 3)
  have hdiag12 : ∀ a c d : Euclidean3, W a a c d = 0 := by
    intro a c d
    have h := hFirstPair a a c d
    linarith
  have hdiag34 : ∀ a b c : Euclidean3, W a b c c = 0 := by
    intro a b c
    have h := hSecondPair a b c c
    linarith
  have hB : W e0 e1 e0 e2 = 0 := by
    have ht := hRicciTrace e1 e2
    rw [Fin.sum_univ_three] at ht
    have h11 : W e1 e1 e1 e2 = 0 := hdiag12 e1 e1 e2
    have h22 : W e2 e1 e2 e2 = 0 := hdiag34 e2 e1 e2
    linarith
  have hC : W e0 e1 e1 e2 = 0 := by
    have ht := hRicciTrace e0 e2
    rw [Fin.sum_univ_three] at ht
    have h00 : W e0 e0 e0 e2 = 0 := hdiag12 e0 e0 e2
    have h22 : W e2 e0 e2 e2 = 0 := hdiag34 e2 e0 e2
    have h10 : W e1 e0 e1 e2 = -W e0 e1 e1 e2 :=
      hFirstPair e1 e0 e1 e2
    have hBianchiUse := hBianchi e0 e1 e2 e1
    linarith [hBianchiUse]
  have hE : W e0 e2 e1 e2 = 0 := by
    have ht := hRicciTrace e0 e1
    rw [Fin.sum_univ_three] at ht
    have h00 : W e0 e0 e0 e1 = 0 := hdiag12 e0 e0 e1
    have h11 : W e1 e0 e1 e1 = 0 := hdiag34 e1 e0 e1
    have h20a : W e2 e0 e2 e1 = -W e0 e2 e2 e1 :=
      hFirstPair e2 e0 e2 e1
    have h20b : W e0 e2 e2 e1 = -W e0 e2 e1 e2 :=
      hSecondPair e0 e2 e2 e1
    linarith
  have hAD : W e0 e1 e0 e1 + W e0 e2 e0 e2 = 0 := by
    have ht := hRicciTrace e0 e0
    rw [Fin.sum_univ_three] at ht
    have h00 : W e0 e0 e0 e0 = 0 := hdiag12 e0 e0 e0
    have h10a : W e1 e0 e1 e0 = -W e0 e1 e1 e0 :=
      hFirstPair e1 e0 e1 e0
    have h10b : W e0 e1 e1 e0 = -W e0 e1 e0 e1 :=
      hSecondPair e0 e1 e1 e0
    have h20a : W e2 e0 e2 e0 = -W e0 e2 e2 e0 :=
      hFirstPair e2 e0 e2 e0
    have h20b : W e0 e2 e2 e0 = -W e0 e2 e0 e2 :=
      hSecondPair e0 e2 e2 e0
    linarith
  have hAF : W e0 e1 e0 e1 + W e1 e2 e1 e2 = 0 := by
    have ht := hRicciTrace e1 e1
    rw [Fin.sum_univ_three] at ht
    have h11 : W e1 e1 e1 e1 = 0 := hdiag12 e1 e1 e1
    have h21a : W e2 e1 e2 e1 = -W e1 e2 e2 e1 :=
      hFirstPair e2 e1 e2 e1
    have h21b : W e1 e2 e2 e1 = -W e1 e2 e1 e2 :=
      hSecondPair e1 e2 e2 e1
    linarith
  have hDF : W e0 e2 e0 e2 + W e1 e2 e1 e2 = 0 := by
    have ht := hRicciTrace e2 e2
    rw [Fin.sum_univ_three] at ht
    have h22 : W e2 e2 e2 e2 = 0 := hdiag12 e2 e2 e2
    linarith
  have hA : W e0 e1 e0 e1 = 0 := by linarith
  have hD : W e0 e2 e0 e2 = 0 := by linarith
  have hF : W e1 e2 e1 e2 = 0 := by linarith
  apply fourLinearEuclidean3_eq_zero_of_basis
  intro i j k l
  let ei := euclidean3Basis i
  let ej := euclidean3Basis j
  let ek := euclidean3Basis k
  let el := euclidean3Basis l
  have h12a := hFirstPair ei ej ek el
  have h12b := hFirstPair ej ei ek el
  have h12c := hFirstPair ei ej el ek
  have h12d := hFirstPair ej ei el ek
  have h12e := hFirstPair ek el ei ej
  have h12f := hFirstPair el ek ei ej
  have h12g := hFirstPair ek el ej ei
  have h12h := hFirstPair el ek ej ei
  have h34a := hSecondPair ei ej ek el
  have h34b := hSecondPair ej ei ek el
  have h34c := hSecondPair ei ej el ek
  have h34d := hSecondPair ej ei el ek
  have h34e := hSecondPair ek el ei ej
  have h34f := hSecondPair el ek ei ej
  have h34g := hSecondPair ek el ej ei
  have h34h := hSecondPair el ek ej ei
  have hpa := hPairExchange ei ej ek el
  have hpb := hPairExchange ej ei ek el
  have hpc := hPairExchange ei ej el ek
  have hpd := hPairExchange ej ei el ek
  have hpe := hPairExchange ek el ei ej
  have hpf := hPairExchange el ek ei ej
  have hpg := hPairExchange ek el ej ei
  have hph := hPairExchange el ek ej ei
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [ei, ej, ek, el, e0, e1, e2] at * <;>
    simp at * <;>
    linarith [hA, hB, hC, hD, hE, hF,
      h12a, h12b, h12c, h12d, h12e, h12f, h12g, h12h,
      h34a, h34b, h34c, h34d, h34e, h34f, h34g, h34h,
      hpa, hpb, hpc, hpd, hpe, hpf, hpg, hph]

/-- Pointwise form of `fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace`. -/
theorem fourLinearEuclidean3_apply_eq_zero_of_riemann_symm_and_trace
    (W : FourLinearEuclidean3)
    (hFirstPair : ∀ x y z t : Euclidean3, W x y z t = -W y x z t)
    (hSecondPair : ∀ x y z t : Euclidean3, W x y z t = -W x y t z)
    (hPairExchange : ∀ x y z t : Euclidean3, W x y z t = W z t x y)
    (hBianchi : ∀ x y z t : Euclidean3, W x y z t + W y z x t + W z x y t = 0)
    (hRicciTrace : ∀ u w : Euclidean3,
      (∑ i : Fin 3, W (euclidean3Basis i) u (euclidean3Basis i) w) = 0)
    (x y z t : Euclidean3) :
    W x y z t = 0 := by
  have hW := fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace W
    hFirstPair hSecondPair hPairExchange hBianchi hRicciTrace
  rw [hW]
  rfl

/--
Transport the Euclidean three-dimensional Weyl-vanishing lemma across an
orthonormal basis of an arbitrary real inner-product space.
-/
theorem fourLinear_eq_zero_of_orthonormal_riemann_symm_and_trace
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis (Fin 3) ℝ V)
    (W : FourLinear V)
    (hFirstPair : ∀ x y z t : V, W x y z t = -W y x z t)
    (hSecondPair : ∀ x y z t : V, W x y z t = -W x y t z)
    (hPairExchange : ∀ x y z t : V, W x y z t = W z t x y)
    (hBianchi : ∀ x y z t : V, W x y z t + W y z x t + W z x y t = 0)
    (hRicciTrace : ∀ u w : V, (∑ i : Fin 3, W (b i) u (b i) w) = 0) :
    W = 0 := by
  classical
  let Wb : FourLinearEuclidean3 :=
    { toFun := fun x =>
        { toFun := fun y =>
            { toFun := fun z =>
                { toFun := fun t => W (b.repr.symm x) (b.repr.symm y)
                    (b.repr.symm z) (b.repr.symm t)
                  map_add' := by
                    intro t₁ t₂
                    simp
                  map_smul' := by
                    intro c t
                    simp }
              map_add' := by
                intro z₁ z₂
                apply LinearMap.ext
                intro t
                simp
              map_smul' := by
                intro c z
                apply LinearMap.ext
                intro t
                simp }
          map_add' := by
            intro y₁ y₂
            apply LinearMap.ext
            intro z
            apply LinearMap.ext
            intro t
            simp
          map_smul' := by
            intro c y
            apply LinearMap.ext
            intro z
            apply LinearMap.ext
            intro t
            simp }
      map_add' := by
        intro x₁ x₂
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        apply LinearMap.ext
        intro t
        simp
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        apply LinearMap.ext
        intro t
        simp }
  have hFirstPair' :
      ∀ x y z t : Euclidean3, Wb x y z t = -Wb y x z t := by
    intro x y z t
    exact hFirstPair _ _ _ _
  have hSecondPair' :
      ∀ x y z t : Euclidean3, Wb x y z t = -Wb x y t z := by
    intro x y z t
    exact hSecondPair _ _ _ _
  have hPairExchange' :
      ∀ x y z t : Euclidean3, Wb x y z t = Wb z t x y := by
    intro x y z t
    exact hPairExchange _ _ _ _
  have hBianchi' :
      ∀ x y z t : Euclidean3, Wb x y z t + Wb y z x t + Wb z x y t = 0 := by
    intro x y z t
    exact hBianchi _ _ _ _
  have hRicciTrace' :
      ∀ u w : Euclidean3,
        (∑ i : Fin 3, Wb (euclidean3Basis i) u (euclidean3Basis i) w) = 0 := by
    intro u w
    simpa [Wb, euclidean3Basis] using
      hRicciTrace (b.repr.symm u) (b.repr.symm w)
  have hWb := fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace Wb
    hFirstPair' hSecondPair' hPairExchange' hBianchi' hRicciTrace'
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro t
  have hzero : Wb (b.repr x) (b.repr y) (b.repr z) (b.repr t) = 0 := by
    rw [hWb]
    rfl
  simpa [Wb] using hzero

/--
Trace-convention bridge for an orthonormal frame: a zero contraction in the
last slot, `Σᵢ W(eᵢ,u,w,eᵢ)`, is equivalent to the Ricci trace used by the
Euclidean vanishing lemma once the second-pair antisymmetry is available.
-/
theorem fourLinear_eq_zero_of_orthonormal_riemann_symm_and_last_trace
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : OrthonormalBasis (Fin 3) ℝ V)
    (W : FourLinear V)
    (hFirstPair : ∀ x y z t : V, W x y z t = -W y x z t)
    (hSecondPair : ∀ x y z t : V, W x y z t = -W x y t z)
    (hPairExchange : ∀ x y z t : V, W x y z t = W z t x y)
    (hBianchi : ∀ x y z t : V, W x y z t + W y z x t + W z x y t = 0)
    (hLastTrace : ∀ u w : V, (∑ i : Fin 3, W (b i) u w (b i)) = 0) :
    W = 0 := by
  refine fourLinear_eq_zero_of_orthonormal_riemann_symm_and_trace b W
    hFirstPair hSecondPair hPairExchange hBianchi ?_
  intro u w
  calc
    (∑ i : Fin 3, W (b i) u (b i) w)
        = ∑ i : Fin 3, -W (b i) u w (b i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact hSecondPair (b i) u (b i) w
    _ = -(∑ i : Fin 3, W (b i) u w (b i)) := by
          rw [Finset.sum_neg_distrib]
    _ = 0 := by
          rw [hLastTrace u w]
          ring

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
