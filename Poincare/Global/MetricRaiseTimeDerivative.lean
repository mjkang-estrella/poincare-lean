import Poincare.Global.ScalarVariation

/-!
# Time derivative of the inverse metric

This file discharges the standalone derivative hypothesis for
`metricRaiseContinuousAt`.  On one fixed tangent fiber, the metric-raising map
is reconstructed from the inverse Gram matrix in a finite basis.  Pointwise
time differentiability of the metric entries therefore differentiates the
actual continuous-linear inverse metric, with derivative
`-g⁻¹ ∘ h^♭ ∘ g⁻¹`.
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

omit [T2Space M] in
/-- A finite matrix-valued path is differentiable when every entry is. -/
theorem differentiableAt_matrix_det_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀) :
    DifferentiableAt ℝ (fun t ↦ (A t).det) t₀ := by
  classical
  rw [show (fun t : ℝ ↦ (A t).det) =
      fun t : ℝ ↦ ∑ σ : Equiv.Perm ι,
        ((↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A t (σ i) i) by
    funext t
    rw [Matrix.det_apply']]
  have hsum : DifferentiableAt ℝ
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
        fun t : ℝ ↦ (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A t (σ i) i) t₀ := by
    refine DifferentiableAt.sum (u := (Finset.univ : Finset (Equiv.Perm ι))) ?_
    intro σ _hσ
    have hprod : DifferentiableAt ℝ
        (∏ i ∈ (Finset.univ : Finset ι), fun t : ℝ ↦ A t (σ i) i) t₀ := by
      refine DifferentiableAt.finsetProd (u := (Finset.univ : Finset ι)) ?_
      intro i _hi
      exact hA (σ i) i
    have hprod' : DifferentiableAt ℝ (fun t : ℝ ↦ ∏ i, A t (σ i) i) t₀ :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by simp)
    have hconst : DifferentiableAt ℝ
        (fun _ : ℝ ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) t₀ := differentiableAt_const _
    simpa using hconst.mul hprod'
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by simp)

omit [T2Space M] in
/-- An adjugate entry of a finite matrix-valued path is differentiable when
all matrix entries are. -/
theorem differentiableAt_matrix_adjugate_entry_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀)
    (i j : ι) :
    DifferentiableAt ℝ (fun t ↦ (A t).adjugate i j) t₀ := by
  classical
  let row : ι → ℝ := Pi.single i (1 : ℝ)
  let B : ℝ → Matrix ι ι ℝ := fun t ↦ (A t).updateRow j row
  have hentries : ∀ a b,
      DifferentiableAt ℝ (fun t ↦ B t a b) t₀ := by
    intro a b
    by_cases ha : a = j
    · subst a
      simpa [B, Matrix.updateRow] using
        (differentiableAt_const t₀ (row b))
    · simpa [B, Matrix.updateRow, ha] using hA a b
  have hdet : DifferentiableAt ℝ (fun t ↦ (B t).det) t₀ :=
    differentiableAt_matrix_det_of_entries hentries
  exact hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ by
    simp [B, row, Matrix.adjugate_apply])

omit [T2Space M] in
/-- An inverse-matrix entry is differentiable at an invertible base matrix. -/
theorem differentiableAt_matrix_inv_entry_of_entries
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun t ↦ A t i j) t₀)
    (hdet : (A t₀).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun t ↦ (A t)⁻¹ i j) t₀ := by
  have hdetDiff : DifferentiableAt ℝ (fun t ↦ (A t).det) t₀ :=
    differentiableAt_matrix_det_of_entries hA
  have hdetInv : DifferentiableAt ℝ (fun t ↦ ((A t).det)⁻¹) t₀ :=
    hdetDiff.inv hdet
  have hadj : DifferentiableAt ℝ (fun t ↦ (A t).adjugate i j) t₀ :=
    differentiableAt_matrix_adjugate_entry_of_entries hA i j
  exact (hdetInv.mul hadj).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ by simp [Matrix.inv_def])

/-- Every entry of the time-dependent Gram matrix on one fixed tangent fiber
is differentiable under `TimeDifferentiableAt`. -/
theorem gramMatrix_time_entry_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    DifferentiableAt ℝ (fun t ↦
      gramMatrix (gt t) x x i j) t₀ := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [gramMatrix, b] using hgt (b i) (b j)

/-- Every inverse-Gram entry on one fixed tangent fiber is differentiable in
time. -/
theorem gramMatrix_time_inv_entry_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    DifferentiableAt ℝ (fun t ↦
      (gramMatrix (gt t) x x)⁻¹ i j) t₀ := by
  apply differentiableAt_matrix_inv_entry_of_entries
    (fun a b ↦ gramMatrix_time_entry_differentiableAt hgt a b)
  exact gramMatrix_at_base_det_ne_zero
    (g := gt t₀) (x := x)

/-- Differentiability of an operator-valued real path can be checked after
applying every fixed input when the operator domain is finite-dimensional. -/
theorem differentiableAt_clm_path_of_apply
    {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ → V →L[ℝ] F} {t₀ : ℝ}
    (h : ∀ v : V, DifferentiableAt ℝ (fun t ↦ Φ t v) t₀) :
    DifferentiableAt ℝ Φ t₀ := by
  let b := Module.finBasis ℝ V
  let coordC : Fin (Module.finrank ℝ V) → (V →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hrepr : ∀ ρ : V →L[ℝ] F,
      ρ = ∑ i, (coordC i).smulRight (ρ (b i)) := by
    intro ρ
    ext v
    have hv := b.sum_repr v
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show coordC i v = b.coord i v from rfl, Module.Basis.coord_apply]
  have hfun : Φ = fun t ↦ ∑ i, (coordC i).smulRight (Φ t (b i)) := by
    funext t
    exact hrepr (Φ t)
  rw [hfun]
  refine DifferentiableAt.fun_sum ?_
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ V F (coordC i)).differentiableAt
    |>.comp t₀ (h (b i))

/-- The raised image of a fixed covector is differentiable in time. -/
theorem metricRaiseContinuousAt_apply_differentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) (φ : TM x →L[ℝ] ℝ) :
    DifferentiableAt ℝ
      (fun t ↦ (gt t).metricRaiseContinuousAt x φ) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let coordC : Fin (Module.finrank ℝ (TM x)) → (TM x →L[ℝ] ℝ) :=
    fun i ↦ LinearMap.toContinuousLinearMap (b.coord i)
  have hcoord : ∀ i,
      DifferentiableAt ℝ
        (fun t ↦ (gt t).metricRaiseContinuousAt x (coordC i)) t₀ := by
    intro i
    have hfun :
        (fun t ↦ (gt t).metricRaiseContinuousAt x (coordC i)) =
          fun t ↦ ∑ j,
            (gramMatrix (gt t) x x)⁻¹ i j • b j := by
      funext t
      rw [← metricDualVectorAt_basisCoord_eq_metricRaiseContinuousAt
        (g := gt t) (x := x) b i]
      exact metricDualVectorAt_finBasis_coord_eq_sum_gram_inv
        (g := gt t) (x := x) i
    rw [hfun]
    refine DifferentiableAt.fun_sum ?_
    intro j _
    exact (gramMatrix_time_inv_entry_differentiableAt hgt i j).smul_const (b j)
  have hφ : φ = ∑ i, φ (b i) • coordC i := by
    ext v
    have hv := b.sum_repr v
    conv_lhs => rw [← hv]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show coordC i v = b.coord i v from rfl, Module.Basis.coord_apply]
    ring
  have hfun :
      (fun t ↦ (gt t).metricRaiseContinuousAt x φ) =
        fun t ↦ ∑ i, φ (b i) •
          (gt t).metricRaiseContinuousAt x (coordC i) := by
    funext t
    conv_lhs => rw [hφ]
    rw [map_sum]
    simp
  rw [hfun]
  refine DifferentiableAt.fun_sum ?_
  intro i _
  exact (hcoord i).const_smul (φ (b i))

/-- Pointwise differentiability of a metric family automatically gives
differentiability of the actual continuous-linear index-raising map. -/
theorem metricRaiseContinuousAt_differentiableAt_of_timeDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    DifferentiableAt ℝ (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  apply differentiableAt_clm_path_of_apply
  exact metricRaiseContinuousAt_apply_differentiableAt hgt

set_option synthInstance.maxHeartbeats 100000

/-- The inverse metric has its canonical derivative; no independent
`hRaise` witness is required. -/
theorem hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x)
      (metricRaiseDerivAt gt t₀ x hgt) t₀ := by
  letI : NormedAddCommGroup (TM x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have hdiff : DifferentiableAt ℝ
      (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀ :=
    metricRaiseContinuousAt_differentiableAt_of_timeDifferentiableAt hgt
  have hderiv : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x)
      (deriv (fun t ↦ (gt t).metricRaiseContinuousAt x) t₀) t₀ :=
    (hasDerivAt_deriv_iff (𝕜 := ℝ)
      (f := fun t ↦ (gt t).metricRaiseContinuousAt x) (x := t₀)).2 hdiff
  have heq := metricRaise_deriv_eq_of_hasDerivAt hgt hderiv
  rw [heq] at hderiv
  exact hderiv

end Poincare
