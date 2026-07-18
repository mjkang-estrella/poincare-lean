import Poincare.Global.VolumeDensity
import Poincare.Global.MetricRaiseTimeDerivative

/-!
# Coordinate volume-density variation

This file proves the finite-dimensional Jacobi formula directly from the
Leibniz expansion of the determinant and then differentiates
`sqrt |det G(t)|`.  The final section specializes the matrix path to the Gram
coefficients of a differentiable Riemannian metric path at a fixed point.

The results here are deliberately chart-local.  Passing from these coordinate
densities to the repo's Hausdorff-defined `volumeMeasure`, including chart
change, gluing, and differentiation under the integral, remains a separate
measure-theoretic bridge.
-/

noncomputable section

open Matrix

namespace Poincare

namespace VolumeDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The first-order determinant variation, expressed by replacing one column
at a time by the corresponding column of the variation matrix. -/
def determinantColumnVariation (A B : Matrix ι ι ℝ) : ℝ :=
  ∑ i, (A.updateCol i (fun j => B j i)).det

private theorem prod_updateCol_eq
    (A B : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i : ι) :
    (∏ j, (A.updateCol i (fun k => B k i)) (σ j) j) =
      (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j => (A.updateCol i (fun k => B k i)) (σ j) j)
    (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)
  · simp

/-- The replaced-column expression agrees with the derivative obtained by
differentiating the Leibniz formula term by term. -/
theorem determinantColumnVariation_eq_leibniz
    (A B : Matrix ι ι ℝ) :
    determinantColumnVariation A B =
      ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  classical
  rw [determinantColumnVariation]
  simp_rw [Matrix.det_apply']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [prod_updateCol_eq]

/-- Entrywise differentiability of a square-matrix path differentiates its
determinant by the replaced-column formula. -/
theorem hasDerivAt_det_of_entries
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀) :
    HasDerivAt (fun t => (A t).det)
      (determinantColumnVariation (A t₀) A') t₀ := by
  classical
  rw [determinantColumnVariation_eq_leibniz]
  rw [show (fun t => (A t).det) =
      fun t => ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A t (σ i) i by
    funext t
    exact Matrix.det_apply' (A t)]
  apply HasDerivAt.fun_sum
  intro σ _hσ
  have hprod :
      HasDerivAt (fun t => ∏ i, A t (σ i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, A t₀ (σ j) j) *
          A' (σ i) i) t₀ := by
    have hp :=
      HasDerivAt.finsetProd (u := Finset.univ)
        (f := fun i t => A t (σ i) i)
        (f' := fun i => A' (σ i) i)
        (fun i _hi => hA (σ i) i)
    exact hp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by simp)
  simpa using hprod.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))

/-- Cramer's rule converts the replaced-column variation to contraction with
the adjugate matrix. -/
theorem determinantColumnVariation_eq_adjugate
    (A B : Matrix ι ι ℝ) :
    determinantColumnVariation A B =
      ∑ i, ∑ j, A.adjugate i j * B j i := by
  classical
  rw [determinantColumnVariation]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- Over the reals, a non-singular adjugate is `det A` times the matrix
inverse, entrywise. -/
theorem det_mul_nonsing_inv_apply_eq_adjugate
    (A : Matrix ι ι ℝ) (hdet : A.det ≠ 0) (i j : ι) :
    A.det * A⁻¹ i j = A.adjugate i j := by
  rw [Matrix.inv_def]
  simp [hdet]

/-- Jacobi's formula for an entrywise differentiable real matrix path. -/
theorem hasDerivAt_det_eq_det_mul_trace
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t₀ : ℝ}
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀)
    (hdet : (A t₀).det ≠ 0) :
    HasDerivAt (fun t => (A t).det)
      ((A t₀).det * ∑ i, ∑ j, (A t₀)⁻¹ i j * A' j i) t₀ := by
  convert hasDerivAt_det_of_entries hA using 1
  rw [determinantColumnVariation_eq_adjugate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← mul_assoc, det_mul_nonsing_inv_apply_eq_adjugate (A t₀) hdet]

/-- If a nonzero scalar path has derivative `f(t₀) * c`, then its absolute
value has derivative `|f(t₀)| * c`.  This local sign argument avoids imposing
a global sign choice on the determinant. -/
theorem hasDerivAt_abs_of_self_mul
    {f : ℝ → ℝ} {t₀ c : ℝ}
    (hf : HasDerivAt f (f t₀ * c) t₀) (hne : f t₀ ≠ 0) :
    HasDerivAt (fun t => |f t|) (|f t₀| * c) t₀ := by
  rcases hne.lt_or_gt with hneg | hpos
  · have hlocal : (fun t => |f t|) =ᶠ[nhds t₀] fun t => -f t :=
      (hf.continuousAt.eventually (Iio_mem_nhds hneg)).mono
        (fun t ht => abs_of_neg ht)
    convert hf.neg.congr_of_eventuallyEq hlocal using 1
    simp [abs_of_neg hneg]
  · have hlocal : (fun t => |f t|) =ᶠ[nhds t₀] f :=
      (hf.continuousAt.eventually (Ioi_mem_nhds hpos)).mono
        (fun t ht => abs_of_pos ht)
    convert hf.congr_of_eventuallyEq hlocal using 1
    simp [abs_of_pos hpos]

/-- The coordinate density derivative at a nonsingular Gram matrix.  The
absolute value makes the formula independent of the determinant's local sign. -/
theorem hasDerivAt_chartVolumeDensity_of_det_ne_zero
    {n : ℕ} {G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G' : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀)
    (hdetne : (G t₀).det ≠ 0) :
    HasDerivAt (fun t => chartVolumeDensity (n := n) (G t))
      ((1 / 2 : ℝ) * chartVolumeDensity (n := n) (G t₀) *
        ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ := by
  have hdet := hasDerivAt_det_eq_det_mul_trace hG hdetne
  have habs : HasDerivAt (fun t => |(G t).det|)
      (|(G t₀).det| * ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ :=
    hasDerivAt_abs_of_self_mul hdet hdetne
  have hsqrt := habs.sqrt (abs_ne_zero.mpr hdetne)
  have habspos : 0 < |(G t₀).det| := abs_pos.2 hdetne
  have hsqrtpos : 0 < Real.sqrt |(G t₀).det| := Real.sqrt_pos.2 habspos
  have hcoeff :
      (|(G t₀).det| * ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) /
          (2 * Real.sqrt |(G t₀).det|) =
        (1 / 2 : ℝ) * Real.sqrt |(G t₀).det| *
          ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i := by
    field_simp
    rw [Real.sq_sqrt habspos.le]
    ring
  simpa [chartVolumeDensity, chartGramDet] using hsqrt.congr_deriv hcoeff

/-- The coordinate density derivative for a positive-definite Gram matrix.
The result is the usual one-half density times the inverse-matrix trace. -/
theorem hasDerivAt_chartVolumeDensity_of_posDef
    {n : ℕ} {G : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {G' : Matrix (Fin n) (Fin n) ℝ} {t₀ : ℝ}
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀)
    (hpos : (G t₀).PosDef) :
    HasDerivAt (fun t => chartVolumeDensity (n := n) (G t))
      ((1 / 2 : ℝ) * chartVolumeDensity (n := n) (G t₀) *
        ∑ i, ∑ j, (G t₀)⁻¹ i j * G' j i) t₀ := by
  have hdet_unit : IsUnit (G t₀).det :=
    (G t₀).isUnit_iff_isUnit_det.mp hpos.isUnit
  exact hasDerivAt_chartVolumeDensity_of_det_ne_zero hG hdet_unit.ne_zero

end VolumeDensity

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

/-- The coefficient matrix of the pointwise metric time derivative in the
canonical Gram frame based at `x`. -/
noncomputable def metricGramTimeDerivativeAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) :
    Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
  fun i j => timeDerivAt gt t₀ x (gramFrame x x i) (gramFrame x x j)

/-- The chart-coordinate density of the fixed-fiber Gram matrix of `gt t` at
`x`. -/
noncomputable def coordinateGramVolumeDensityAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) : ℝ :=
  VolumeDensity.chartVolumeDensity
    (n := Module.finrank ℝ (TM x)) (gramMatrix (gt t) x x)

omit [T2Space M] in
/-- Pointwise time differentiability of the metric differentiates every entry
of its canonical fixed-fiber Gram matrix with the expected coefficient. -/
theorem hasDerivAt_gramMatrix_time_entry
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    HasDerivAt (fun t => gramMatrix (gt t) x x i j)
      (metricGramTimeDerivativeAt gt t₀ x i j) t₀ := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  simpa [metricGramTimeDerivativeAt, gramMatrix, gramFrame, b, timeDerivAt] using
    (hgt (b i) (b j)).hasDerivAt

/-- The inverse-Gram contraction of the coefficient derivative is exactly the
intrinsic metric trace.  Symmetry removes the transpose appearing in the
generic Jacobi formula. -/
theorem inverseGram_contract_metricGramTimeDerivativeAt_eq_trace
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    (∑ i, ∑ j, (gramMatrix (gt t₀) x x)⁻¹ i j *
        metricGramTimeDerivativeAt gt t₀ x j i) =
      traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have htrace := traceMetricVariationAt_eq_sum_gram_inv
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x) (y := x)
    (gramMatrix_at_base_isUnit (g := gt t₀) (x := x))
    (timeDerivBilinAt gt t₀ x hgt) (by intro p q; rfl)
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [metricGramTimeDerivativeAt]
  rw [timeDerivAt_symm gt t₀ x (gramFrame x x j) (gramFrame x x i)]

/-- Coordinate Riemannian density first variation at a fixed point:
`d/dt sqrt(det g) = (1/2) sqrt(det g) tr_g(g')`.

This is the final finite-dimensional endpoint.  Identifying these local
densities with the Hausdorff-defined global `volumeMeasure`, gluing them across
charts, and differentiating their integral are intentionally not assumed here.
-/
theorem hasDerivAt_coordinateGramVolumeDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (coordinateGramVolumeDensityAt gt x)
      ((1 / 2 : ℝ) * coordinateGramVolumeDensityAt gt x t₀ *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x) t₀ := by
  have hdensity :=
    VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
      (G := fun t => gramMatrix (gt t) x x)
      (G' := metricGramTimeDerivativeAt gt t₀ x)
      (fun i j => hasDerivAt_gramMatrix_time_entry hgt i j)
      (gramMatrix_at_base_det_ne_zero (g := gt t₀) (x := x))
  have hcoeff :
      (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity (gramMatrix (gt t₀) x x) *
          (∑ i, ∑ j, (gramMatrix (gt t₀) x x)⁻¹ i j *
            metricGramTimeDerivativeAt gt t₀ x j i) =
        (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity (gramMatrix (gt t₀) x x) *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
    rw [inverseGram_contract_metricGramTimeDerivativeAt_eq_trace hgt]
  simpa [coordinateGramVolumeDensityAt] using hdensity.congr_deriv hcoeff

end ClosedSmoothRiemannianMetric

end Poincare
