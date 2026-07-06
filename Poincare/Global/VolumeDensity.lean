import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Chart-level Riemannian volume density

This file records the coordinate density that a future global Riemannian volume
measure must use in each smooth chart: `sqrt |det G|`, where `G` is the Gram
matrix of the metric coefficients in the standard orthonormal coordinates.

The construction intentionally stays chart-local.  It does not define or glue a
measure on a manifold.
-/

noncomputable section

open Matrix
namespace Poincare

namespace VolumeDensity

variable {n : ℕ}

/-- Continuous-linear scaling of the Euclidean inner-product bilinear form. -/
def conformalInnerScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ℝ →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)

@[simp]
theorem conformalInnerScale_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (v w : E) :
    conformalInnerScale (E := E) c v w = c * inner ℝ v w := by
  rw [conformalInnerScale, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]
  change ((c • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) v) w =
    c * inner ℝ v w
  simp [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- The Gram matrix of a continuous bilinear form in the standard basis of `Fin n → ℝ`. -/
def bilinearFormMatrix
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- The conformally Euclidean Gram matrix `c I`. -/
def conformalGram (c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  c • (1 : Matrix (Fin n) (Fin n) ℝ)

@[simp]
theorem bilinearFormMatrix_conformalInnerScale (c : ℝ) :
    bilinearFormMatrix (n := n)
        (conformalInnerScale
          (E := EuclideanSpace ℝ (Fin n)) c) =
      conformalGram (n := n) c := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [bilinearFormMatrix, conformalGram]
  · simp [bilinearFormMatrix, conformalGram, EuclideanSpace.inner_single_left,
      hij]

/-- The determinant of a coordinate Gram matrix. -/
def chartGramDet (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  G.det

/-- The chart-level Riemannian volume density `sqrt |det G|`. -/
def chartVolumeDensity (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt |chartGramDet G|

/--
The same density, starting from a continuous bilinear form on the standard
coordinate model.
-/
def chartVolumeDensityOfBilinear
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) : ℝ :=
  chartVolumeDensity (bilinearFormMatrix B)

@[simp]
theorem chartGramDet_conformalGram (c : ℝ) :
    chartGramDet (conformalGram (n := n) c) = c ^ n := by
  simp [chartGramDet, conformalGram]

theorem chartVolumeDensity_nonneg (G : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ chartVolumeDensity G :=
  Real.sqrt_nonneg _

/-- Positive-definite metric coefficients give strictly positive density. -/
theorem chartVolumeDensity_pos_of_posDef {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) :
    0 < chartVolumeDensity (n := n) G := by
  have hdet_unit : IsUnit G.det := G.isUnit_iff_isUnit_det.mp hG.isUnit
  exact Real.sqrt_pos.2 (abs_pos.2 hdet_unit.ne_zero)

/-- Positive-definite bilinear-form coefficients give strictly positive density. -/
theorem chartVolumeDensityOfBilinear_pos_of_posDef
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hB : (bilinearFormMatrix B).PosDef) :
    0 < chartVolumeDensityOfBilinear (n := n) B :=
  chartVolumeDensity_pos_of_posDef hB

/-- A positive conformal factor gives positive-definite conformally Euclidean coefficients. -/
theorem conformalGram_posDef {c : ℝ} (hc : 0 < c) :
    (conformalGram (n := n) c).PosDef := by
  simpa [conformalGram] using
    (Matrix.PosDef.smul
      (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef) hc)

/--
For conformally Euclidean coefficients, the squared density is `c^n`.

This is the clean algebraic form of the usual `c^(n/2)` density formula and
avoids choosing a real-power normalization for `n / 2`.
-/
theorem chartVolumeDensity_conformalGram_sq (c : ℝ) (hc : 0 ≤ c) :
    chartVolumeDensity (n := n) (conformalGram (n := n) c) ^ 2 = c ^ n := by
  rw [chartVolumeDensity, chartGramDet_conformalGram,
    abs_of_nonneg (pow_nonneg hc n)]
  exact Real.sq_sqrt (pow_nonneg hc n)

/--
Bilinear-form version of the conformal squared-density computation, assuming
the form's coordinate Gram matrix is `c I`.
-/
theorem chartVolumeDensityOfBilinear_conformal_sq
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {c : ℝ} (hB : bilinearFormMatrix B = conformalGram (n := n) c)
    (hc : 0 ≤ c) :
    chartVolumeDensityOfBilinear (n := n) B ^ 2 = c ^ n := by
  rw [chartVolumeDensityOfBilinear, hB]
  exact chartVolumeDensity_conformalGram_sq c hc

/-- Conformal bilinear-form squared density for the scaled Euclidean inner product. -/
theorem chartVolumeDensityOfBilinear_conformalInnerScale_sq (c : ℝ)
    (hc : 0 ≤ c) :
    chartVolumeDensityOfBilinear (n := n)
        (conformalInnerScale (E := EuclideanSpace ℝ (Fin n)) c) ^ 2 =
      c ^ n := by
  exact chartVolumeDensityOfBilinear_conformal_sq
    (bilinearFormMatrix_conformalInnerScale (n := n) c) hc

/-- The determinant of a continuous family of Gram matrices is continuous. -/
theorem continuous_chartGramDet {X : Type*} [TopologicalSpace X]
    {G : X → Matrix (Fin n) (Fin n) ℝ} (hG : Continuous G) :
    Continuous fun z => chartGramDet (G z) := by
  simpa [chartGramDet] using hG.matrix_det

/-- The chart density is continuous for a continuous family of Gram matrices. -/
theorem continuous_chartVolumeDensity {X : Type*} [TopologicalSpace X]
    {G : X → Matrix (Fin n) (Fin n) ℝ} (hG : Continuous G) :
    Continuous fun z => chartVolumeDensity (n := n) (G z) := by
  have hdet : Continuous fun z => chartGramDet (G z) :=
    continuous_chartGramDet hG
  exact Real.continuous_sqrt.comp hdet.abs

end VolumeDensity

end Poincare
