import Poincare.Global.CoordinateVolumeDensityVariation

/-!
# Volume-density variation in an arbitrary and inverse-chart frame

`coordinateGramVolumeDensityAt` uses Mathlib's selected finite basis of the
tangent fiber.  Its time-variation formula is intrinsic, but its numerical
density is not automatically the density relative to an arbitrary coordinate
Lebesgue measure: the latter must use the tangent frame obtained by
differentiating that coordinate chart's inverse.

This file proves the determinant calculation in any fixed tangent basis and
then specializes it to `chartTangentBasisAt`, the inverse-chart derivative
frame already constructed in `ScalarVariation`.  Thus the Hausdorff/coordinate
measure bridge can use the correct chart Gram determinant without any false
identification with the selected `Module.finBasis` density.
-/

noncomputable section

open Bundle FiberBundle Matrix
open scoped Manifold ContDiff

namespace Poincare

universe u

variable {n d : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

/-- Matrix of a metric in an arbitrary fixed finite tangent basis. -/
def metricMatrixInBasisAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ g.metricBilinAt x (b i) (b j)

omit [T2Space M] in
@[simp]
theorem metricMatrixInBasisAt_apply
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) (i j : Fin d) :
    metricMatrixInBasisAt g x b i j = g.metricBilinAt x (b i) (b j) :=
  rfl

/-- Matrix of a metric-speed tensor in the same fixed tangent basis. -/
def metricVariationMatrixInBasisAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j ↦ timeDerivAt gt t₀ x (b i) (b j)

omit [T2Space M] in
@[simp]
theorem metricVariationMatrixInBasisAt_apply
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) (i j : Fin d) :
    metricVariationMatrixInBasisAt gt t₀ x b i j =
      timeDerivAt gt t₀ x (b i) (b j) :=
  rfl

/-- Square-root Gram determinant in an arbitrary fixed tangent basis. -/
def basisVolumeDensityAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) (t : ℝ) : ℝ :=
  VolumeDensity.chartVolumeDensity (metricMatrixInBasisAt (gt t) x b)

/-- Metric nondegeneracy makes its matrix nonsingular in every basis. -/
theorem metricMatrixInBasisAt_det_ne_zero
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) :
    (metricMatrixInBasisAt g x b).det ≠ 0 := by
  have hmatrix :
      metricMatrixInBasisAt g x b =
        LinearMap.toMatrix₂ b b (g.metricBilinAt x) := by
    ext i j
    simp [metricMatrixInBasisAt, LinearMap.toMatrix₂_apply,
      g.metricBilinAt_apply]
  rw [hmatrix]
  exact
    (LinearMap.nondegenerate_iff_det_ne_zero b).mp
      (g.metricBilinAt_nondegenerate x)

omit [T2Space M] in
/-- Pointwise time differentiability differentiates every entry in any fixed
tangent basis. -/
theorem hasDerivAt_metricMatrixInBasisAt_entry
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (b : Module.Basis (Fin d) ℝ (TM x))
    (hgt : TimeDifferentiableAt gt t₀ x) (i j : Fin d) :
    HasDerivAt (fun t ↦ metricMatrixInBasisAt (gt t) x b i j)
      (metricVariationMatrixInBasisAt gt t₀ x b i j) t₀ := by
  change HasDerivAt (fun t ↦ (gt t).inner x (b i) (b j))
    (deriv (fun t ↦ (gt t).inner x (b i) (b j)) t₀) t₀
  exact (hgt (b i) (b j)).hasDerivAt

/-- The metric-raised dual of an arbitrary basis covector is the inverse-Gram
linear combination of that basis. -/
theorem metricDualVectorAt_basis_coord_eq_sum_inv
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (b : Module.Basis (Fin d) ℝ (TM x)) (i : Fin d) :
    metricDualVectorAt g x (b.coord i) =
      ∑ j, (metricMatrixInBasisAt g x b)⁻¹ i j • b j := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let G := metricMatrixInBasisAt g x b
  have hdet : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr
      (metricMatrixInBasisAt_det_ne_zero g x b)
  apply
    (LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)).injective
  apply b.ext
  intro k
  have hmatrix : ∑ j, G⁻¹ i j * G j k = if i = k then 1 else 0 := by
    have hmul := congrArg
      (fun A : Matrix (Fin d) (Fin d) ℝ ↦ A i k)
      (Matrix.nonsing_inv_mul G hdet)
    simpa [Matrix.mul_apply] using hmul
  calc
    ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x))
        (metricDualVectorAt g x (b.coord i))) (b k) =
        b.coord i (b k) := by
          simp [metricDualVectorAt]
    _ = if i = k then 1 else 0 := by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
          by_cases hik : i = k <;> simp [hik, eq_comm]
    _ = ∑ j, G⁻¹ i j * G j k := hmatrix.symm
    _ = ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
        (g.metricBilinAt_nondegenerate x))
        (∑ j, G⁻¹ i j • b j)) (b k) := by
          simp [LinearMap.BilinForm.toDual_def,
            ClosedSmoothRiemannianMetric.metricBilinAt_apply,
            G, smul_eq_mul]

/-- The inverse-Gram contraction of the speed matrix in any tangent basis is
the intrinsic metric trace. -/
theorem inverseMetricMatrix_contract_metricVariationMatrix_eq_trace
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (b : Module.Basis (Fin d) ℝ (TM x))
    (hgt : TimeDifferentiableAt gt t₀ x) :
    (∑ i, ∑ j, (metricMatrixInBasisAt (gt t₀) x b)⁻¹ i j *
        metricVariationMatrixInBasisAt gt t₀ x b j i) =
      traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let B := timeDerivBilinAt gt t₀ x hgt
  have htrace := traceMetricVariationAt_eq_metricTraceInBasisAt
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
    (B := B) (b := b) (by intro p q; rfl)
  rw [htrace]
  unfold metricTraceInBasisAt
  apply Finset.sum_congr rfl
  intro i _hi
  rw [metricDualVectorAt_basis_coord_eq_sum_inv (g := gt t₀) (x := x) b i]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [map_smul, smul_eq_mul]
  rw [metricVariationMatrixInBasisAt]
  rw [timeDerivAt_symm gt t₀ x (b j) (b i)]
  rfl

/-- Basis-coordinate Riemannian density first variation:
`d/dt sqrt(det g_b) = (1/2) sqrt(det g_b) tr_g(g')`. -/
theorem hasDerivAt_basisVolumeDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (b : Module.Basis (Fin d) ℝ (TM x))
    (hgt : TimeDifferentiableAt gt t₀ x) :
    HasDerivAt (basisVolumeDensityAt gt x b)
      ((1 / 2 : ℝ) * basisVolumeDensityAt gt x b t₀ *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x) t₀ := by
  have hdensity :=
    VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
      (G := fun t ↦ metricMatrixInBasisAt (gt t) x b)
      (G' := metricVariationMatrixInBasisAt gt t₀ x b)
      (fun i j ↦ hasDerivAt_metricMatrixInBasisAt_entry b hgt i j)
      (metricMatrixInBasisAt_det_ne_zero (gt t₀) x b)
  have hcoeff :
      (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity
            (metricMatrixInBasisAt (gt t₀) x b) *
          (∑ i, ∑ j, (metricMatrixInBasisAt (gt t₀) x b)⁻¹ i j *
            metricVariationMatrixInBasisAt gt t₀ x b j i) =
        (1 / 2 : ℝ) *
          VolumeDensity.chartVolumeDensity
            (metricMatrixInBasisAt (gt t₀) x b) *
          traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x := by
    rw [inverseMetricMatrix_contract_metricVariationMatrix_eq_trace b hgt]
  simpa [basisVolumeDensityAt] using hdensity.congr_deriv hcoeff

/-- The inverse-chart tangent basis obtained from the canonical Euclidean
orthonormal coordinate basis.  This is the frame appropriate to Euclidean
Lebesgue measure, unlike an arbitrary selected finite basis of the model
space. -/
def inverseChartEuclideanTangentBasisAt
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    Module.Basis (Fin n) ℝ (TM ((extChartAt I x₀).symm z)) :=
  let hInv := isInvertible_mfderivWithin_extChartAt_symm (x := x₀) hz
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
    (Classical.choose hInv).toLinearEquiv

omit [T2Space M] in
/-- The inverse-chart Euclidean tangent basis evaluates to the inverse-chart
derivative applied to the canonical Euclidean basis vector. -/
theorem inverseChartEuclideanTangentBasisAt_apply
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (i : Fin n) :
    inverseChartEuclideanTangentBasisAt (n := n) (M := M) x₀ hz i =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  let hInv := isInvertible_mfderivWithin_extChartAt_symm (x := x₀) hz
  have hchoose :
      ((Classical.choose hInv :
          E ≃L[ℝ] TM ((extChartAt I x₀).symm z)) : E →L[ℝ]
            TM ((extChartAt I x₀).symm z)) =
        mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm) (Set.range I) z :=
    Classical.choose_spec hInv
  unfold inverseChartEuclideanTangentBasisAt
  rw [Module.Basis.map_apply]
  simpa [hInv] using
    congrArg
      (fun L : E →L[ℝ] TM ((extChartAt I x₀).symm z) ↦
        L (EuclideanSpace.basisFun (Fin n) ℝ i)) hchoose

/-- The actual inverse-chart Gram density relative to the canonical Euclidean
coordinate basis at a point in the target of the extended chart centered at
`x₀`. -/
def inverseChartVolumeDensityAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : E} (hz : z ∈ (extChartAt I x₀).target) (t : ℝ) : ℝ :=
  basisVolumeDensityAt gt ((extChartAt I x₀).symm z)
    (inverseChartEuclideanTangentBasisAt (n := n) (M := M) x₀ hz) t

/-- The correct inverse-chart Gram density has the intrinsic first variation,
without identifying it with a determinant in an unrelated selected basis. -/
theorem hasDerivAt_inverseChartVolumeDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x₀ : M}
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hgt : TimeDifferentiableAt gt t₀ ((extChartAt I x₀).symm z)) :
    HasDerivAt (inverseChartVolumeDensityAt gt x₀ hz)
      ((1 / 2 : ℝ) * inverseChartVolumeDensityAt gt x₀ hz t₀ *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
          ((extChartAt I x₀).symm z)) t₀ := by
  exact
    hasDerivAt_basisVolumeDensityAt
      (inverseChartEuclideanTangentBasisAt (n := n) (M := M) x₀ hz) hgt

end ClosedSmoothRiemannianMetric
end Poincare
