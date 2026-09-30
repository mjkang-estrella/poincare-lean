import Poincare.Global.MetricCoefficientNeighborhoods

/-!
# Actual inverse metric coefficients for the local solver

The metric's coordinate Gram matrix is positive definite on its genuine
chart target, so its inverse is positive definite there. Smoothness of the
metric entries and nonvanishing of the determinant give smooth inverse
entries. These supply the coefficient inputs of the metric-adapted local
parametrix, on the route toward universal Hamilton input existence.
-/

noncomputable section
set_option autoImplicit false
open Set Matrix
open scoped Manifold ContDiff

universe u

namespace Poincare.MetricInverseCoefficientRegularity

variable {M : Type u} [TopologicalSpace M] [T2Space M] [hcompact : CompactSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

include hcompact in
/-- The actual inverse Gram matrix is positive definite on the chart target. -/
theorem inverse_metric_field_posDef
    (g0 : ClosedSmoothRiemannianMetric 3 M) (p : M)
    (z : ClosedSmoothModel 3)
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target) :
    ((inverseChartPullbackGramMatrixField g0 p z)⁻¹).PosDef := by
  let x := (extChartAt (closedSmoothModelWithCorners 3) p).symm z
  let b := ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt p hz
  have hmatrix : inverseChartPullbackGramMatrixField g0 p z =
      LinearMap.toMatrix₂ b b (g0.metricBilinAt x) := by
    ext i j
    simp only [LinearMap.toMatrix₂_apply, g0.metricBilinAt_apply]
    change CovariantDerivative.chartMetric g0.inner p z
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      g0.inner x (b i) (b j)
    dsimp only [b]
    rw [ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply,
      ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt_apply]
    rfl
  have hpos : (LinearMap.toMatrix₂ b b (g0.metricBilinAt x)).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · apply Matrix.IsHermitian.ext
      intro i j
      simp only [LinearMap.toMatrix₂_apply, star_trivial, g0.metricBilinAt_apply]
      exact g0.inner_symm x (b j) (b i)
    · intro a ha
      have hva : b.equivFun.symm a ≠ 0 := b.equivFun.symm.map_ne_zero_iff.mpr ha
      have heq : star a ⬝ᵥ (LinearMap.toMatrix₂ b b (g0.metricBilinAt x)).mulVec a =
          g0.metricBilinAt x (b.equivFun.symm a) (b.equivFun.symm a) := by
        simpa using dotProduct_toMatrix₂_mulVec b b (g0.metricBilinAt x) a a
      rw [heq, g0.metricBilinAt_apply]
      exact g0.inner_pos x hva
  rw [hmatrix]
  exact hpos.inv

/-- Every actual inverse metric entry is smooth on the genuine chart target. -/
theorem inverse_metric_entry_contDiffOn
    (g0 : ClosedSmoothRiemannianMetric 3 M) (p : M) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun z ↦ (inverseChartPullbackGramMatrixField g0 p z)⁻¹ i j)
      (extChartAt (closedSmoothModelWithCorners 3) p).target := by
  classical
  have hG (a b : Fin 3) :
      ContDiffOn ℝ ∞ (fun z ↦ inverseChartPullbackGramMatrixField g0 p z a b)
        (extChartAt (closedSmoothModelWithCorners 3) p).target :=
    (CovariantDerivative.contMDiffOn_chartMetric_pairing
      g0.inner p (m := ∞) (by simp) g0.contMDiff_inner
      (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b)).contDiffOn
  have hdet := ClosedLaplacianStokesProducer.contDiffOn_matrix_det
    (inverseChartPullbackGramMatrixField g0 p)
    (extChartAt (closedSmoothModelWithCorners 3) p).target hG
  have hne (z : ClosedSmoothModel 3)
      (hz : z ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target) :
      (inverseChartPullbackGramMatrixField g0 p z).det ≠ 0 :=
    MetricCoefficientNeighborhoods.gramField_det_ne_zero g0 p hz
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply (hdet.inv hne).mul
  apply ClosedLaplacianStokesProducer.contDiffOn_matrix_det
  intro k l
  by_cases hk : k = j
  · simpa only [Matrix.updateRow_apply, hk, ite_true] using
      (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : ClosedSmoothModel 3 ↦ (Pi.single i (1 : ℝ) : Fin 3 → ℝ) l)
        (extChartAt (closedSmoothModelWithCorners 3) p).target)
  · simpa only [Matrix.updateRow_apply, hk, ite_false] using hG k l

end Poincare.MetricInverseCoefficientRegularity
