import Poincare.Global.HausdorffCoordinateDensityVariation
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Hausdorff area formula for a fixed linear pullback metric

The variable-metric area formula isolated in
`HausdorffPullbackAreaFormulaReduction` is not presently available in
Mathlib.  There is, however, an exact theorem when the coordinate metric is
the pullback of the standard Euclidean metric by one fixed continuous linear
equivalence.

For `e : E ≃L[ℝ] E` and a measurable `U ⊆ E`, put the metric on `U` obtained
by pulling the Euclidean metric back along `z ↦ e z`.  This parametrization is
an isometry.  Its source Hausdorff measure is exactly the raw-Hausdorff
normalized coordinate measure with constant density `|det e|`.

The proof is entirely measure-theoretic.  After mapping both measures along
the measurable embedding `z ↦ e z`, isometry invariance identifies the first
one with Hausdorff measure restricted to `e '' U`.  For the second one,
`map_comap_subtype_coe` first turns coordinate measure into Euclidean volume
restricted to `U`, and `map_linearMap_addHaar_eq_smul_addHaar` supplies the
inverse determinant arising from pushforward.  It cancels the determinant in
the density.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal MeasureTheory Topology MatrixOrder

namespace Poincare

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- Restriction of a continuous linear equivalence to a coordinate subset. -/
def linearPullbackParametrization
    (e : E ≃L[ℝ] E) (U : Set E) : U → E :=
  fun z ↦ e z

/-- The restricted linear equivalence is a topological embedding. -/
theorem linearPullbackParametrization_isEmbedding
    (e : E ≃L[ℝ] E) (U : Set E) :
    Topology.IsEmbedding (linearPullbackParametrization e U) := by
  exact e.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal

/-- The range of the restricted linear equivalence is its image of the
coordinate subset. -/
theorem range_linearPullbackParametrization
    (e : E ≃L[ℝ] E) (U : Set E) :
    Set.range (linearPullbackParametrization e U) = e '' U := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Mapping coordinate Lebesgue measure by a restricted linear equivalence
produces restricted Euclidean volume with the inverse determinant factor. -/
theorem map_linearPullbackParametrization_coordinateLebesgueMeasure
    {U : Set E} (hU : MeasurableSet U) (e : E ≃L[ℝ] E) :
    Measure.map (linearPullbackParametrization e U)
        (coordinateLebesgueMeasure U) =
      ENNReal.ofReal
          |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| •
        (volume : Measure E).restrict (e '' U) := by
  let he : MeasurableEmbedding (e : E → E) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : Measure.map (e : E → E) (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| •
        (volume : Measure E) := by
    simpa using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar
        (volume : Measure E) hdet)
  change
    Measure.map ((e : E → E) ∘ ((↑) : U → E))
        (Measure.comap ((↑) : U → E) (volume : Measure E)) = _
  rw [← Measure.map_map e.continuous.measurable measurable_subtype_coe]
  rw [map_comap_subtype_coe hU]
  calc
    Measure.map (e : E → E) ((volume : Measure E).restrict U) =
        (Measure.map (e : E → E) (volume : Measure E)).restrict (e '' U) := by
      rw [he.restrict_map]
      rw [e.injective.preimage_image]
    _ =
        ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| •
          (volume : Measure E).restrict (e '' U) := by
      rw [hmap]
      rw [Measure.restrict_smul]

/-- A constant determinant density is a scalar multiple of coordinate
Lebesgue measure. -/
theorem rawHausdorffCoordinateDensityMeasure_const_abs_det
    (U : Set E) (e : E ≃L[ℝ] E) :
    rawHausdorffCoordinateDensityMeasure U
        (fun _ ↦ |LinearMap.det (e : E →ₗ[ℝ] E)|) =
      ((rawHausdorffLebesgueScale n : ℝ≥0∞) *
          ENNReal.ofReal |LinearMap.det (e : E →ₗ[ℝ] E)|) •
        coordinateLebesgueMeasure U := by
  rw [rawHausdorffCoordinateDensityMeasure]
  simp only [ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]
  rw [withDensity_const]

/-- The determinant in the coordinate density cancels the inverse
determinant introduced by linear pushforward. -/
theorem map_linearPullbackParametrization_rawHausdorffCoordinateDensityMeasure
    {U : Set E} (hU : MeasurableSet U) (e : E ≃L[ℝ] E) :
    Measure.map (linearPullbackParametrization e U)
        (rawHausdorffCoordinateDensityMeasure U
          (fun _ ↦ |LinearMap.det (e : E →ₗ[ℝ] E)|)) =
      (rawHausdorffLebesgueScale n : ℝ≥0∞) •
        (volume : Measure E).restrict (e '' U) := by
  have hdet : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hcancel :
      ENNReal.ofReal |LinearMap.det (e : E →ₗ[ℝ] E)| *
          ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [← abs_mul, mul_inv_cancel₀ hdet, abs_one, ENNReal.ofReal_one]
  rw [rawHausdorffCoordinateDensityMeasure_const_abs_det]
  rw [Measure.map_smul]
  rw [map_linearPullbackParametrization_coordinateLebesgueMeasure hU e]
  rw [smul_smul, mul_assoc, hcancel, mul_one]

/-- Matrix of a continuous linear equivalence in the canonical Euclidean
orthonormal basis. -/
noncomputable def linearPullbackCoordinateMatrix
    (e : E ≃L[ℝ] E) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (e : E →ₗ[ℝ] E)

/-- Entries of the coordinate matrix are the standard Euclidean coordinates
of the images of the canonical basis vectors. -/
theorem linearPullbackCoordinateMatrix_apply
    (e : E ≃L[ℝ] E) (i j : Fin n) :
    linearPullbackCoordinateMatrix e i j =
      e (EuclideanSpace.basisFun (Fin n) ℝ j) i := by
  simp [linearPullbackCoordinateMatrix, LinearMap.toMatrix_apply]

/-- Gram matrix of the Euclidean metric pulled back by `e`, expressed in the
canonical Euclidean coordinate frame. -/
noncomputable def linearPullbackGramMatrix
    (e : E ≃L[ℝ] E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    inner ℝ
      (e (EuclideanSpace.basisFun (Fin n) ℝ i))
      (e (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- The pullback Gram matrix is `Aᵀ A`, where `A` is the coordinate matrix of
the linear equivalence. -/
theorem linearPullbackGramMatrix_eq_transpose_mul
    (e : E ≃L[ℝ] E) :
    linearPullbackGramMatrix e =
      Matrix.transpose (linearPullbackCoordinateMatrix e) *
        linearPullbackCoordinateMatrix e := by
  ext i j
  simp [linearPullbackGramMatrix, Matrix.mul_apply,
    linearPullbackCoordinateMatrix_apply, PiLp.inner_apply, mul_comm]

/-- The determinant of the coordinate matrix is the intrinsic determinant of
the underlying linear endomorphism. -/
theorem det_linearPullbackCoordinateMatrix
    (e : E ≃L[ℝ] E) :
    (linearPullbackCoordinateMatrix e).det =
      LinearMap.det (e : E →ₗ[ℝ] E) := by
  exact LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (e : E →ₗ[ℝ] E)

/-- The determinant of a linear pullback Gram matrix is the square of the
Jacobian determinant. -/
theorem det_linearPullbackGramMatrix
    (e : E ≃L[ℝ] E) :
    (linearPullbackGramMatrix e).det =
      (LinearMap.det (e : E →ₗ[ℝ] E)) ^ 2 := by
  rw [linearPullbackGramMatrix_eq_transpose_mul]
  rw [Matrix.det_mul, Matrix.det_transpose]
  rw [det_linearPullbackCoordinateMatrix]
  rw [pow_two]

/-- The Gram density used by the variable Riemannian area formula is exactly
the constant absolute determinant density used above. -/
theorem chartVolumeDensity_linearPullbackGramMatrix
    (e : E ≃L[ℝ] E) :
    VolumeDensity.chartVolumeDensity (linearPullbackGramMatrix e) =
      |LinearMap.det (e : E →ₗ[ℝ] E)| := by
  rw [VolumeDensity.chartVolumeDensity, VolumeDensity.chartGramDet]
  rw [det_linearPullbackGramMatrix, abs_sq]
  rw [Real.sqrt_sq_eq_abs]

/-- The exact fixed-linear source-side area formula.

The `PseudoEMetricSpace U` used by `μH[n]` is obtained from the metric pulled
back from standard Euclidean `E` along `z ↦ e z`. -/
def LinearPullbackMetricHausdorffAreaFormula
    (U : Set E) (e : E ≃L[ℝ] E) : Prop :=
  let ψ := linearPullbackParametrization e U
  let hψ := linearPullbackParametrization_isEmbedding e U
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  (μH[(n : ℝ)] : Measure U) =
    rawHausdorffCoordinateDensityMeasure U
      (fun _ ↦ |LinearMap.det (e : E →ₗ[ℝ] E)|)

/-- Hausdorff measure for a metric pulled back by a fixed continuous linear
equivalence equals coordinate Lebesgue measure with the exact constant
Jacobian density `|det e|`, including Mathlib's raw-Hausdorff normalization. -/
theorem linearPullbackMetricHausdorffAreaFormula
    {U : Set E} (hU : MeasurableSet U) (e : E ≃L[ℝ] E) :
    LinearPullbackMetricHausdorffAreaFormula U e := by
  rw [LinearPullbackMetricHausdorffAreaFormula]
  let ψ := linearPullbackParametrization e U
  let hψ := linearPullbackParametrization_isEmbedding e U
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  have hψiso : Isometry ψ := by
    intro z w
    rfl
  have hcoe : MeasurableEmbedding ((↑) : U → E) :=
    MeasurableEmbedding.subtype_coe hU
  have he : MeasurableEmbedding (e : E → E) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hψmeas : MeasurableEmbedding ψ := by
    exact he.comp hcoe
  apply hψmeas.map_injective
  rw [hψiso.map_hausdorffMeasure (Or.inl (by positivity : (0 : ℝ) ≤ n))]
  rw [map_linearPullbackParametrization_rawHausdorffCoordinateDensityMeasure
    hU e]
  rw [range_linearPullbackParametrization]
  rw [hausdorffMeasure_closedSmoothModel_eq_scale_smul_volume n]
  rw [Measure.restrict_smul]

/-- Gram-density form of the fixed-linear pullback area formula.

Unlike `linearPullbackMetricHausdorffAreaFormula`, the density in this
statement is written in exactly the `VolumeDensity.chartVolumeDensity G`
form used by the variable Riemannian area formula. -/
theorem linearPullbackMetricHausdorffAreaFormula_chartVolumeDensity
    {U : Set E} (hU : MeasurableSet U) (e : E ≃L[ℝ] E) :
    let ψ := linearPullbackParametrization e U
    let hψ := linearPullbackParametrization_isEmbedding e U
    let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
    let pullbackEMetric : EMetricSpace U :=
      @MetricSpace.toEMetricSpace U pullbackMetric
    letI : EMetricSpace U := pullbackEMetric
    letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
    (μH[(n : ℝ)] : Measure U) =
      rawHausdorffCoordinateDensityMeasure U
        (fun _ ↦
          VolumeDensity.chartVolumeDensity
            (linearPullbackGramMatrix e)) := by
  have harea := linearPullbackMetricHausdorffAreaFormula hU e
  simpa only [LinearPullbackMetricHausdorffAreaFormula,
    chartVolumeDensity_linearPullbackGramMatrix] using harea

/-- Every positive-definite constant real Gram matrix is the pullback Gram
matrix of a continuous linear equivalence of the Euclidean model.

The representative is obtained from the positive matrix square root
`B = CFC.sqrt G`.  Since `G` is positive definite, `B` is invertible;
nonnegativity makes `B` self-adjoint, and functional calculus gives
`B * B = G`.  Thus the linear equivalence with coordinate matrix `B` has
Gram matrix `Bᵀ * B = G`. -/
theorem exists_continuousLinearEquiv_linearPullbackGramMatrix_eq
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) :
    ∃ e : E ≃L[ℝ] E, linearPullbackGramMatrix e = G := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt G
  have hGnonneg : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ G :=
    hG.posSemidef.nonneg
  have hBnonneg : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ B := by
    dsimp [B]
    exact CFC.sqrt_nonneg G
  have hBunit : IsUnit B := by
    dsimp [B]
    exact (CFC.isUnit_sqrt_iff G hGnonneg).2 hG.isUnit
  have hBdetunit : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  let b : Module.Basis (Fin n) ℝ E :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let f : E →ₗ[ℝ] E := Matrix.toLin b b B
  have hfMatrix : LinearMap.toMatrix b b f = B := by
    dsimp [f]
    exact LinearMap.toMatrix_toLin b b B
  have hfdetunit : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [hfMatrix]
    exact hBdetunit
  let eLin : E ≃ₗ[ℝ] E := LinearEquiv.ofIsUnitDet hfdetunit
  let e : E ≃L[ℝ] E := eLin.toContinuousLinearEquiv
  have heMatrix : linearPullbackCoordinateMatrix e = B := by
    unfold linearPullbackCoordinateMatrix
    change LinearMap.toMatrix b b (e : E →ₗ[ℝ] E) = B
    rw [show (e : E →ₗ[ℝ] E) = eLin from
      LinearEquiv.coe_toContinuousLinearEquiv eLin]
    rw [show (eLin : E →ₗ[ℝ] E) = f from
      LinearEquiv.coe_ofIsUnitDet hfdetunit]
    exact hfMatrix
  have hBtranspose : Matrix.transpose B = B := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hBnonneg.star_eq
  have hBsquare : B * B = G := by
    dsimp [B]
    exact CFC.sqrt_mul_sqrt_self G hGnonneg
  refine ⟨e, ?_⟩
  rw [linearPullbackGramMatrix_eq_transpose_mul]
  rw [heMatrix, hBtranspose, hBsquare]

/-- A fixed representative of a positive-definite constant Gram matrix,
chosen from the square-root construction above. -/
noncomputable def positiveDefiniteGramLinearEquiv
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) : E ≃L[ℝ] E :=
  Classical.choose
    (exists_continuousLinearEquiv_linearPullbackGramMatrix_eq hG)

/-- The chosen continuous linear representative has exactly the requested
positive-definite Gram matrix. -/
theorem linearPullbackGramMatrix_positiveDefiniteGramLinearEquiv
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    linearPullbackGramMatrix (positiveDefiniteGramLinearEquiv G hG) = G :=
  Classical.choose_spec
    (exists_continuousLinearEquiv_linearPullbackGramMatrix_eq hG)

/-- Exact Hausdorff area formula for an arbitrary positive-definite constant
Gram matrix.

The metric on `U` is pulled back along the fixed square-root representative
of `G`; the coordinate density is stated directly as
`VolumeDensity.chartVolumeDensity G`. -/
theorem positiveDefiniteConstantGramHausdorffAreaFormula
    {U : Set E} (hU : MeasurableSet U)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    let e := positiveDefiniteGramLinearEquiv G hG
    let ψ := linearPullbackParametrization e U
    let hψ := linearPullbackParametrization_isEmbedding e U
    let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
    let pullbackEMetric : EMetricSpace U :=
      @MetricSpace.toEMetricSpace U pullbackMetric
    letI : EMetricSpace U := pullbackEMetric
    letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
    (μH[(n : ℝ)] : Measure U) =
      rawHausdorffCoordinateDensityMeasure U
        (fun _ ↦ VolumeDensity.chartVolumeDensity G) := by
  have harea :=
    linearPullbackMetricHausdorffAreaFormula_chartVolumeDensity hU
      (positiveDefiniteGramLinearEquiv G hG)
  simpa only [linearPullbackGramMatrix_positiveDefiniteGramLinearEquiv]
    using harea

end Poincare
