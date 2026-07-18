import Poincare.Global.NormalizedFlowScalarVarianceConcentration
import Poincare.Global.NormalizedFlowFiniteTimeCurvatureCompactness

/-!
# A finite Hamilton-pinched slice from a positive mean-scalar floor

The scalar-variance and traceless-Ricci concentration theorem supplies one
escaping sample on which both densities are uniformly small.  If the mean
scalar is uniformly positive on the forward ray, one sufficiently late
sampled slice has

* `R > c / 2`, and
* `|Ric°|² < (c / 24)²`.

Taking `rho = c / 2`, the second estimate is exactly the existing
`(rho / 12)²` threshold for the `R / 4` Ricci-eigenvalue floor.  This removes
the global pointwise scalar-floor assumption from the finite-slice step while
keeping separate scalar-variance and traceless-Ricci Lipschitz inputs.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Finite absolute dissipation and a positive forward mean-scalar floor
produce a nonnegative finite slice with Hamilton's `R / 4` eigenvalue floor.

No pointwise scalar lower bound is assumed.  The pointwise bound at the
selected slice is obtained from uniform concentration of scalar variance on
the same sample that makes traceless Ricci uniformly small. -/
theorem exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_meanLower
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {LScalar LTraceless c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarVarianceLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2) LScalar)
    (hTracelessLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) LTraceless)
    (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt)
    (hc : 0 < c)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t)) :
    ∃ t0 : ℝ, 0 ≤ t0 ∧
      (∀ x : M, c / 2 < (gt t0).scalarAt x) ∧
      (∀ x : M,
        (gt t0).tracelessRicciNormSqAt x < (c / 24) ^ 2) ∧
      GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t0) ∧
      GlobalPinchingQuotientBound3 (gt t0) (3 / 8) := by
  obtain ⟨sample, hsample, _hVarianceZero, _hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hhalf : 0 < c / 2 := div_pos hc (by norm_num)
  have htrThreshold : 0 < (c / 24) ^ 2 :=
    sq_pos_of_pos (div_pos hc (by norm_num))
  have hsmallEventually :
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < c / 2 ∧
          (gt (sample i)).tracelessRicciNormSqAt x < (c / 24) ^ 2 :=
    hUniform (c / 2) hhalf ((c / 24) ^ 2) htrThreshold
  have htimeEventually : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hsample.eventually (eventually_ge_atTop 0)
  obtain ⟨i, htime, hsmall⟩ :=
    (htimeEventually.and hsmallEventually).exists
  have hscalar : ∀ x : M, c / 2 < (gt (sample i)).scalarAt x := by
    intro x
    have hcentered := (hsmall x).1
    have hmean := hMeanLower (sample i) htime
    have hgap :
        meanScalar (gt (sample i)) - (gt (sample i)).scalarAt x ≤
          |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| := by
      calc
        meanScalar (gt (sample i)) - (gt (sample i)).scalarAt x ≤
            |meanScalar (gt (sample i)) - (gt (sample i)).scalarAt x| :=
          le_abs_self _
        _ = |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| :=
          abs_sub_comm _ _
    linarith
  have htraceless : ∀ x : M,
      (gt (sample i)).tracelessRicciNormSqAt x < (c / 24) ^ 2 :=
    fun x ↦ (hsmall x).2
  let rho : ℝ := c / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact hhalf
  have hscalarLower : ∀ x : M, rho ≤ (gt (sample i)).scalarAt x :=
    fun x ↦ (hscalar x).le
  have hrhoThreshold : (rho / 12) ^ 2 = (c / 24) ^ 2 := by
    dsimp only [rho]
    ring
  have htracelessFloor : ∀ x : M,
      (gt (sample i)).tracelessRicciNormSqAt x < (rho / 12) ^ 2 := by
    intro x
    rw [hrhoThreshold]
    exact htraceless x
  have hfloor :
      GlobalRicciEigenvalueFloor3 (gt (sample i)) (1 / 4) :=
    (gt (sample i)).globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
      hrho hscalarLower htracelessFloor
  have hRpos : ∀ x : M, 0 < (gt (sample i)).scalarAt x :=
    fun x ↦ hhalf.trans (hscalar x)
  have hpositive : GlobalPositiveRicci3 (gt (sample i)) := by
    intro x
    apply (gt (sample i)).hasPosRicciAt_of_scalar_lower_of_traceless_lt
      hrho (hscalarLower x)
    have hsmallSq : (rho / 12) ^ 2 < (rho / 6) ^ 2 := by
      nlinarith [sq_pos_of_pos
        (div_pos hrho (by norm_num : (0 : ℝ) < 12))]
    exact (htracelessFloor x).trans hsmallSq
  have hquotient :
      GlobalPinchingQuotientBound3 (gt (sample i)) (3 / 8) :=
    (gt (sample i)).globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
      hRpos hfloor
  exact ⟨sample i, htime, hscalar, htraceless, hfloor, hpositive,
    hquotient⟩

/-- Tensor compact-reference control supplies noncollapse, while the
traceless curvature/covariant-derivative bounds supply only the traceless
density's Lipschitz estimate.  The scalar-variance Lipschitz bound remains a
separate honest hypothesis. -/
theorem exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_compactTensorReferenceFamily_of_meanLower
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B LScalar c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarVarianceLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2) LScalar)
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hc : 0 < c)
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t)) :
    ∃ t0 : ℝ, 0 ≤ t0 ∧
      (∀ x : M, c / 2 < (gt t0).scalarAt x) ∧
      (∀ x : M,
        (gt t0).tracelessRicciNormSqAt x < (c / 24) ^ 2) ∧
      GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t0) ∧
      GlobalPinchingQuotientBound3 (gt t0) (3 / 8) := by
  have hTracelessLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  exact
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_meanLower
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hNoncollapse hc hMeanLower

end Poincare
