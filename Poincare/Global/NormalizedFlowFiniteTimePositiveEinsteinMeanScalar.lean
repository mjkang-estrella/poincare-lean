import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinstein
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity

/-!
# Positive Einstein limit from a positive mean-scalar floor

This module composes scalar/traceless concentration, samplewise scalar-floor
decay, and the sampled compact-parameterization limit consumer.

The quantitative pointwise scalar floor is used only eventually on the one
escaping dissipation sample.  On the full forward ray, scalar curvature is
assumed merely positive.  Consequently neither a global constant pointwise
scalar floor nor a bounded normalization primitive appears in the endpoint.
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

local notation "I" => closedSmoothModelWithCorners 3

/-- End-to-end positive-Einstein endpoint from finite absolute dissipation
and a positive mean-scalar floor, using the denominator-free scalar-minimum /
squared-traceless-Ricci-maximum compact pair.

The concentration sample already makes squared traceless Ricci uniformly
small.  Consequently this route needs no forward scalar-positivity premise,
no spatial pinching-quotient regularity, and no continuity of a quotient on
the compact parameter family. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    {LScalar LTraceless c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
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
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨sample, hSampleAtTop, _hVarianceZero, _hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hSampleEventuallyNonnegative : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop 0)
  have hMeanSample : ∀ᶠ i in atTop,
      c ≤ meanScalar (gt (sample i)) := by
    filter_upwards [hSampleEventuallyNonnegative] with i hi
    exact hMeanLower (sample i) hi
  have hCenteredUniform : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hUniform epsilon hepsilon 1 (by norm_num)] with i hi
    exact fun x ↦ (hi x).1
  have hSampleScalarLower : ∀ᶠ i in atTop, ∀ x : M,
      c / 2 ≤ (gt (sample i)).scalarAt x := by
    filter_upwards
      [scalarAt_eventually_gt_half_of_centeredScalar_uniform_decay_of_meanLower
        gt sample hc hMeanSample hCenteredUniform]
      with i hi
    exact fun x ↦ (hi x).le
  have hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt ((0 : ℝ) + sample i)).tracelessRicciNormSqAt x < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hUniform 1 (by norm_num) epsilon hepsilon] with i hi
    simpa only [zero_add] using fun x ↦ (hi x).2
  have hScalarLowerSample : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c / 2 ≤ (gt ((0 : ℝ) + sample i)).scalarAt x := by
    filter_upwards [hSampleScalarLower] with i hi
    intro _hSampleNonnegative x
    simpa only [zero_add] using hi x
  have hEnergyPairContinuous : Continuous (fun k ↦
      closedMetricScalarMinimumTracelessRicciMaximumPair (metric k)) :=
    continuous_closedMetricScalarMinimumTracelessRicciMaximumPair_comp_of_joint
      metric hJointScalar hJointTraceless
  apply
    positiveEinsteinMetric3_of_sampled_uniform_tracelessRicciNormSqAt_tendsto_zero_of_compact_parameterization
      (t0 := 0) (c := c / 2) gt sample hSampleAtTop
      (div_pos hc (by norm_num)) hUniformSmall hScalarLowerSample metric
      (fun i ↦ parameter (sample i))
  · intro i
    simpa only [zero_add] using hRealize (sample i)
  · exact hEnergyPairContinuous

/-- End-to-end positive-Einstein endpoint from finite absolute dissipation
and a positive mean-scalar floor.

The compact family is used only to realize a cluster point of the invariant
pairs along the selected sample.  The analytic concentration inputs retain
separate Lipschitz hypotheses for scalar variance and traceless Ricci. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization_of_relativePinchingMaximum
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    {LScalar LTraceless c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
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
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  have hRposForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt ((0 : ℝ) + s)).scalarAt x := by
    intro s hs x
    simpa only [zero_add] using hForwardScalarPos s hs x
  have hTQTwoForward : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt ((0 : ℝ) + s)).tracelessPinchingAt y 0) x := by
    intro s hs x
    simpa only [zero_add] using hTQTwo s hs x
  obtain ⟨sample, hSampleAtTop, _hVarianceZero, _hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hSampleEventuallyNonnegative : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop 0)
  have hMeanSample : ∀ᶠ i in atTop,
      c ≤ meanScalar (gt (sample i)) := by
    filter_upwards [hSampleEventuallyNonnegative] with i hi
    exact hMeanLower (sample i) hi
  have hCenteredUniform : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hUniform epsilon hepsilon 1 (by norm_num)] with i hi
    exact fun x ↦ (hi x).1
  have hSampleScalarLower : ∀ᶠ i in atTop, ∀ x : M,
      c / 2 ≤ (gt (sample i)).scalarAt x := by
    filter_upwards
      [scalarAt_eventually_gt_half_of_centeredScalar_uniform_decay_of_meanLower
        gt sample hc hMeanSample hCenteredUniform]
      with i hi
    exact fun x ↦ (hi x).le
  have hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hUniform 1 (by norm_num) epsilon hepsilon] with i hi
    exact fun x ↦ (hi x).2
  have hMaximumSampleZero : Tendsto
      (fun i ↦ tracelessPinchingMaximumTrack gt 0 0 (sample i))
      atTop (nhds 0) := by
    simpa only [sub_zero] using
      shiftedSample_tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_of_eventual_scalar_floor
        (t0 := 0) gt (div_pos hc (by norm_num)) hRposForward
        hTQTwoForward sample hSampleAtTop hSampleEventuallyNonnegative
        hSampleScalarLower hUniformSmall
  have hScalarLowerSample : ∀ᶠ i in atTop,
      0 ≤ sample i → ∀ x : M,
        c / 2 ≤ (gt ((0 : ℝ) + sample i)).scalarAt x := by
    filter_upwards [hSampleScalarLower] with i hi
    intro _hSampleNonnegative x
    simpa only [zero_add] using hi x
  apply
    positiveEinsteinMetric3_of_sampled_relativePinchingMaximum_tendsto_zero_of_compact_parameterization
      (t0 := 0) (c := c / 2) gt sample hSampleAtTop
      (div_pos hc (by norm_num)) hMaximumSampleZero hScalarLowerSample
      metric (fun i ↦ parameter (sample i))
  · intro i
    simpa only [zero_add] using hRealize (sample i)
  · exact hInvariantContinuous

/-- Tensor compact-reference control derives the traceless-density Lipschitz
bound and noncollapse used above.  The scalar-variance Lipschitz estimate
remains an independent hypothesis. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B LScalar c : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hc : 0 < c)
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
    (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
    (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x)
    (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
    (hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k))) :
    PositiveEinsteinMetric3 M := by
  have hTracelessLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization_of_relativePinchingMaximum
      gt metric parameter hRealize hc hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation
      hScalarVarianceLipschitz hTracelessLipschitz hNoncollapse
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

end Poincare
