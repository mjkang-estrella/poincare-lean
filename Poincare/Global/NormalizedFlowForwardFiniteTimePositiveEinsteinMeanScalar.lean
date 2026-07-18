import Poincare.Global.NormalizedFlowForwardAbsoluteDissipation
import Poincare.Global.NormalizedFlowScalarVarianceConcentration
import Poincare.Global.NormalizedFlowEnergyConcentrationLipschitzBridge
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity

/-!
# Forward-ray mean-scalar positive-Einstein endpoint

The geometric normalized Ricci flow is needed only for nonnegative time.
The absolute-dissipation selector already supplies a sample entirely in
`Ici 0`; restricting the Lipschitz and noncollapse contracts to the same
subtype is therefore sufficient for both scalar-variance and traceless-Ricci
concentration.  The denominator-free compact pair then produces the positive
Einstein limit without any negative-time flow extension.
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

/-- Slice-wise Lipschitz control only on the forward real ray.  Reusing the
existing arbitrary-index contract on the subtype `Ici 0` prevents any hidden
quantification over negative times. -/
def ForwardUniformClosedRiemannianLipschitzBound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (f : ℝ → M → ℝ) (L : ℝ) : Prop :=
  UniformClosedRiemannianLipschitzBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) (fun t x ↦ f t.1 x) L

/-- Ball-volume noncollapse only for metrics on the forward real ray. -/
def ForwardUniformClosedRiemannianBallVolumeLower
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) : Prop :=
  UniformClosedRiemannianBallVolumeLower
    (fun t : Ici (0 : ℝ) ↦ gt t.1)

/-- The intrinsic first-derivative contract, including its spatial `C¹`
field, restricted to nonnegative times.  This is a sufficient producer of the
forward Lipschitz contract; the raw concentration theorem below needs only
the produced Lipschitz estimate. -/
def ForwardUniformClosedRiemannianMFDerivBound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (f : ℝ → M → ℝ) (L : ℝ) : Prop :=
  UniformClosedRiemannianMFDerivBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) (fun t x ↦ f t.1 x) L

omit [MeasurableSpace M] [BorelSpace M] in
/-- A forward intrinsic derivative bound integrates to the corresponding
forward slice-wise Lipschitz estimate. -/
theorem forwardUniformClosedRiemannianLipschitzBound_of_mfderivBound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (f : ℝ → M → ℝ) {L : ℝ}
    (h : ForwardUniformClosedRiemannianMFDerivBound gt f L) :
    ForwardUniformClosedRiemannianLipschitzBound gt f L := by
  exact uniformClosedRiemannianLipschitzBound_of_mfderivBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) (fun t x ↦ f t.1 x) h

/-- Forward finite absolute dissipation supplies one nonnegative escaping
sample on which centered scalar and squared traceless Ricci are simultaneously
uniformly small.  Every analytic hypothesis used for concentration is
restricted to `Ici 0`. -/
theorem exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {LScalar LTraceless : ℝ}
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarVarianceLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2) LScalar)
    (hTracelessLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ (gt t).tracelessRicciNormSqAt x) LTraceless)
    (hUniformNoncollapse :
      ForwardUniformClosedRiemannianBallVolumeLower gt) :
    ∃ sample : ℕ → ℝ,
      (∀ i : ℕ, sample i ∈ Ici (0 : ℝ)) ∧
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ ∫ x,
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      (∀ εScalar : ℝ, 0 < εScalar →
        ∀ εTraceless : ℝ, 0 < εTraceless →
          ∀ᶠ i in atTop, ∀ x : M,
            |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| <
                εScalar ∧
              (gt (sample i)).tracelessRicciNormSqAt x < εTraceless) := by
  obtain ⟨sample, hSampleNonneg, hSampleAtTop, _hDerivativeZero,
      hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hSampleScalarLipschitz :
      UniformClosedRiemannianLipschitzBound (fun i ↦ gt (sample i))
        (fun i x ↦
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2)
        LScalar := by
    refine ⟨hScalarVarianceLipschitz.1, ?_⟩
    intro i x y
    exact hScalarVarianceLipschitz.2 ⟨sample i, hSampleNonneg i⟩ x y
  have hSampleTracelessLipschitz :
      UniformClosedRiemannianLipschitzBound (fun i ↦ gt (sample i))
        (fun i x ↦ (gt (sample i)).tracelessRicciNormSqAt x)
        LTraceless := by
    refine ⟨hTracelessLipschitz.1, ?_⟩
    intro i x y
    exact hTracelessLipschitz.2 ⟨sample i, hSampleNonneg i⟩ x y
  have hSampleNoncollapse :
      UniformClosedRiemannianBallVolumeLower
        (fun i ↦ gt (sample i)) := by
    intro r hr
    obtain ⟨volume, hvolume, hballs⟩ := hUniformNoncollapse r hr
    exact ⟨volume, hvolume,
      fun i x ↦ hballs ⟨sample i, hSampleNonneg i⟩ x⟩
  have hScalarUniform :=
    scalarAt_sub_meanScalar_eventually_uniformly_small_of_variance_tendsto_zero
      (fun i ↦ gt (sample i)) hSampleScalarLipschitz hSampleNoncollapse
        hVarianceZero
  have hTracelessUniform :=
    tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
      (fun i ↦ gt (sample i)) (by norm_num) hSampleTracelessLipschitz
        hSampleNoncollapse hEnergyZero
  refine ⟨sample, hSampleNonneg, hSampleAtTop, hVarianceZero, hEnergyZero, ?_⟩
  intro εScalar hεScalar εTraceless hεTraceless
  filter_upwards
    [hScalarUniform εScalar hεScalar,
      hTracelessUniform εTraceless hεTraceless]
    with i hScalar hTraceless
  exact fun x ↦ ⟨hScalar x, hTraceless x⟩

/-- Forward-ray version of the denominator-free direct mean-scalar endpoint.
The flow equation, moving-total derivatives, metric realization, Lipschitz
bounds, noncollapse, and mean lower bound are all required only for
nonnegative times. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    {LScalar LTraceless c : ℝ}
    (hc : 0 < c)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0))
    (hScalarVarianceLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2) LScalar)
    (hTracelessLipschitz :
      ForwardUniformClosedRiemannianLipschitzBound gt
        (fun t x ↦ (gt t).tracelessRicciNormSqAt x) LTraceless)
    (hUniformNoncollapse :
      ForwardUniformClosedRiemannianBallVolumeLower gt)
    (hMeanLower : ∀ t ∈ Ici (0 : ℝ), c ≤ meanScalar (gt t))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  obtain ⟨sample, hSampleNonneg, hSampleAtTop, _hVarianceZero,
      _hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation_Ici
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hMeanSample : ∀ᶠ i in atTop,
      c ≤ meanScalar (gt (sample i)) :=
    Eventually.of_forall fun i ↦
      hMeanLower (sample i) (hSampleNonneg i)
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
      (fun i ↦ parameter ⟨sample i, hSampleNonneg i⟩)
  · intro i
    simpa only [zero_add] using
      hRealize ⟨sample i, hSampleNonneg i⟩
  · exact hEnergyPairContinuous

end Poincare
