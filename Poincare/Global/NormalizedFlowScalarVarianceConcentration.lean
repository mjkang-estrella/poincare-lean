import Poincare.Global.NormalizedFlowEnergyConcentration

/-!
# Uniform concentration of normalized-flow scalar variance

Finite absolute normalized-flow dissipation selects one escaping sequence on
which both the centered-scalar variance and the total squared traceless-Ricci
energy tend to zero.  This file applies the same varying-metric concentration
argument to the nonnegative density

`(scalarAt - meanScalar) ^ 2`.

The scalar-variance density and the traceless-Ricci density have separate
uniform Lipschitz hypotheses.  In particular, no scalar-gradient estimate is
inferred from a covariant-derivative estimate for traceless Ricci.  A shared
ball-volume lower bound then upgrades both integral limits to simultaneous
uniform smallness along the same dissipation sample.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section RiemannianScalarVarianceConcentration

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Vanishing integrated centered-scalar variance upgrades to uniform
smallness of the squared centered-scalar density when that density has its
own uniform slice-wise Lipschitz bound and the metric sequence is uniformly
noncollapsed at every fixed radius. -/
theorem centeredScalarSqAt_eventually_uniformly_small_of_variance_tendsto_zero
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    {L : ℝ}
    (hLipschitz : UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ ((g i).scalarAt x - meanScalar (g i)) ^ 2) L)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hVarianceZero :
      Tendsto
        (fun i ↦ ∫ x, ((g i).scalarAt x - meanScalar (g i)) ^ 2
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M,
        ((g i).scalarAt x - meanScalar (g i)) ^ 2 < ε := by
  rcases hLipschitz with ⟨hL, hLip⟩
  apply
    eventually_forall_lt_of_integral_tendsto_zero_of_uniform_lipschitz_ball_lower
      (fun i ↦ volumeMeasure (g i))
      (fun i x ↦ ((g i).scalarAt x - meanScalar (g i)) ^ 2)
      (fun i x y ↦ closedRiemannianDistance (g i) x y)
      (fun i x r ↦ closedRiemannianBall (g i) x r)
      hL
  · intro i x r y hy
    exact (mem_closedRiemannianBall_iff (g i) x y r).1 hy
  · intro i x r
    exact closedRiemannianBall_measurableSet (g i) x r
  · intro i x r
    letI : IsFiniteMeasure (volumeMeasure (g i)) :=
      volumeMeasure_isFiniteMeasure (g i)
    exact ne_top_of_le_ne_top
      (measure_ne_top (volumeMeasure (g i)) Set.univ)
      (measure_mono (Set.subset_univ _))
  · exact hNoncollapse
  · exact hLip
  · intro i
    exact centeredScalarSq_integrable (g i)
  · intro i x
    exact sq_nonneg ((g i).scalarAt x - meanScalar (g i))
  · exact hVarianceZero

/-- Equivalent uniform-decay statement for the absolute centered scalar,
obtained by applying concentration at the threshold `ε²`. -/
theorem scalarAt_sub_meanScalar_eventually_uniformly_small_of_variance_tendsto_zero
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    {L : ℝ}
    (hLipschitz : UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ ((g i).scalarAt x - meanScalar (g i)) ^ 2) L)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hVarianceZero :
      Tendsto
        (fun i ↦ ∫ x, ((g i).scalarAt x - meanScalar (g i)) ^ 2
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M,
        |(g i).scalarAt x - meanScalar (g i)| < ε := by
  intro ε hε
  filter_upwards
    [centeredScalarSqAt_eventually_uniformly_small_of_variance_tendsto_zero
      g hLipschitz hNoncollapse hVarianceZero (ε ^ 2) (sq_pos_of_pos hε)]
    with i hi
  intro x
  exact abs_lt_of_sq_lt_sq (hi x) hε.le

end RiemannianScalarVarianceConcentration

section NormalizedFlowScalarVarianceConcentration

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Finite absolute dissipation produces one escaping sample on which both
centered scalar and traceless Ricci are uniformly small.

The conclusion records both integral limits and combines the two pointwise
concentration statements under one eventuality, making explicit that no
second subsequence is selected. -/
theorem exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {LScalar LTraceless : ℝ}
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
    (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt) :
    ∃ sample : ℕ → ℝ,
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
  obtain ⟨sample, hsample, _hDerivativeZero, hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hSampleScalarLipschitz :
      UniformClosedRiemannianLipschitzBound (fun i ↦ gt (sample i))
        (fun i x ↦
          ((gt (sample i)).scalarAt x - meanScalar (gt (sample i))) ^ 2)
        LScalar :=
    ⟨hScalarVarianceLipschitz.1,
      fun i x y ↦ hScalarVarianceLipschitz.2 (sample i) x y⟩
  have hSampleTracelessLipschitz :
      UniformClosedRiemannianLipschitzBound (fun i ↦ gt (sample i))
        (fun i x ↦ (gt (sample i)).tracelessRicciNormSqAt x)
        LTraceless :=
    ⟨hTracelessLipschitz.1,
      fun i x y ↦ hTracelessLipschitz.2 (sample i) x y⟩
  have hSampleNoncollapse :
      UniformClosedRiemannianBallVolumeLower
        (fun i ↦ gt (sample i)) := by
    intro r hr
    obtain ⟨v, hv, hvr⟩ := hUniformNoncollapse r hr
    exact ⟨v, hv, fun i x ↦ hvr (sample i) x⟩
  have hScalarUniform :=
    scalarAt_sub_meanScalar_eventually_uniformly_small_of_variance_tendsto_zero
      (fun i ↦ gt (sample i)) hSampleScalarLipschitz
        hSampleNoncollapse hVarianceZero
  have hTracelessUniform :=
    tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
      (fun i ↦ gt (sample i)) (by norm_num) hSampleTracelessLipschitz
        hSampleNoncollapse hEnergyZero
  refine ⟨sample, hsample, hVarianceZero, hEnergyZero, ?_⟩
  intro εScalar hεScalar εTraceless hεTraceless
  filter_upwards
    [hScalarUniform εScalar hεScalar,
      hTracelessUniform εTraceless hεTraceless]
    with i hScalarSmall hTracelessSmall
  intro x
  exact ⟨hScalarSmall x, hTracelessSmall x⟩

/-- Eventual uniform centered-scalar decay converts an eventual positive
mean-scalar floor into a pointwise scalar floor of half the same size. -/
theorem scalarAt_eventually_gt_half_of_centeredScalar_uniform_decay_of_meanLower
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (sample : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ᶠ i in atTop,
      c ≤ meanScalar (gt (sample i)))
    (hCenteredUniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < ε) :
    ∀ᶠ i in atTop, ∀ x : M,
      c / 2 < (gt (sample i)).scalarAt x := by
  have hhalf : 0 < c / 2 := div_pos hc (by norm_num)
  filter_upwards [hMeanLower, hCenteredUniform (c / 2) hhalf]
    with i hMean hCentered
  intro x
  have hCenteredAt := hCentered x
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

/-- Uniform positive mean scalar plus finite absolute dissipation yields one
escaping sample with simultaneous scalar-variance/traceless-Ricci uniform
concentration and an eventual positive pointwise scalar floor.

Unlike the bounded-normalization-primitive route, this conclusion is only
along the selected sample; that is the exact strength supplied by the
vanishing variance integral. -/
theorem exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_meanLower
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {LScalar LTraceless c : ℝ}
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
    (hMeanLower : ∀ t : ℝ, c ≤ meanScalar (gt t)) :
    ∃ sample : ℕ → ℝ,
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
              (gt (sample i)).tracelessRicciNormSqAt x < εTraceless) ∧
      (∀ᶠ i in atTop, ∀ x : M,
        c / 2 < (gt (sample i)).scalarAt x) := by
  obtain ⟨sample, hsample, hVarianceZero, hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hCenteredUniform : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < ε := by
    intro ε hε
    filter_upwards [hUniform ε hε 1 (by norm_num)] with i hi
    exact fun x ↦ (hi x).1
  have hPointwiseLower :
      ∀ᶠ i in atTop, ∀ x : M,
        c / 2 < (gt (sample i)).scalarAt x :=
    scalarAt_eventually_gt_half_of_centeredScalar_uniform_decay_of_meanLower
      gt sample hc (Eventually.of_forall fun i ↦ hMeanLower (sample i))
        hCenteredUniform
  exact ⟨sample, hsample, hVarianceZero, hEnergyZero, hUniform,
    hPointwiseLower⟩

end NormalizedFlowScalarVarianceConcentration

end Poincare
