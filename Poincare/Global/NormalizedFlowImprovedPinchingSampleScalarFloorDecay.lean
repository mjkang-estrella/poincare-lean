import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowScalarVarianceConcentration

/-!
# Improved-pinching decay from a scalar floor only on the sample

The exponent-zero traceless-pinching quotient needs a quantitative scalar
floor only when converting uniform `|Ric°|²` smallness into quotient
smallness.  It does not need that floor at every forward time.  This file
therefore weakens the decay bridge as follows:

* along the escaping sample, assume an eventual uniform positive scalar floor;
* on the whole forward ray, assume only pointwise scalar positivity, spatial
  `C²` regularity, and Hamilton antitonicity.

The first theorem proves decay on the shifted sample.  The second invokes the
abstract nonnegative-antitone bridge to obtain decay of the full maximum
track.  A final normalized-flow wrapper gets the sampled scalar floor from
the simultaneous scalar-variance/traceless-Ricci concentration theorem and a
positive mean-scalar lower bound.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- A scalar floor only at the escaping sample times converts uniform sampled
traceless-Ricci decay into decay of the shifted sampled exponent-zero
pinching maximum. -/
theorem shiftedSample_tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_of_eventual_scalar_floor
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hForwardScalarPos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hSampleEventuallyForward : ∀ᶠ i in atTop, t0 ≤ sample i)
    (hSampleScalarLower : ∀ᶠ i in atTop, ∀ x : M,
      rho ≤ (gt (sample i)).scalarAt x)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < epsilon) :
    Tendsto
      (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (sample i - t0))
      atTop (nhds 0) := by
  let shiftedSample : ℕ → ℝ := fun i ↦ sample i - t0
  have hShiftedAtTop : Tendsto shiftedSample atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards
      [hSampleAtTop.eventually (eventually_ge_atTop (b + t0))]
      with i hi
    dsimp only [shiftedSample]
    linarith
  have hShiftedEventuallyNonneg : ∀ᶠ i in atTop, 0 ≤ shiftedSample i := by
    filter_upwards [hSampleEventuallyForward] with i hi
    dsimp only [shiftedSample]
    exact sub_nonneg.mpr hi
  change Tendsto
    (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (shiftedSample i))
    atTop (nhds 0)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hShiftedEventuallyNonneg] with i hi
    exact ha.trans_le <|
      tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
        gt t0 0 (shiftedSample i)
          (hForwardScalarPos (shiftedSample i) hi)
          (hQTwo (shiftedSample i) hi)
  · intro eta heta
    have hepsilon : 0 < eta * rho ^ 2 :=
      mul_pos heta (sq_pos_of_pos hrho)
    filter_upwards
      [hShiftedEventuallyNonneg, hSampleScalarLower,
        hUniformSmall (eta * rho ^ 2) hepsilon]
      with i hi hScalarLower hsmall
    have htime : t0 + shiftedSample i = sample i := by
      dsimp only [shiftedSample]
      ring
    obtain ⟨xmax, hmax⟩ :=
      exists_tracelessPinchingAt_isMaxOn
        (g := gt (sample i)) 0 (by
          intro x
          simpa only [htime] using hQTwo (shiftedSample i) hi x)
    rw [tracelessPinchingMaximumTrack, htime,
      tracelessPinchingMaximumAt_eq_of_isMaxOn
        (g := gt (sample i)) 0 hmax]
    rw [(gt (sample i)).tracelessPinchingAt_eq]
    norm_num
    have hRLower : rho ≤ (gt (sample i)).scalarAt xmax :=
      hScalarLower xmax
    have hRpos : 0 < (gt (sample i)).scalarAt xmax :=
      hrho.trans_le hRLower
    apply (div_lt_iff₀ (sq_pos_of_pos hRpos)).2
    calc
      (gt (sample i)).tracelessRicciNormSqAt xmax < eta * rho ^ 2 :=
        hsmall xmax
      _ ≤ eta * ((gt (sample i)).scalarAt xmax) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hrho.le hRpos.le).2 hRLower) heta.le

/-- Samplewise scalar control is sufficient for full forward decay: only
nonnegativity of the quotient maximum is needed away from the sample. -/
theorem tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_sample_of_eventual_scalar_floor
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hForwardScalarPos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ)))
    (sample : ℕ → ℝ)
    (hSampleAtTop : Tendsto sample atTop atTop)
    (hSampleEventuallyForward : ∀ᶠ i in atTop, t0 ≤ sample i)
    (hSampleScalarLower : ∀ᶠ i in atTop, ∀ x : M,
      rho ≤ (gt (sample i)).scalarAt x)
    (hUniformSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (gt (sample i)).tracelessRicciNormSqAt x < epsilon) :
    Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) := by
  let shiftedSample : ℕ → ℝ := fun i ↦ sample i - t0
  have hShiftedAtTop : Tendsto shiftedSample atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards
      [hSampleAtTop.eventually (eventually_ge_atTop (b + t0))]
      with i hi
    dsimp only [shiftedSample]
    linarith
  have hSampleMaximumZero : Tendsto
      (fun i ↦ tracelessPinchingMaximumTrack gt t0 0 (shiftedSample i))
      atTop (nhds 0) := by
    simpa only [shiftedSample] using
      shiftedSample_tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_of_eventual_scalar_floor
        gt hrho hForwardScalarPos hQTwo sample hSampleAtTop
        hSampleEventuallyForward hSampleScalarLower hUniformSmall
  apply tendsto_zero_of_antitoneOn_Ici_of_nonneg_of_sample
    (tracelessPinchingMaximumTrack gt t0 0) shiftedSample
      _ hAntitone hShiftedAtTop hSampleMaximumZero
  intro s hs
  exact tracelessPinchingMaximumTrack_nonneg_of_scalar_pos
    gt t0 0 s (hForwardScalarPos s hs) (hQTwo s hs)

/-- The simultaneous finite-dissipation sample supplies both the uniform
traceless-Ricci decay and the eventual scalar floor needed above.  A positive
mean-scalar lower bound is used only at the sampled nonnegative times. -/
theorem tracelessPinchingMaximumTrack_tendsto_zero_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_hamilton_antitone
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {t0 LScalar LTraceless c : ℝ}
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
    (hForwardScalarPos : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt (t0 + s)).scalarAt x)
    (hQTwo : ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t0 + s)).tracelessPinchingAt y 0) x)
    (hAntitone :
      AntitoneOn (tracelessPinchingMaximumTrack gt t0 0) (Ici (0 : ℝ))) :
    Tendsto (tracelessPinchingMaximumTrack gt t0 0) atTop (nhds 0) := by
  obtain ⟨sample, hSampleAtTop, _hVarianceZero, _hEnergyZero, hUniform⟩ :=
    exists_normalizedFlow_centeredScalar_and_tracelessRicci_eventually_uniformly_small_of_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse
  have hSampleEventuallyNonnegative : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop 0)
  have hSampleEventuallyForward : ∀ᶠ i in atTop, t0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop t0)
  have hMeanSample : ∀ᶠ i in atTop,
      c ≤ meanScalar (gt (sample i)) := by
    filter_upwards [hSampleEventuallyNonnegative] with i hi
    exact hMeanLower (sample i) hi
  have hCenteredUniform : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        |(gt (sample i)).scalarAt x - meanScalar (gt (sample i))| < epsilon := by
    intro epsilon hepsilon
    filter_upwards [hUniform epsilon hepsilon 1 (by norm_num)]
      with i hi
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
    filter_upwards [hUniform 1 (by norm_num) epsilon hepsilon]
      with i hi
    exact fun x ↦ (hi x).2
  exact
    tracelessPinchingMaximumTrack_tendsto_zero_of_uniform_tracelessRicci_sample_of_eventual_scalar_floor
      gt (div_pos hc (by norm_num)) hForwardScalarPos hQTwo hAntitone
      sample hSampleAtTop hSampleEventuallyForward hSampleScalarLower
      hUniformSmall

end Poincare
