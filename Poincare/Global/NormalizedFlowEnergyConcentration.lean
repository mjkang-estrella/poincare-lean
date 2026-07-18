import Poincare.Global.NormalizedFlowAbsoluteDissipation

/-!
# Uniform concentration from vanishing normalized-flow energy

This file isolates a compactness-free consequence of the normalized-flow
energy extraction.  A nonnegative density whose integrals tend to zero tends
to zero uniformly provided that

* the density has one uniform Lipschitz constant, and
* balls of each fixed positive radius have a uniform positive measure lower
  bound.

The abstract theorem permits both the distance and the measures to vary with
the sequence index.  Its Riemannian specialization therefore applies directly
to a sequence of evolving metrics; it does not assume a limit metric, a closed
invariant range, or any metric-orbit compactness.

For squared traceless Ricci curvature, the two genuine geometric inputs left
visible by this reduction are a uniform spatial first-derivative bound (used
through the Lipschitz estimate) and uniform noncollapse for Riemannian balls.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section AbstractConcentration

variable {X : Type u} [MeasurableSpace X]

/--
Abstract uniform `L¹`-to-`L∞` concentration with an index-dependent distance,
ball family, and measure.

The ball hypotheses intentionally mention only the properties used in the
proof.  Thus the theorem applies to genuinely varying metric spaces without
installing a different metric typeclass for every index.
-/
theorem eventually_forall_lt_of_integral_tendsto_zero_of_uniform_lipschitz_ball_lower
    (μ : ℕ → Measure X) (f : ℕ → X → ℝ)
    (distance : ℕ → X → X → ℝ)
    (ball : ℕ → X → ℝ → Set X)
    {L : ℝ} (hL : 0 < L)
    (hBallDistance : ∀ i x r y, y ∈ ball i x r → distance i y x < r)
    (hBallMeasurable : ∀ i x r, MeasurableSet (ball i x r))
    (hBallFinite : ∀ i x r, μ i (ball i x r) ≠ (⊤ : ℝ≥0∞))
    (hBallLower : ∀ r : ℝ, 0 < r →
      ∃ v : ℝ, 0 < v ∧ ∀ i x, v ≤ (μ i).real (ball i x r))
    (hLipschitz : ∀ i x y,
      |f i y - f i x| ≤ L * distance i y x)
    (hIntegrable : ∀ i, Integrable (f i) (μ i))
    (hNonneg : ∀ i x, 0 ≤ f i x)
    (hIntegralZero :
      Tendsto (fun i ↦ ∫ x, f i x ∂(μ i)) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x : X, f i x < ε := by
  intro ε hε
  let r : ℝ := ε / (2 * L)
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) hL)
  obtain ⟨v, hv, hvolume⟩ := hBallLower r hr
  have hthreshold : 0 < (ε / 2) * v :=
    mul_pos (div_pos hε (by norm_num)) hv
  filter_upwards [hIntegralZero.eventually (Iio_mem_nhds hthreshold)] with i hi
  intro x
  by_contra hnot
  have hx : ε ≤ f i x := le_of_not_gt hnot
  let s : Set X := ball i x r
  have hsMeasurable : MeasurableSet s := hBallMeasurable i x r
  have hsFinite : μ i s ≠ (⊤ : ℝ≥0∞) := hBallFinite i x r
  have hsLower : v ≤ (μ i).real s := hvolume i x
  have hpointLower : ∀ y ∈ s, ε / 2 ≤ f i y := by
    intro y hy
    have hdist : distance i y x < r := hBallDistance i x r y hy
    have hscaled : L * distance i y x < ε / 2 := by
      have hmul : L * distance i y x < L * r :=
        mul_lt_mul_of_pos_left hdist hL
      have hLr : L * r = ε / 2 := by
        dsimp only [r]
        field_simp
      simpa only [hLr] using hmul
    have hosc : |f i y - f i x| < ε / 2 :=
      (hLipschitz i x y).trans_lt hscaled
    have hsub : f i x - f i y ≤ |f i y - f i x| := by
      rw [abs_sub_comm]
      exact le_abs_self (f i x - f i y)
    linarith
  have hlocalLower :
      (ε / 2) * (μ i).real s ≤ ∫ y in s, f i y ∂(μ i) :=
    setIntegral_ge_of_const_le_real hsMeasurable hsFinite hpointLower
      (hIntegrable i).integrableOn
  have hlocalGlobal :
      (∫ y in s, f i y ∂(μ i)) ≤ ∫ y, f i y ∂(μ i) :=
    setIntegral_le_integral (hIntegrable i)
      (Eventually.of_forall fun y ↦ hNonneg i y)
  have hcontradiction :
      (ε / 2) * v ≤ ∫ y, f i y ∂(μ i) := by
    calc
      (ε / 2) * v ≤ (ε / 2) * (μ i).real s :=
        mul_le_mul_of_nonneg_left hsLower (div_nonneg hε.le (by norm_num))
      _ ≤ ∫ y in s, f i y ∂(μ i) := hlocalLower
      _ ≤ ∫ y, f i y ∂(μ i) := hlocalGlobal
  exact (not_le_of_gt hi) hcontradiction

/--
Fixed-metric-space form of the abstract concentration theorem.  The measures
may still vary with the sequence index.
-/
theorem eventually_forall_lt_of_integral_tendsto_zero_of_uniform_lipschitz_noncollapse
    [PseudoMetricSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (f : ℕ → X → ℝ)
    {K : ℝ≥0} (hK : 0 < K)
    (hFinite : ∀ i, μ i Set.univ ≠ (⊤ : ℝ≥0∞))
    (hBallLower : ∀ r : ℝ, 0 < r →
      ∃ v : ℝ, 0 < v ∧ ∀ i x, v ≤ (μ i).real (Metric.ball x r))
    (hLipschitz : ∀ i, LipschitzWith K (f i))
    (hIntegrable : ∀ i, Integrable (f i) (μ i))
    (hNonneg : ∀ i x, 0 ≤ f i x)
    (hIntegralZero :
      Tendsto (fun i ↦ ∫ x, f i x ∂(μ i)) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x : X, f i x < ε := by
  apply
    eventually_forall_lt_of_integral_tendsto_zero_of_uniform_lipschitz_ball_lower
      μ f (fun _ x y ↦ dist x y) (fun _ x r ↦ Metric.ball x r)
      (by exact_mod_cast hK)
  · intro i x r y hy
    simpa only [Metric.mem_ball, dist_comm] using hy
  · intro i x r
    exact Metric.isOpen_ball.measurableSet
  · intro i x r
    exact ne_top_of_le_ne_top (hFinite i) (measure_mono (Set.subset_univ _))
  · exact hBallLower
  · intro i x y
    simpa only [Real.dist_eq] using (hLipschitz i).dist_le_mul y x
  · exact hIntegrable
  · exact hNonneg
  · exact hIntegralZero

end AbstractConcentration

section RiemannianConcentration

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Ordinary Riemannian distance, exposed without installing a global metric
instance.  This lets one compare distances belonging to a sequence of
different metrics in a single statement. -/
def closedRiemannianDistance
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) : ℝ :=
  letI : MetricSpace M := g.toMetricSpace
  dist x y

/-- An open ball for the metric induced by `g`, again exposed without a global
metric instance. -/
def closedRiemannianBall
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (r : ℝ) : Set M :=
  letI : MetricSpace M := g.toMetricSpace
  Metric.ball x r

theorem mem_closedRiemannianBall_iff
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) (r : ℝ) :
    y ∈ closedRiemannianBall g x r ↔ closedRiemannianDistance g y x < r := by
  letI : MetricSpace M := g.toMetricSpace
  rfl

theorem closedRiemannianBall_measurableSet
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (r : ℝ) :
    MeasurableSet (closedRiemannianBall g x r) := by
  letI : MetricSpace M := g.toMetricSpace
  simpa only [closedRiemannianBall] using Metric.isOpen_ball.measurableSet

/-- A uniform spatial Lipschitz estimate measured in each slice's own
Riemannian distance. -/
def UniformClosedRiemannianLipschitzBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) (L : ℝ) : Prop :=
  0 < L ∧ ∀ i x y,
    |f i y - f i x| ≤ L * closedRiemannianDistance (g i) y x

/-- Uniform positive lower volume for every fixed positive-radius ball along a
metric sequence.  This is the exact qualitative noncollapse used by the
concentration proof. -/
def UniformClosedRiemannianBallVolumeLower
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M) : Prop :=
  ∀ r : ℝ, 0 < r →
    ∃ v : ℝ, 0 < v ∧ ∀ i x,
      v ≤ (volumeMeasure (g i)).real (closedRiemannianBall (g i) x r)

/-- Quantitative three-dimensional ball noncollapse up to a uniform radius. -/
def UniformClosedRiemannianCubicNoncollapse
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (κ r₀ : ℝ) : Prop :=
  0 < κ ∧ 0 < r₀ ∧ ∀ i x r, 0 < r → r ≤ r₀ →
    κ * r ^ 3 ≤
      (volumeMeasure (g i)).real (closedRiemannianBall (g i) x r)

/-- Cubic noncollapse on a common positive scale supplies the qualitative
fixed-radius lower bound used by concentration. -/
theorem uniformClosedRiemannianBallVolumeLower_of_cubicNoncollapse
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    {κ r₀ : ℝ} (h : UniformClosedRiemannianCubicNoncollapse g κ r₀) :
    UniformClosedRiemannianBallVolumeLower g := by
  rcases h with ⟨hκ, hr₀, hcollapse⟩
  intro r hr
  let ρ : ℝ := min r r₀
  have hρ : 0 < ρ := lt_min hr hr₀
  have hρr : ρ ≤ r := min_le_left _ _
  have hρr₀ : ρ ≤ r₀ := min_le_right _ _
  refine ⟨κ * ρ ^ 3, mul_pos hκ (pow_pos hρ 3), ?_⟩
  intro i x
  have hsmall := hcollapse i x ρ hρ hρr₀
  have hsubset :
      closedRiemannianBall (g i) x ρ ⊆
        closedRiemannianBall (g i) x r := by
    letI : MetricSpace M := (g i).toMetricSpace
    simpa only [closedRiemannianBall] using
      (Metric.ball_subset_ball hρr : Metric.ball x ρ ⊆ Metric.ball x r)
  letI : IsFiniteMeasure (volumeMeasure (g i)) :=
    volumeMeasure_isFiniteMeasure (g i)
  exact hsmall.trans (measureReal_mono hsubset)

/--
Vanishing total squared traceless-Ricci energy along a sequence of metrics
upgrades to uniform pointwise smallness, without extracting a limit metric.
-/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L : ℝ}
    (hLipschitz : UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < ε := by
  rcases hLipschitz with ⟨hL, hLip⟩
  apply
    eventually_forall_lt_of_integral_tendsto_zero_of_uniform_lipschitz_ball_lower
      (fun i ↦ volumeMeasure (g i))
      (fun i x ↦ (g i).tracelessRicciNormSqAt x)
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
    exact tracelessRicciNormSqAt_integrable (g i)
  · intro i x
    exact (g i).tracelessRicciNormSqAt_nonneg x hn
  · exact hEnergyZero

/-- Common-scale cubic noncollapse is a quantitative geometric source of the
ball-volume hypothesis in the preceding theorem. -/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_cubicNoncollapse
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L κ r₀ : ℝ}
    (hLipschitz : UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianCubicNoncollapse g κ r₀)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < ε :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
    g hn hLipschitz
      (uniformClosedRiemannianBallVolumeLower_of_cubicNoncollapse g hNoncollapse)
      hEnergyZero

end RiemannianConcentration

section NormalizedFlowConcentration

variable {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Finite absolute normalized-flow dissipation produces an escaping sequence on
which squared traceless Ricci curvature tends to zero uniformly, provided the
sampled metrics obey uniform spatial Lipschitz and ball-volume lower bounds.

This strengthens the existing integral-energy extraction and remains entirely
finite-time: no limiting metric or compactness hypothesis appears.
-/
theorem exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L : ℝ}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ i in atTop, ∀ x : M,
          (gt (sample i)).tracelessRicciNormSqAt x < ε) := by
  obtain ⟨sample, hsample, _hDerivativeZero, _hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  refine ⟨sample, hsample, hEnergyZero, ?_⟩
  have hSampleLipschitz :
      UniformClosedRiemannianLipschitzBound (fun i ↦ gt (sample i))
        (fun i x ↦ (gt (sample i)).tracelessRicciNormSqAt x) L :=
    ⟨hUniformLipschitz.1,
      fun i x y ↦ hUniformLipschitz.2 (sample i) x y⟩
  have hSampleNoncollapse :
      UniformClosedRiemannianBallVolumeLower (fun i ↦ gt (sample i)) := by
    intro r hr
    obtain ⟨v, hv, hvr⟩ := hUniformNoncollapse r hr
    exact ⟨v, hv, fun i x ↦ hvr (sample i) x⟩
  exact tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
    (fun i ↦ gt (sample i))
    (by norm_num)
    hSampleLipschitz
    hSampleNoncollapse
    hEnergyZero

/-- Quantitative noncollapse version of the compactness-free finite-time
normalized-flow concentration endpoint. -/
theorem exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_cubicNoncollapse
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L κ r₀ : ℝ}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse :
      UniformClosedRiemannianCubicNoncollapse gt κ r₀) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ i in atTop, ∀ x : M,
          (gt (sample i)).tracelessRicciNormSqAt x < ε) :=
  exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hUniformLipschitz
      (uniformClosedRiemannianBallVolumeLower_of_cubicNoncollapse
        gt hUniformNoncollapse)

end NormalizedFlowConcentration

end Poincare
