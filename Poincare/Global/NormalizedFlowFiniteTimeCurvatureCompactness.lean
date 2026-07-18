import Poincare.Global.ClosedRiemannianBallVolumeLower
import Poincare.Global.ClosedRiemannianDistanceComparison
import Poincare.Global.NormalizedFlowEnergyConcentrationCurvatureDerivative
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching

/-!
# Finite pinched slices from curvature derivatives and compact metric control

The finite-time positive-Ricci theorems consume two abstract uniform inputs:
a Lipschitz bound for squared traceless Ricci curvature and qualitative ball
noncollapse.  This module supplies both from geometric data closer to a
Hamilton compactness argument.

Uniform intrinsic bounds on `Ric°` and `∇ Ric°` give the Lipschitz estimate.
A compact metric parameter space, continuous positive reference-comparison
factors, and pointwise distance/volume comparisons give uniform noncollapse.
The resulting theorems retain no Lipschitz or ball-volume premise.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section CompactReferenceFamily

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Proof-bearing compact reference comparison data for a metric family. -/
structure CompactReferenceMetricFamilyData
    (K : Type v) [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M) where
  referenceMetric : ClosedSmoothRiemannianMetric 3 M
  distanceFactor : K → ℝ
  volumeFactor : K → ℝ
  distanceFactor_continuous : Continuous distanceFactor
  volumeFactor_continuous : Continuous volumeFactor
  distanceFactor_pos : ∀ k, 0 < distanceFactor k
  volumeFactor_pos : ∀ k, 0 < volumeFactor k
  distance_le : ∀ k x y,
    closedRiemannianDistance (metric k) y x ≤
      distanceFactor k *
        closedRiemannianDistance referenceMetric y x
  volume_le : ∀ k (A : Set M), MeasurableSet A →
    volumeFactor k * (volumeMeasure referenceMetric).real A ≤
      (volumeMeasure (metric k)).real A

namespace CompactReferenceMetricFamilyData

variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable {metric : K → ClosedSmoothRiemannianMetric 3 M}

/-- Compact reference comparison data supply uniform noncollapse for the
whole ambient metric family. -/
theorem uniformBallVolumeLower
    (data : CompactReferenceMetricFamilyData K metric) :
    UniformClosedRiemannianBallVolumeLower metric :=
  uniformClosedRiemannianBallVolumeLower_of_compact_referenceComparison
    data.referenceMetric metric data.distanceFactor data.volumeFactor
    data.distanceFactor_continuous data.volumeFactor_continuous
    data.distanceFactor_pos data.volumeFactor_pos
    data.distance_le data.volume_le

/-- Every family realized through the compact metric family inherits the
same uniform noncollapse. -/
theorem uniformBallVolumeLower_of_realizes
    (data : CompactReferenceMetricFamilyData K metric)
    {iota : Type*} (parameter : iota → K)
    (g : iota → ClosedSmoothRiemannianMetric 3 M)
    (hRealize : ∀ i, metric (parameter i) = g i) :
    UniformClosedRiemannianBallVolumeLower g := by
  exact uniformClosedRiemannianBallVolumeLower_of_compact_parameterization
    data.referenceMetric metric parameter g hRealize
    data.distanceFactor data.volumeFactor
    data.distanceFactor_continuous data.volumeFactor_continuous
    data.distanceFactor_pos data.volumeFactor_pos
    data.distance_le data.volume_le

end CompactReferenceMetricFamilyData

/-- Tensor-level compact reference data.  Unlike
`CompactReferenceMetricFamilyData`, this structure does not assume a distance
comparison: it records only pointwise domination of the metric quadratic
forms, from which distance comparison is proved by path integration. -/
structure CompactReferenceMetricTensorFamilyData
    (K : Type v) [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M) where
  referenceMetric : ClosedSmoothRiemannianMetric 3 M
  metricFactor : K → ℝ
  volumeFactor : K → ℝ
  metricFactor_continuous : Continuous metricFactor
  volumeFactor_continuous : Continuous volumeFactor
  metricFactor_pos : ∀ k, 0 < metricFactor k
  volumeFactor_pos : ∀ k, 0 < volumeFactor k
  metric_le : ∀ k x
      (w : TangentSpace (closedSmoothModelWithCorners 3) x),
    (metric k).inner x w w ≤
      (metricFactor k) ^ 2 * referenceMetric.inner x w w
  volume_le : ∀ k (A : Set M), MeasurableSet A →
    volumeFactor k * (volumeMeasure referenceMetric).real A ≤
      (volumeMeasure (metric k)).real A

namespace CompactReferenceMetricTensorFamilyData

variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable {metric : K → ClosedSmoothRiemannianMetric 3 M}

/-- Tensor-level compact reference data supply noncollapse for the ambient
metric family. -/
theorem uniformBallVolumeLower
    (data : CompactReferenceMetricTensorFamilyData K metric) :
    UniformClosedRiemannianBallVolumeLower metric :=
  uniformClosedRiemannianBallVolumeLower_of_compact_metric_volumeReferenceComparison
    data.referenceMetric metric data.metricFactor data.volumeFactor
    data.metricFactor_continuous data.volumeFactor_continuous
    data.metricFactor_pos data.volumeFactor_pos data.metric_le data.volume_le

/-- Compact tensor data construct the older distance-comparison package by
maximizing the metric factor.  The distance estimate itself is proved from
quadratic-form domination, not retained as an additional premise. -/
theorem exists_distanceFamilyData
    (data : CompactReferenceMetricTensorFamilyData K metric) :
    Nonempty (CompactReferenceMetricFamilyData K metric) := by
  obtain ⟨kMax, _hkMax, hkMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMaxOn
      Set.univ_nonempty data.metricFactor_continuous.continuousOn
  let C : ℝ := data.metricFactor kMax
  have hUniformMetric :
      UniformClosedRiemannianMetricUpperComparison
        data.referenceMetric metric C := by
    refine ⟨data.metricFactor_pos kMax, ?_⟩
    intro k x w
    have hfactorSq : (data.metricFactor k) ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (data.metricFactor_pos k).le
        (data.metricFactor_pos kMax).le).2 <| by
          simpa only [C] using hkMax (Set.mem_univ k)
    exact (data.metric_le k x w).trans <|
      mul_le_mul_of_nonneg_right hfactorSq
        (data.referenceMetric.inner_nonneg x w)
  have hDistance :
      UniformClosedRiemannianDistanceUpperComparison
        data.referenceMetric metric C :=
    uniformClosedRiemannianDistanceUpperComparison_of_metric
      data.referenceMetric metric hUniformMetric
  exact ⟨{
    referenceMetric := data.referenceMetric
    distanceFactor := fun _ ↦ C
    volumeFactor := data.volumeFactor
    distanceFactor_continuous := continuous_const
    volumeFactor_continuous := data.volumeFactor_continuous
    distanceFactor_pos := fun _ ↦ hDistance.1
    volumeFactor_pos := data.volumeFactor_pos
    distance_le := hDistance.2
    volume_le := data.volume_le }⟩

/-- Every realized subfamily inherits the tensor-generated noncollapse. -/
theorem uniformBallVolumeLower_of_realizes
    (data : CompactReferenceMetricTensorFamilyData K metric)
    {iota : Type*} (parameter : iota → K)
    (g : iota → ClosedSmoothRiemannianMetric 3 M)
    (hRealize : ∀ i, metric (parameter i) = g i) :
    UniformClosedRiemannianBallVolumeLower g := by
  have hParameterized := data.uniformBallVolumeLower.comp parameter
  intro r hr
  rcases hParameterized r hr with ⟨v, hv, hball⟩
  refine ⟨v, hv, ?_⟩
  intro i x
  simpa only [hRealize i] using hball i x

end CompactReferenceMetricTensorFamilyData

end CompactReferenceFamily

section FinitePinchedSlice

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Finite absolute dissipation, intrinsic `Ric°`/`∇ Ric°` bounds, and a
compact reference-controlled realization of the metric orbit produce a
finite globally positive-Ricci slice.

The finite-dimensional tensor Cauchy--Schwarz contraction is proved by the
imported curvature-derivative module; neither it, a scalar Lipschitz bound,
nor ball noncollapse is assumed here.
-/
theorem exists_finite_normalizedFlow_time_global_positiveRicci_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricFamilyData K metric)
    {A B rho : ℝ} (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∀ x : M,
        (∀ (b : Module.Basis (Fin 3) ℝ
            (TangentSpace (closedSmoothModelWithCorners 3) x))
            (mu : Fin 3 → ℝ),
          (∀ i : Fin 3, (gt t).ricciEndoAt x (b i) = mu i • b i) →
            ∀ i : Fin 3,
              rho / 6 < mu i ∧ (gt t).scalarAt x / 6 < mu i) ∧
        CovariantDerivative.HasPosRicciAt (gt t).leviCivita x ∧
        (gt t).pinchingQuotientAt x ≤ 1 / 2) := by
  have hLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  exact
    exists_finite_normalizedFlow_time_global_positiveRicci_of_finiteAbsoluteDissipation
      gt hrho hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hLipschitz
      hNoncollapse hScalarLower

/-- The same raw curvature and compact-reference inputs produce the stronger
`R/4` eigenvalue floor and `Q <= 3/8` finite slice used by Hamilton's forward
pinching theorem. -/
theorem exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactReferenceFamily
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricFamilyData K metric)
    {A B rho : ℝ} (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x) :
    ∃ t : ℝ, 0 ≤ t ∧
      GlobalRicciEigenvalueFloor3 (gt t) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t) ∧
      GlobalPinchingQuotientBound3 (gt t) (3 / 8) := by
  have hLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  exact
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation
      gt hrho hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hLipschitz
      hNoncollapse hScalarLower

/--
Tensor-level compact reference control is enough for the strong finite
Hamilton slice.  In particular, no distance comparison, Lipschitz bound, or
ball-volume lower bound appears in the input.
-/
theorem exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation_of_covariantDerivativeBound_of_compactTensorReferenceFamily
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t, metric (parameter t) = gt t)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {A B rho : ℝ} (hrho : 0 < rho)
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
    (hCOne : UniformTracelessRicciEnergyCOne gt)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
    (hScalarLower : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      rho ≤ (gt t).scalarAt x) :
    ∃ t : ℝ, 0 ≤ t ∧
      GlobalRicciEigenvalueFloor3 (gt t) (1 / 4) ∧
      GlobalPositiveRicci3 (gt t) ∧
      GlobalPinchingQuotientBound3 (gt t) (3 / 8) := by
  have hLipschitz : UniformClosedRiemannianLipschitzBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) (2 * A * B) :=
    uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      gt hCOne hBounds
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower gt :=
    compactControl.uniformBallVolumeLower_of_realizes
      parameter gt hRealize
  exact
    exists_finite_normalizedFlow_time_global_one_fourth_ricci_pinched_of_finiteAbsoluteDissipation
      gt hrho hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hLipschitz
      hNoncollapse hScalarLower

end FinitePinchedSlice

end Poincare
