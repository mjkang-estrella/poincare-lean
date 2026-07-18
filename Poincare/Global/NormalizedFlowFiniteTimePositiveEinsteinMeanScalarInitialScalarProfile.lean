import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarSphere
import Poincare.Global.NormalizedFlowScalarLowerProfile

/-!
# Mean-scalar Einstein endpoint from an initial scalar profile

The direct-sample mean-scalar endpoint needs scalar curvature to stay strictly
positive on the forward ray, but it does not need a time-independent positive
pointwise floor there.  This module derives that strict positivity from:

* a positive numerical scalar floor on the initial slice;
* the normalized-flow scalar equation supplied by global Lichnerowicz
  regularity;
* joint scalar continuity; and
* the moving total-scalar and total-volume derivative identities.

The last identities make `meanScalar` continuous.  Its interval integral
then constructs the normalization primitive by FTC, so no primitive witness
or upper bound is assumed.  The resulting lower profile may decay to zero.
It is fed into the strongest tensor-reference-family positive-Einstein
endpoint and its unit-curvature and sphere corollaries.
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

omit [SecondCountableTopology M] in
/-- The all-time moving total-scalar and total-volume derivative identities
make the mean scalar continuous.  Positivity of Riemannian volume supplies
the nonvanishing denominator in the quotient. -/
theorem continuous_meanScalar_of_movingTotalScalarVolume_derivatives
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) :
    Continuous (fun t ↦ meanScalar (gt t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  simpa only [meanScalar, totalVolume] using
    (hDifferentiateMovingTotalScalar t).continuousAt.div
      (hDifferentiateMovingVolume t).continuousAt
      (totalVolume_ne_zero (gt t))

/-- Canonical normalization primitive constructed from the continuous mean
scalar track. -/
noncomputable def normalizedMeanScalarPrimitive
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (2 / 3 : ℝ) * meanScalar (gt s)

omit [SecondCountableTopology M] in
/-- The interval-integral normalization primitive is continuous whenever the
mean scalar track is continuous. -/
theorem continuous_normalizedMeanScalarPrimitive
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanContinuous : Continuous (fun t ↦ meanScalar (gt t))) :
    Continuous (normalizedMeanScalarPrimitive gt) := by
  let f : ℝ → ℝ := fun t ↦ (2 / 3 : ℝ) * meanScalar (gt t)
  have hf : Continuous f := continuous_const.mul hMeanContinuous
  exact (intervalIntegral.differentiable_integral_of_continuous
    (a := 0) hf).continuous

omit [SecondCountableTopology M] in
/-- FTC derivative of the canonical normalization primitive. -/
theorem hasDerivAt_normalizedMeanScalarPrimitive
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeanContinuous : Continuous (fun t ↦ meanScalar (gt t)))
    (t : ℝ) :
    HasDerivAt (normalizedMeanScalarPrimitive gt)
      ((2 / 3 : ℝ) * meanScalar (gt t)) t := by
  let f : ℝ → ℝ := fun s ↦ (2 / 3 : ℝ) * meanScalar (gt s)
  have hf : Continuous f := continuous_const.mul hMeanContinuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/-- A positive initial scalar floor and the unbounded normalization profile
imply strict scalar positivity on the whole forward ray.

Both the scalar evolution equation and its spatial `C²` regularity are
derived from the normalized metric flow and global Lichnerowicz assembly.
The exponential factor is positive for every finite time, regardless of
whether the normalization primitive is bounded above. -/
theorem normalizedFlow_forwardScalarPos_of_initialScalarFloor_of_globalLichnerowicz_of_normalizationPrimitive
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun t (x : M) ↦ (gt t).scalarAt x))
    (normalizationPrimitive : ℝ → ℝ)
    (hPrimitiveContinuous : Continuous normalizationPrimitive)
    (hPrimitiveDerivative : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt normalizationPrimitive
        ((2 / 3 : ℝ) * meanScalar (gt t)) t)
    (hInitialScalarFloor : ∀ x : M, rho ≤ (gt 0).scalarAt x) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M, 0 < (gt t).scalarAt x := by
  have hProfile : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      (rho / 2) * Real.exp
          (-(normalizationPrimitive t - normalizationPrimitive 0)) <
        (gt ((0 : ℝ) + t)).scalarAt x := by
    apply normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
      (gt := gt) (t0 := 0) (rho := rho) hrho
    · simpa only [zero_add] using hScalarContinuous
    · intro t _ht x
      exact
        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
          (hFlow ((0 : ℝ) + t)) hLichnerowicz
    · intro t _ht x
      exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
        (hFlow ((0 : ℝ) + t))
        (hLichnerowicz.timeVariationEntries ((0 : ℝ) + t)) x
    · exact hPrimitiveContinuous
    · intro t ht
      simpa only [zero_add] using hPrimitiveDerivative t ht
    · exact hInitialScalarFloor
  intro t ht x
  have hLowerPos :
      0 < (rho / 2) * Real.exp
          (-(normalizationPrimitive t - normalizationPrimitive 0)) :=
    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _)
  exact hLowerPos.trans (by simpa only [zero_add] using hProfile t ht x)

/-- Primitive-free forward scalar positivity.  The moving total-scalar and
total-volume derivative identities construct the normalization primitive by
interval integration, so no primitive witness remains in the interface. -/
theorem normalizedFlow_forwardScalarPos_of_initialScalarFloor_of_globalLichnerowicz_of_movingTotalScalarVolume
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {rho : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hrho : 0 < rho)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalarContinuous :
      Continuous ↿(fun t (x : M) ↦ (gt t).scalarAt x))
    (hInitialScalarFloor : ∀ x : M, rho ≤ (gt 0).scalarAt x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : M, 0 < (gt t).scalarAt x := by
  have hMeanContinuous : Continuous (fun t ↦ meanScalar (gt t)) :=
    continuous_meanScalar_of_movingTotalScalarVolume_derivatives
      gt hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
  exact
    normalizedFlow_forwardScalarPos_of_initialScalarFloor_of_globalLichnerowicz_of_normalizationPrimitive
      gt hrho hFlow hLichnerowicz hScalarContinuous
      (normalizedMeanScalarPrimitive gt)
      (continuous_normalizedMeanScalarPrimitive gt hMeanContinuous)
      (fun t _ht ↦
        hasDerivAt_normalizedMeanScalarPrimitive gt hMeanContinuous t)
      hInitialScalarFloor

section CompactTensorControl

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : ℝ → K)
variable (hRealize : ∀ t, metric (parameter t) = gt t)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {A B LScalar c rho : ℝ}
variable [∀ t : ℝ,
  CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
variable (hc : 0 < c)
variable (hrho : 0 < rho)
variable (hFlow : ∀ t : ℝ, ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t x)
variable (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
variable (hScalarContinuous :
  Continuous ↿(fun t (x : M) ↦ (gt t).scalarAt x))
variable (hInitialScalarFloor : ∀ x : M,
  rho ≤ (gt 0).scalarAt x)
variable (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
  HasDerivAt (fun s ↦ totalScalar (gt s))
    (normalizedMeanScalarEnergyNumerator (gt t)) t)
variable (hDifferentiateMovingVolume : ∀ t : ℝ,
  HasDerivAt (fun s ↦ totalVolume (gt s))
    (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
variable (hFiniteDissipation :
  IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
variable (hScalarVarianceLipschitz : UniformClosedRiemannianLipschitzBound gt
  (fun t x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2) LScalar)
variable (hCOne : UniformTracelessRicciEnergyCOne gt)
variable (hBounds :
  UniformTracelessRicciAndCovariantDerivativeNormBound gt A B)
variable (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
variable (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
  ContMDiffAt I 𝓘(ℝ) 2
    (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
variable (hInvariantContinuous :
  Continuous (fun k ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)))

include gt metric parameter hRealize compactControl hc hrho hFlow
  hLichnerowicz hScalarContinuous hInitialScalarFloor
  hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
  hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds hMeanLower
  hTQTwo hInvariantContinuous

/-- Strongest tensor-reference-family positive-Einstein endpoint with
all-forward scalar positivity derived from a possibly decaying initial-data
profile whose normalization primitive is constructed internally. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_initialScalarProfile :
    PositiveEinsteinMetric3 M := by
  have hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
      0 < (gt t).scalarAt x :=
    normalizedFlow_forwardScalarPos_of_initialScalarFloor_of_globalLichnerowicz_of_movingTotalScalarVolume
      gt hrho hFlow hLichnerowicz hScalarContinuous
      hInitialScalarFloor hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- The same initial-profile route constructs a metric of sectional curvature
exactly `1`; no uniform forward scalar floor is introduced. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_initialScalarProfile :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_initialScalarProfile
      gt metric parameter hRealize compactControl hc hrho hFlow
      hLichnerowicz hScalarContinuous hInitialScalarFloor
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds hMeanLower
      hTQTwo hInvariantContinuous

/-- With explicit unit-curvature recognition, the initial-profile route
reaches the round-sphere conclusion without bounded normalization data. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_initialScalarProfile
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_initialScalarProfile
      gt metric parameter hRealize compactControl hc hrho hFlow
      hLichnerowicz hScalarContinuous hInitialScalarFloor
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds hMeanLower
      hTQTwo hInvariantContinuous

end CompactTensorControl

end Poincare
