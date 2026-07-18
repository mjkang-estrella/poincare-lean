import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity

/-!
# Mean-scalar Einstein endpoint from joint compact-family continuity

This file removes the opaque continuity premise for the scalar-minimum /
relative-pinching-maximum pair from the strongest tensor-reference-family
mean-scalar endpoint.  The primary theorem assumes joint continuity of scalar
curvature and exponent-zero pinching on `K × M`.  A second theorem replaces
joint pinching continuity by joint squared-traceless-Ricci continuity and an
explicit positive scalar floor on the whole ambient compact family.

Positivity on the full compact family is not inferred from realization of the
flow: the parameter map need not be surjective onto `K`.
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

/-- Joint scalar and exponent-zero pinching continuity on the compact
reference family discharge the invariant-pair continuity premise in the
mean-scalar positive-Einstein endpoint. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching
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
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0)) :
    PositiveEinsteinMetric3 M := by
  have hInvariantContinuous :
      Continuous (fun k ↦
        closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)) :=
    continuous_closedMetricScalarMinimumRelativePinchingMaximumPair_comp_of_joint
      metric hJointScalar hJointPinching
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- Joint scalar and squared-traceless-Ricci continuity imply the same
endpoint when scalar curvature is positive on the whole ambient compact
family.  This last premise is explicit because flow realization does not make
the time-parameter map surjective onto `K`. -/
theorem positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_familyScalarPos
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
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTracelessRicci : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x))
    (hFamilyScalarPos : ∀ k : K, ∀ x : M,
      0 < (metric k).scalarAt x) :
    PositiveEinsteinMetric3 M := by
  have hJointPinching : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessPinchingAt x 0) :=
    continuous_joint_tracelessPinchingAt_zero_of_joint_scalarAt_of_joint_tracelessRicciNormSqAt_of_pos
      metric hJointScalar hJointTracelessRicci hFamilyScalarPos
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_pinching
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hJointScalar hJointPinching

end Poincare
