import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.EinsteinNormalization

/-!
# Unit-curvature and sphere endpoints for the mean-scalar route

This file extends the direct-sample positive-Einstein theorem by only the two
final geometric steps:

1. constant rescaling of a positive Einstein metric to sectional curvature
   exactly `1`; and
2. the explicit `UnitConstantCurvatureSphereRecognition3` boundary.

The analytic signature is unchanged.  In particular, these endpoints assume
neither Hamilton evolution/antitonicity, a global constant pointwise scalar
floor, nor a bounded normalization primitive.
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

section RawConcentration

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : ℝ → K)
variable (hRealize : ∀ t, metric (parameter t) = gt t)
variable {LScalar LTraceless c : ℝ}
variable [∀ t : ℝ,
  CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : ℝ, ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t x)
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
variable (hTracelessLipschitz : UniformClosedRiemannianLipschitzBound gt
  (fun t x ↦ (gt t).tracelessRicciNormSqAt x) LTraceless)
variable (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt)
variable (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
variable (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
  0 < (gt t).scalarAt x)
variable (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
  ContMDiffAt I 𝓘(ℝ) 2
    (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
variable (hInvariantContinuous :
  Continuous (fun k ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)))

include gt metric parameter hRealize hc hFlow
  hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
  hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
  hUniformNoncollapse hMeanLower hForwardScalarPos hTQTwo
  hInvariantContinuous

/-- The direct-sample mean-scalar endpoint constructs a metric of sectional
curvature exactly `1` by normalizing its positive Einstein metric. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization_of_relativePinchingMaximum
      gt metric parameter hRealize hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse hMeanLower hForwardScalarPos hTQTwo
      hInvariantContinuous

/-- With the explicit unit-curvature recognition premise, the same analytic
route yields the statement-layer homeomorphism to the unit `3`-sphere. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceConcentration_of_meanLower_of_compact_parameterization_of_relativePinchingMaximum
      gt metric parameter hRealize hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hTracelessLipschitz
      hUniformNoncollapse hMeanLower hForwardScalarPos hTQTwo
      hInvariantContinuous

end RawConcentration

section CompactTensorControl

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : ℝ → K)
variable (hRealize : ∀ t, metric (parameter t) = gt t)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {A B LScalar c : ℝ}
variable [∀ t : ℝ,
  CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : ℝ, ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t x)
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
variable (hForwardScalarPos : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
  0 < (gt t).scalarAt x)
variable (hTQTwo : ∀ t : ℝ, 0 ≤ t → ∀ x : M,
  ContMDiffAt I 𝓘(ℝ) 2
    (fun y : M ↦ (gt t).tracelessPinchingAt y 0) x)
variable (hInvariantContinuous :
  Continuous (fun k ↦
    closedMetricScalarMinimumRelativePinchingMaximumPair (metric k)))

include gt metric parameter hRealize compactControl hc hFlow
  hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
  hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
  hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- Tensor compact-reference control supplies the traceless concentration and
noncollapse inputs before Einstein normalization. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

/-- Tensor-control sphere endpoint with the final recognition boundary kept
explicit. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_scalarVarianceLipschitz_of_covariantDerivativeBound_of_meanLower_of_compactTensorReferenceFamily
      gt metric parameter hRealize compactControl hc hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hScalarVarianceLipschitz hCOne hBounds
      hMeanLower hForwardScalarPos hTQTwo hInvariantContinuous

end CompactTensorControl

end Poincare
