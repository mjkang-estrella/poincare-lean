import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient
import Poincare.Global.EinsteinNormalization

/-!
# Unit-curvature and sphere endpoints from full covariant-Ricci control

This file appends only Einstein normalization and the existing unit-curvature
sphere-recognition boundary to the strongest mean-scalar analytic endpoint.
No scalar-gradient, centered-scalar, scalar-variance Lipschitz, invariant-pair
continuity, uniform traceless-Ricci norm bound, forward scalar positivity, or
pinching-quotient regularity premise is reintroduced.  The uniform norm bound
is extracted from joint continuity on the compact reference family.
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

section FullCovariantRicciControl

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : ℝ → K)
variable (hRealize : ∀ t, metric (parameter t) = gt t)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {D c : ℝ}
variable [∀ t : ℝ,
  CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : ℝ, ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t x)
variable (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
  MetricEntriesJointContDiffAt gt t x 3)
variable (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
  HasDerivAt (fun s ↦ totalScalar (gt s))
    (normalizedMeanScalarEnergyNumerator (gt t)) t)
variable (hDifferentiateMovingVolume : ∀ t : ℝ,
  HasDerivAt (fun s ↦ totalVolume (gt s))
    (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
variable (hFiniteDissipation :
  IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
variable (hFullCovariantRicci :
  UniformCovariantRicciDerivativeNormBound gt D)
variable (hMeanLower : ∀ t : ℝ, 0 ≤ t → c ≤ meanScalar (gt t))
variable (hJointScalar : Continuous ↿(fun k (x : M) ↦
  (metric k).scalarAt x))
variable (hJointTraceless : Continuous ↿(fun k (x : M) ↦
  (metric k).tracelessRicciNormSqAt x))

include gt metric parameter hRealize compactControl hc hFlow
  hJointMetricEntries hDifferentiateMovingTotalScalar
  hDifferentiateMovingVolume hFiniteDissipation
  hFullCovariantRicci hMeanLower hJointScalar hJointTraceless

/-- The strongest full-covariant-Ricci mean-scalar endpoint normalizes its
positive Einstein metric to sectional curvature exactly `1`. -/
theorem exists_unitConstantCurvature_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation
      hFullCovariantRicci hMeanLower hJointScalar hJointTraceless

/-- With the repository's explicit unit-curvature recognition boundary, the
same full-covariant-Ricci route yields a homeomorphism to the unit `3`-sphere. -/
theorem sphereConclusion_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation
      hFullCovariantRicci hMeanLower hJointScalar hJointTraceless

end FullCovariantRicciControl

end Poincare
