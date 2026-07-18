import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient
import Poincare.Global.NormalizedFlowForwardFiniteDissipationReduction

/-!
# Forward positive-Einstein endpoint from finite traceless-Ricci energy

This module replaces the opaque finite absolute-dissipation premise in the
strongest geometric forward mean-scalar endpoint by three direct forward-ray
hypotheses:

* the mean-scalar derivative is nonnegative;
* the mean scalar has a finite uniform upper bound; and
* total squared traceless-Ricci curvature is time-integrable.

The forward finite-dissipation reduction converts those hypotheses into the
absolute-dissipation integrability consumed by the existing endpoint.  Every
time-indexed premise is carried by `Ici 0`; no negative-time flow equation,
regularity instance, derivative identity, sign, or bound is assumed.
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

/-- Strongest geometric forward endpoint with finite time-integrated total
traceless-Ricci energy as its dissipation input.

Nonnegative mean-scalar derivative and the forward mean upper bound make its
absolute derivative integrable.  The exact three-dimensional normalized-flow
identity and constant forward volume then turn finite traceless-Ricci energy
into finite scalar variance, hence finite absolute dissipation. -/
theorem positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ),
      metric (parameter t) = gt t.1)
    (compactControl : CompactReferenceMetricTensorFamilyData K metric)
    {D c C : ℝ}
    [∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (gt t.1).leviCivita 1]
    (hc : 0 < c)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t.1 x 3)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hMeanScalarDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
    (hMeanUpper : ∀ t : Ici (0 : ℝ),
      meanScalar (gt t.1) ≤ C)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hFullCovariantRicci :
      UniformCovariantRicciDerivativeNormBound
        (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
    (hMeanLower : ∀ t : Ici (0 : ℝ),
      c ≤ meanScalar (gt t.1))
    (hJointScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hJointTraceless : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    PositiveEinsteinMetric3 M := by
  have hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
        (Ici 0) :=
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
      gt hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hMeanScalarDerivativeNonneg
      hMeanUpper hFiniteTracelessRicciEnergy
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hFiniteDissipation hFullCovariantRicci
      hMeanLower hJointScalar hJointTraceless

section Consequences

variable [Nonempty M] [SimplyConnectedSpace M]
variable {K : Type v} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
variable (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
variable (metric : K → ClosedSmoothRiemannianMetric 3 M)
variable (parameter : Ici (0 : ℝ) → K)
variable (hRealize : ∀ t : Ici (0 : ℝ),
  metric (parameter t) = gt t.1)
variable (compactControl : CompactReferenceMetricTensorFamilyData K metric)
variable {D c C : ℝ}
variable [∀ t : Ici (0 : ℝ),
  CovariantDerivative.ContMDiffCovariantDerivative
    (gt t.1).leviCivita 1]
variable (hc : 0 < c)
variable (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
  IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
variable (hJointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
  MetricEntriesJointContDiffAt gt t.1 x 3)
variable (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalScalar (gt s))
    (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
variable (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
  HasDerivAt (fun s ↦ totalVolume (gt s))
    (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
variable (hMeanScalarDerivativeNonneg : ∀ t : Ici (0 : ℝ),
  0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1)
variable (hMeanUpper : ∀ t : Ici (0 : ℝ),
  meanScalar (gt t.1) ≤ C)
variable (hFiniteTracelessRicciEnergy :
  IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
variable (hFullCovariantRicci :
  UniformCovariantRicciDerivativeNormBound
    (fun t : Ici (0 : ℝ) ↦ gt t.1) D)
variable (hMeanLower : ∀ t : Ici (0 : ℝ),
  c ≤ meanScalar (gt t.1))
variable (hJointScalar : Continuous ↿(fun k (x : M) ↦
  (metric k).scalarAt x))
variable (hJointTraceless : Continuous ↿(fun k (x : M) ↦
  (metric k).tracelessRicciNormSqAt x))

include gt metric parameter hRealize compactControl hc hFlow
  hJointMetricEntries hDifferentiateMovingTotalScalar
  hDifferentiateMovingVolume hMeanScalarDerivativeNonneg hMeanUpper
  hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
  hJointScalar hJointTraceless

/-- The finite-traceless-energy forward endpoint produces a metric of
sectional curvature exactly `1`. -/
theorem exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hMeanScalarDerivativeNonneg hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

/-- With the explicit unit-curvature recognition boundary, the same
finite-traceless-energy route yields the unit `3`-sphere conclusion. -/
theorem sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hMeanScalarDerivativeNonneg hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

end Consequences

end Poincare
