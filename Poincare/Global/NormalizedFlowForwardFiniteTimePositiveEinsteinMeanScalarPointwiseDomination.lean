import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination

/-!
# Forward positive-Einstein endpoint from pointwise density domination

The integrated condition used by the energy-domination endpoint is

`scalar variance ≤ 6 * traceless-Ricci energy`.

This module derives it from the stronger but fully geometric slice-wise
pointwise inequality

`(R - meanScalar) ^ 2 ≤ 6 * |Ric°| ^ 2`.

Both densities are automatically integrable on every compact smooth slice.
Consequently, ordinary monotonicity of the Riemannian integral proves the
track inequality without a separate measurability or slice-integrability
premise.  The result then discharges the energy-domination hypothesis in the
positive-Einstein, unit-curvature, and sphere endpoints.

Every time-indexed hypothesis is carried by `Ici 0`; no negative-time datum
is introduced.
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

omit [SecondCountableTopology M] in
/-- A pointwise comparison of the centered-scalar and traceless-Ricci
densities on every forward slice implies the corresponding integrated track
inequality.

Compact smoothness supplies integrability of both densities.  Thus the proof
is exactly integral monotonicity followed by pulling the constant `6` through
the integral. -/
theorem normalizedFlowScalarVarianceTrack_le_six_tracelessRicciEnergyTrack_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hPointwise : ∀ t : Ici (0 : ℝ), ∀ x : M,
      ((gt t.1).scalarAt x - meanScalar (gt t.1)) ^ 2 ≤
        6 * (gt t.1).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1 := by
  intro t
  unfold normalizedFlowScalarVarianceTrack
    normalizedFlowTracelessRicciEnergyTrack
  calc
    (∫ x, ((gt t.1).scalarAt x - meanScalar (gt t.1)) ^ 2
        ∂(volumeMeasure (gt t.1))) ≤
        ∫ x, 6 * (gt t.1).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t.1)) := by
      exact integral_mono
        (centeredScalarSq_integrable (gt t.1))
        ((tracelessRicciNormSqAt_integrable (gt t.1)).const_mul 6)
        (hPointwise t)
    _ = 6 *
        ∫ x, (gt t.1).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt t.1)) := by
      rw [integral_const_mul]

/-- Strongest geometric finite-energy endpoint with integrated energy
domination generated from the pointwise slice inequality
`(R - meanScalar) ^ 2 ≤ 6 * |Ric°| ^ 2`. -/
theorem positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
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
    (hPointwise : ∀ t : Ici (0 : ℝ), ∀ x : M,
      ((gt t.1).scalarAt x - meanScalar (gt t.1)) ^ 2 ≤
        6 * (gt t.1).tracelessRicciNormSqAt x)
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
  have hEnergyDomination : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1 :=
    normalizedFlowScalarVarianceTrack_le_six_tracelessRicciEnergyTrack_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq
      gt hPointwise
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hEnergyDomination hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

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
variable (hPointwise : ∀ t : Ici (0 : ℝ), ∀ x : M,
  ((gt t.1).scalarAt x - meanScalar (gt t.1)) ^ 2 ≤
    6 * (gt t.1).tracelessRicciNormSqAt x)
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
  hDifferentiateMovingVolume hPointwise hMeanUpper
  hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
  hJointScalar hJointTraceless

/-- Pointwise density domination and finite traceless-Ricci energy produce a
metric of sectional curvature exactly `1`. -/
theorem exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hPointwise hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

/-- With the explicit unit-curvature recognition boundary, pointwise density
domination and finite traceless-Ricci energy yield the unit `3`-sphere
conclusion. -/
theorem sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hPointwise hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

end Consequences

end Poincare
