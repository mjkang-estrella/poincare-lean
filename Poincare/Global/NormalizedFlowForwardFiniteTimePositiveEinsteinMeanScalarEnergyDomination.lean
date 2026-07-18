import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergy

/-!
# Forward positive-Einstein endpoint from scalar-variance energy domination

In dimension three, the exact normalized mean-scalar derivative is

`(2 * E - (1 / 3) * V) / volume`,

where `E` is total squared traceless-Ricci curvature and `V` is scalar
variance.  Thus the pointwise-in-time integrated inequality `V ≤ 6 * E`
makes the derivative nonnegative.  This module records that subtype-indexed
calculation and uses it to discharge the derivative-sign premise of the
finite-traceless-energy forward endpoint.

Every time-indexed hypothesis is carried by `Ici 0`; no negative-time flow,
regularity, differentiation, energy, or scalar hypothesis is introduced.
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
/-- The integrated inequality `scalar variance ≤ 6 * traceless-Ricci
energy` makes the forward mean-scalar derivative nonnegative.

The factor `6` is exact: after multiplying the inequality by `1 / 3`, it
states that the numerator `2 * E - (1 / 3) * V` in the three-dimensional
normalized-flow derivative identity is nonnegative. -/
theorem meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hEnergyDomination : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1 := by
  intro t
  have hDerivative :=
    (hasDerivAt_meanScalar_three_of_normalizedFlow
      (hFlow t) (hDifferentiateMovingTotalScalar t)
        (hDifferentiateMovingVolume t)).deriv
  have hNumerator :
      0 ≤ 2 * normalizedFlowTracelessRicciEnergyTrack gt t.1 -
        (1 / 3 : ℝ) * normalizedFlowScalarVarianceTrack gt t.1 := by
    linarith [hEnergyDomination t]
  rw [hDerivative]
  apply div_nonneg
  · simpa only [normalizedFlowTracelessRicciEnergyTrack,
      normalizedFlowScalarVarianceTrack] using hNumerator
  · exact (totalVolume_pos (gt t.1)).le

/-- Strongest geometric finite-energy endpoint with the raw derivative-sign
premise replaced by the integrated inequality `V ≤ 6 * E` on every forward
time slice. -/
theorem positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
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
    (hEnergyDomination : ∀ t : Ici (0 : ℝ),
      normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1)
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
  have hMeanScalarDerivativeNonneg : ∀ t : Ici (0 : ℝ),
      0 ≤ deriv (fun s ↦ meanScalar (gt s)) t.1 :=
    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
      gt hFlow hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hEnergyDomination
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_meanScalarDerivativeNonneg_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hMeanScalarDerivativeNonneg hMeanUpper
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
variable (hEnergyDomination : ∀ t : Ici (0 : ℝ),
  normalizedFlowScalarVarianceTrack gt t.1 ≤
    6 * normalizedFlowTracelessRicciEnergyTrack gt t.1)
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
  hDifferentiateMovingVolume hEnergyDomination hMeanUpper
  hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
  hJointScalar hJointTraceless

/-- The scalar-variance energy-domination route produces a metric of
sectional curvature exactly `1`. -/
theorem exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hEnergyDomination hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

/-- With the explicit unit-curvature recognition boundary, scalar-variance
energy domination and finite traceless-Ricci energy yield the unit `3`-sphere
conclusion. -/
theorem sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack_of_meanUpper_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      gt metric parameter hRealize compactControl hc hFlow
      hJointMetricEntries hDifferentiateMovingTotalScalar
      hDifferentiateMovingVolume hEnergyDomination hMeanUpper
      hFiniteTracelessRicciEnergy hFullCovariantRicci hMeanLower
      hJointScalar hJointTraceless

end Consequences

end Poincare
