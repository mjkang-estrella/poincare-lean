import Poincare.Global.NormalizedFlowCompactFixedTargetCoerciveGapPositiveEinstein

/-!
# Compact fixed-target positive Einstein data from an eventual coercive gap

A strict scalar-variance/traceless-Ricci energy gap need not hold on the
entire normalized-flow ray.  The proved eventual coercive-gap theorem only
needs such a gap after one finite nonnegative time, provided the absolute
mean-scalar dissipation is continuous on `Ici 0`.

This file derives that continuity from the compact moving-metric family:
weak continuity of the finite volume measures and joint continuity of scalar
and traceless-Ricci curvature make the variance and energy tracks continuous.
The exact three-dimensional normalized-flow identity then makes the
mean-scalar derivative, and hence the full absolute dissipation, continuous.

The resulting analytic package assumes exactly an eventual gap

`exists T kappa, 0 <= T and 0 <= kappa and kappa < 6 and
  forall t in Ici T, V(t) <= kappa * E(t)`.

Neither continuity nor integrability of the dissipation is stored as input.
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

/-- Compact moving-measure continuity makes the complete absolute
mean-scalar/variance dissipation continuous on the forward ray.

The derivative summand is not treated as an abstract derivative of a
continuous function.  At every forward time it is rewritten using the exact
normalized-flow formula

`mean' = (2 * E - V / 3) / volume`.

The two moving-integral continuity theorems give continuity of `E` and `V`,
while normalized-flow volume preservation replaces the denominator by the
fixed positive number `totalVolume (gt 0)`. -/
theorem continuousOn_normalizedMeanScalarAbsoluteVarianceDissipation_of_compact_parameterization
    [Nonempty M]
    {K : Type v} [TopologicalSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hTracelessRicci : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)) :
    ContinuousOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) := by
  have hVariance : ContinuousOn
      (normalizedFlowScalarVarianceTrack gt) (Ici 0) :=
    continuousOn_normalizedFlowScalarVarianceTrack_of_parameterization
      gt metric parameter hParameter hRealizes hMeasure hScalar
  have hEnergy : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) :=
    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
      gt metric parameter hParameter hRealizes hMeasure hTracelessRicci
  let derivativeModel : ℝ → ℝ := fun t ↦
    (2 * normalizedFlowTracelessRicciEnergyTrack gt t -
      (1 / 3 : ℝ) * normalizedFlowScalarVarianceTrack gt t) /
        totalVolume (gt 0)
  have hDerivativeModel : ContinuousOn derivativeModel (Ici 0) := by
    dsimp only [derivativeModel]
    exact
      ((hEnergy.const_mul 2).sub (hVariance.const_mul (1 / 3))).div_const
        (totalVolume (gt 0))
  have hModel : ContinuousOn
      (fun t ↦ |derivativeModel t| +
        normalizedFlowScalarVarianceTrack gt t) (Ici 0) :=
    hDerivativeModel.abs.add hVariance
  apply hModel.congr
  intro t ht
  have hVolumeConstant :
      totalVolume (gt t) = totalVolume (gt 0) :=
    totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      (s := t) (t := 0)
      (fun r hr ↦ hFlow ⟨r, hr⟩)
      (fun r hr ↦ hDifferentiateMovingVolume ⟨r, hr⟩)
      ht (by norm_num)
  have hDerivative :
      deriv (fun s ↦ meanScalar (gt s)) t = derivativeModel t := by
    have h :=
      (hasDerivAt_meanScalar_three_of_normalizedFlow
        (hFlow ⟨t, ht⟩)
        (hDifferentiateMovingTotalScalar ⟨t, ht⟩)
        (hDifferentiateMovingVolume ⟨t, ht⟩)).deriv
    simpa only [derivativeModel, normalizedFlowTracelessRicciEnergyTrack,
      normalizedFlowScalarVarianceTrack, hVolumeConstant] using h
  rw [normalizedMeanScalarAbsoluteVarianceDissipation, hDerivative]
  rfl

/-- Fully geometric compact-family form of the eventual coercive-gap
integrability theorem.

Compact joint scalar continuity supplies a global finite upper bound for the
mean scalar.  The preceding theorem supplies dissipation continuity.  After
those two independent constructions, the eventual gap is passed to
`normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_eventual_coerciveGap`.
-/
theorem normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_continuity_eventualCoerciveGap
    [Nonempty M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t.1 x)
    (hDifferentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1)
    (hDifferentiateMovingVolume : ∀ t : Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous ↿(fun k (x : M) ↦
      (metric k).scalarAt x))
    (hTracelessRicci : Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x))
    (hEventualCoerciveGap :
      ∃ T kappa : ℝ, 0 ≤ T ∧ 0 ≤ kappa ∧ kappa < 6 ∧
        ∀ t : Ici T,
          normalizedFlowScalarVarianceTrack gt t.1 ≤
            kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0) := by
  letI : Nonempty K := ⟨parameter ⟨0, by simp⟩⟩
  obtain ⟨C, _hC, hMeanUpper⟩ :=
    exists_pos_meanScalarUpper_of_compact_parameterization_of_joint_scalar
      gt metric parameter hRealizes hScalar
  have hDissipationContinuous : ContinuousOn
      (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) :=
    continuousOn_normalizedMeanScalarAbsoluteVarianceDissipation_of_compact_parameterization
      gt metric parameter hParameter hRealizes hFlow
      hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hMeasure hScalar hTracelessRicci
  obtain ⟨T, kappa, hT, hkappa_nonneg, hkappa_lt, hGap⟩ :=
    hEventualCoerciveGap
  exact
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_eventual_coerciveGap
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hT hDissipationContinuous hMeanUpper hkappa_nonneg hkappa_lt hGap

/-- Compact normalized-flow data in which finite absolute dissipation is
replaced by compact moving-measure continuity and one eventual strict
scalar-variance/traceless-energy gap. -/
structure
    NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  compactTensorReferenceControl :
    letI : TopologicalSpace K := topologicalSpaceK
    CompactReferenceMetricTensorFamilyData K metric
  fullCovariantRicciDerivativeBound : ℝ
  meanScalarFloor : ℝ
  covariantDerivativeRegularity : ∀ t : Ici (0 : ℝ),
    CovariantDerivative.ContMDiffCovariantDerivative
      (gt t.1).leviCivita 1
  meanScalarFloor_pos : 0 < meanScalarFloor
  normalizedFlow : ∀ t : Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t.1 x
  jointMetricEntries : ∀ t : Ici (0 : ℝ), ∀ x : M,
    MetricEntriesJointContDiffAt gt t.1 x 3
  differentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t.1)) t.1
  differentiateMovingVolume : ∀ t : Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t.1) (timeDerivAt gt t.1)) t.1
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)
  eventualCoerciveGap :
    ∃ T kappa : ℝ, 0 ≤ T ∧ 0 ≤ kappa ∧ kappa < 6 ∧
      ∀ t : Ici T,
        normalizedFlowScalarVarianceTrack gt t.1 ≤
          kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1
  fullCovariantRicciControl :
    UniformCovariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1)
        fullCovariantRicciDerivativeBound
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)

/-- Fixed-target form of the eventual coercive-gap package.  Smooth
instances are requested only after a downstream smoothing theorem chooses an
atlas on the target topological manifold. -/
def FixedTargetNormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3

variable [SimplyConnectedSpace M]

/-- A global strict coercive gap is the special eventual gap with tail start
`T = 0`.  This constructor preserves all compact geometric data and changes
only the presentation of the gap hypothesis. -/
noncomputable def ofGlobalCoerciveGap
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
      M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact {
    K := data.K
    topologicalSpaceK := data.topologicalSpaceK
    compactSpaceK := data.compactSpaceK
    gt := data.gt
    metric := data.metric
    parameter := data.parameter
    parameterContinuous := data.parameterContinuous
    realizesFlow := data.realizesFlow
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound :=
      data.fullCovariantRicciDerivativeBound
    meanScalarFloor := data.meanScalarFloor
    covariantDerivativeRegularity := data.covariantDerivativeRegularity
    meanScalarFloor_pos := data.meanScalarFloor_pos
    normalizedFlow := data.normalizedFlow
    jointMetricEntries := data.jointMetricEntries
    differentiateMovingTotalScalar := data.differentiateMovingTotalScalar
    differentiateMovingVolume := data.differentiateMovingVolume
    finiteVolumeMeasureContinuous := data.finiteVolumeMeasureContinuous
    scalarJointContinuous := data.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.tracelessRicciNormSqJointContinuous
    eventualCoerciveGap :=
      ⟨0, data.kappa, le_rfl, data.kappa_nonneg, data.kappa_lt_six, by
        simpa using data.scalarVarianceEnergyGap⟩
    fullCovariantRicciControl := data.fullCovariantRicciControl
    meanScalarLower := data.meanScalarLower }

/-- Construct the existing finite-time endpoint package.  Its absolute
dissipation field is proved from compact continuity and the eventual gap. -/
noncomputable def toFiniteTimePositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact {
    K := data.K
    topologicalSpaceK := data.topologicalSpaceK
    compactSpaceK := data.compactSpaceK
    gt := data.gt
    metric := data.metric
    parameter := data.parameter
    realizesFlow := data.realizesFlow
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound :=
      data.fullCovariantRicciDerivativeBound
    meanScalarFloor := data.meanScalarFloor
    covariantDerivativeRegularity := data.covariantDerivativeRegularity
    meanScalarFloor_pos := data.meanScalarFloor_pos
    normalizedFlow := data.normalizedFlow
    jointMetricEntries := data.jointMetricEntries
    differentiateMovingTotalScalar := data.differentiateMovingTotalScalar
    differentiateMovingVolume := data.differentiateMovingVolume
    finiteAbsoluteDissipation :=
      normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_continuity_eventualCoerciveGap
        data.gt data.metric data.parameter data.parameterContinuous
        data.realizesFlow data.normalizedFlow
        data.differentiateMovingTotalScalar data.differentiateMovingVolume
        data.finiteVolumeMeasureContinuous data.scalarJointContinuous
        data.tracelessRicciNormSqJointContinuous data.eventualCoerciveGap
    fullCovariantRicciControl := data.fullCovariantRicciControl
    meanScalarLower := data.meanScalarLower
    scalarJointContinuous := data.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.tracelessRicciNormSqJointContinuous }

/-- Finite absolute mean-scalar dissipation is a theorem of the eventual-gap
compact geometric package. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation data.gt)
      (Ici 0) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- The eventual coercive-gap package constructs a positive Einstein
metric. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The resulting positive Einstein metric admits a unit-curvature
normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature sphere recognition turns the constructed Einstein metric
into the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactEventualCoerciveGapPositiveEinsteinAnalyticData3

end Poincare
