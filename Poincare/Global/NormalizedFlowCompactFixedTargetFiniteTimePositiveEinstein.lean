import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient

/-!
# Compact fixed-target finite-time positive-Einstein package

This file isolates the strongest geometric forward-ray consumer in
`NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient` as a
fixed-target analytic package.  The record contains only hypotheses.  In
particular, it stores neither a `PositiveEinsteinMetric3` witness nor a
unit-curvature sphere-recognition theorem.

Compared with the quantitative near-round-tail package, this route does not
assume a tail start, a `3 / 10` Ricci-eigenvalue floor, pointwise scalar
positivity on that tail, a `3 / 2` scalar-to-mean estimate, continuity of the
flow parameter, or continuity of the moving finite-volume measure.  It uses
instead compact tensor-reference control, finite absolute mean-scalar
dissipation, a full covariant-Ricci derivative bound, and the two moving
total-scalar/volume derivative identities.  Thus the packages are honest
alternative boundaries rather than one being claimed to imply the other.

All time-dependent assumptions here are indexed by `Ici 0`.  No regularity,
flow equation, or compact realization is requested at negative time.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- The exact compact geometric inputs of the forward finite-time
positive-Einstein theorem.

The parameter itself supplies `Nonempty K`, so nonemptiness is not duplicated
as a field.  Joint continuity on the compact reference family supplies the
zeroth-order scalar and traceless-Ricci bounds used by the endpoint, while
joint `C³` metric-entry regularity and full covariant-Ricci control supply the
spatial concentration estimates. -/
structure NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3
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
  finiteAbsoluteDissipation :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (Ici 0)
  fullCovariantRicciControl :
    UniformCovariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1)
        fullCovariantRicciDerivativeBound
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦ (metric k).scalarAt x)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous ↿(fun k (x : M) ↦
      (metric k).tracelessRicciNormSqAt x)

/-- Fixed-target form of the compact finite-time package.  Its smooth
instances are requested only after a downstream smoothing construction has
selected an atlas on the target topological manifold. -/
def FixedTargetNormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The compact hypothesis package constructs a positive Einstein metric; it
does not carry that metric as input data. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  letI : Nonempty data.K :=
    ⟨data.parameter ⟨0, by simp⟩⟩
  letI : ∀ t : Ici (0 : ℝ),
      CovariantDerivative.ContMDiffCovariantDerivative
        (data.gt t.1).leviCivita 1 :=
    data.covariantDerivativeRegularity
  exact
    positiveEinsteinMetric3_of_finiteAbsoluteDissipation_Ici_of_fullCovariantRicciDerivativeBound_of_meanLower_of_compactTensorReferenceFamily_of_joint_scalar_tracelessRicci_of_jointMetricEntriesThree
      data.gt data.metric data.parameter data.realizesFlow
      data.compactTensorReferenceControl data.meanScalarFloor_pos
      data.normalizedFlow data.jointMetricEntries
      data.differentiateMovingTotalScalar data.differentiateMovingVolume
      data.finiteAbsoluteDissipation data.fullCovariantRicciControl
      data.meanScalarLower data.scalarJointContinuous
      data.tracelessRicciNormSqJointContinuous

/-- The derived positive Einstein metric can be normalized to sectional
curvature exactly `1`, still without adding any recognition input. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact data.positiveEinsteinMetric3

/-- Unit-curvature recognition is supplied only at the final theorem call.
It is not a field of the compact analytic package. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _
    unitRecognition
  exact data.positiveEinsteinMetric3

end NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3

end Poincare
