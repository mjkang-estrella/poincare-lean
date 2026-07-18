import Poincare.Global.NormalizedFlowFiniteDissipationCoerciveGap

/-!
# Compact fixed-target positive Einstein data from a coercive energy gap

The older compact finite-time package asks directly for integrability of the
absolute mean-scalar dissipation on `Ici 0`.  This file replaces that analytic
input by geometric compact-orbit data from which the integrability theorem is
proved:

* the forward parameter in the compact metric family is continuous;
* the corresponding finite Riemannian volume measures vary continuously; and
* scalar variance is bounded by `kappa` times traceless-Ricci energy for one
  coefficient `0 <= kappa < 6`.

The conversion to
`NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3` uses
`ofCoerciveGapOfCompactContinuity`.  In particular, the resulting
`finiteAbsoluteDissipation` field is constructed rather than assumed.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Compact normalized-flow data in which finite absolute dissipation is
replaced by a strict scalar-variance/traceless-energy gap and the continuity
needed to make the scalar-variance track measurable.

The remaining fields are exactly the geometric hypotheses consumed by the
compact finite-time positive-Einstein endpoint. -/
structure NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3
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
  kappa : ℝ
  kappa_nonneg : 0 ≤ kappa
  kappa_lt_six : kappa < 6
  scalarVarianceEnergyGap : ∀ t : Ici (0 : ℝ),
    normalizedFlowScalarVarianceTrack gt t.1 ≤
      kappa * normalizedFlowTracelessRicciEnergyTrack gt t.1
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

/-- Fixed-target form of the coercive-gap package.  Smooth instances are
requested only after a downstream smoothing theorem chooses an atlas on the
target topological manifold. -/
def FixedTargetNormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Construct the existing finite-time endpoint package.  Its absolute
dissipation proof is supplied by the compact-continuity coercive-gap theorem,
not by a field of `data`. -/
noncomputable def toFiniteTimePositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.ofCoerciveGapOfCompactContinuity
      data.gt data.metric data.parameter data.parameterContinuous
      data.realizesFlow data.compactTensorReferenceControl
      data.fullCovariantRicciDerivativeBound data.meanScalarFloor
      data.covariantDerivativeRegularity data.meanScalarFloor_pos
      data.normalizedFlow data.jointMetricEntries
      data.differentiateMovingTotalScalar data.differentiateMovingVolume
      data.finiteVolumeMeasureContinuous data.kappa_nonneg
      data.kappa_lt_six data.scalarVarianceEnergyGap
      data.fullCovariantRicciControl data.meanScalarLower
      data.scalarJointContinuous data.tracelessRicciNormSqJointContinuous

/-- Finite absolute mean-scalar dissipation is a theorem of the new compact
geometric package. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation data.gt)
      (Ici 0) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- The coercive-gap package constructs a positive Einstein metric. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The resulting positive Einstein metric admits a unit-curvature
normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature sphere recognition turns the constructed Einstein metric
into the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactCoerciveGapPositiveEinsteinAnalyticData3

end Poincare
