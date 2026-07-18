import Poincare.Global.NormalizedFlowCompactFiniteDissipationBoundedVariation
import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTimePositiveEinstein

/-!
# Compact fixed-target positive Einstein data from finite traceless energy

This package replaces the finite absolute mean-scalar/variance dissipation
field of the compact finite-time positive-Einstein endpoint by the weaker
analytic input

`IntegrableOn normalizedFlowTracelessRicciEnergyTrack (Ici 0)`.

Compact moving-measure continuity makes the traceless-energy and
scalar-variance tracks continuous.  The exact normalized-flow identity,
constant positive volume, and the stored uniform lower bound for mean scalar
then give finite scalar variance and finite absolute mean-scalar variation.
Thus the finite-dissipation field consumed downstream is proved rather than
assumed.  No sign condition on the mean-scalar derivative and no pointwise
variance/energy gap occurs in this package.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Compact normalized-flow data in which finite absolute dissipation is
replaced by finite total forward traceless-Ricci energy.

Apart from that replacement, the fields agree with the compact eventual-gap
positive-Einstein package. -/
structure
    NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3
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
  finiteTracelessRicciEnergy :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)
  fullCovariantRicciControl :
    UniformCovariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ gt t.1)
        fullCovariantRicciDerivativeBound
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)

/-- Fixed-target form of the finite-traceless-energy package.  Smooth
instances are requested only after a downstream smoothing theorem chooses an
atlas on the target topological manifold. -/
def FixedTargetNormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Construct the existing compact finite-time positive-Einstein package.
Its finite absolute-dissipation field is derived from compact continuity,
finite traceless energy, and the mean-scalar lower bound. -/
noncomputable def toFiniteTimePositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
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
      normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_compact_parameterization_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower
        data.gt data.metric data.parameter data.parameterContinuous
        data.realizesFlow data.normalizedFlow
        data.differentiateMovingTotalScalar data.differentiateMovingVolume
        data.finiteVolumeMeasureContinuous data.scalarJointContinuous
        data.tracelessRicciNormSqJointContinuous
        data.finiteTracelessRicciEnergy data.meanScalarLower
    fullCovariantRicciControl := data.fullCovariantRicciControl
    meanScalarLower := data.meanScalarLower
    scalarJointContinuous := data.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.tracelessRicciNormSqJointContinuous }

/-- Finite absolute mean-scalar/variance dissipation is a theorem of the
finite-traceless-energy package. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation data.gt)
      (Ici 0) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- The finite-traceless-energy package constructs a positive Einstein
metric. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The resulting positive Einstein metric admits a unit-curvature
normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature sphere recognition turns the constructed Einstein metric
into the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3

end Poincare
