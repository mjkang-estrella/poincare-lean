import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein

/-!
# Compact fixed-target positive Einstein data from reaction decay

The compact reaction-decay package proves finite total forward
traceless-Ricci energy, but the stronger finite-time positive-Einstein
endpoint also needs compact metric-tensor reference control, a uniform full
covariant-Ricci derivative bound, and the moving total-scalar identity.

This file adds exactly those three geometric inputs.  Everything else is
reused from the reaction package:

* normalized flow and global joint `C³` metric-entry regularity are restricted
  to `Ici 0`;
* the finite chart-frame density package proves moving-volume
  differentiation;
* reaction domination proves finite traceless-Ricci energy; and
* compact moving-measure continuity and bounded mean-scalar variation turn
  that finite energy into finite absolute dissipation.

Levi-Civita covariant-derivative regularity is already an inferred instance
for every closed smooth metric, so it is not duplicated as an input field.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Reaction-decay data extended by exactly the geometric controls missing
from the compact finite-time positive-Einstein endpoint. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  reaction :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v}
      M
  compactTensorReferenceControl :
    letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
    CompactReferenceMetricTensorFamilyData reaction.K reaction.metric
  fullCovariantRicciDerivativeBound : ℝ
  fullCovariantRicciControl :
    UniformCovariantRicciDerivativeNormBound
      (fun t : Ici (0 : ℝ) ↦ reaction.gt t.1)
        fullCovariantRicciDerivativeBound
  differentiateMovingTotalScalar : ∀ t : Ici (0 : ℝ),
    HasDerivAt (fun s ↦ totalScalar (reaction.gt s))
      (normalizedMeanScalarEnergyNumerator (reaction.gt t.1)) t.1

/-- Fixed-target form of the reaction-decay positive-Einstein package.
Smooth instances are requested only after a downstream smoothing theorem
chooses an atlas on the target topological manifold. -/
def FixedTargetNormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M

/-- Short public name for the fixed-target reaction-decay positive-Einstein
package.  The longer name above records the moving mean-energy/measure route
used to construct it; this alias emphasizes the resulting analytic contract. -/
abbrev FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  FixedTargetNormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
    M

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Convert reaction decay and the three additional geometric controls into
the finite-traceless-energy positive-Einstein package.

Finite energy and moving-volume differentiation are both theorems of the
stored reaction data, not additional fields of this extension. -/
noncomputable def toFiniteTracelessEnergyPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
      M := by
  let reaction := data.reaction
  letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
  letI : CompactSpace reaction.K := reaction.compactSpaceK
  exact {
    K := reaction.K
    topologicalSpaceK := reaction.topologicalSpaceK
    compactSpaceK := reaction.compactSpaceK
    gt := reaction.gt
    metric := reaction.metric
    parameter := reaction.parameter
    parameterContinuous := reaction.parameterContinuous
    realizesFlow := reaction.realizesFlow
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound :=
      data.fullCovariantRicciDerivativeBound
    meanScalarFloor := reaction.meanScalarFloor
    covariantDerivativeRegularity := fun _t ↦ inferInstance
    meanScalarFloor_pos := reaction.meanScalarFloor_pos
    normalizedFlow := fun t x ↦ reaction.normalizedFlow t.1 t.2 x
    jointMetricEntries := fun t x ↦ reaction.jointMetricEntries t.1 x
    differentiateMovingTotalScalar := data.differentiateMovingTotalScalar
    differentiateMovingVolume := fun t ↦
      reaction.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
        t.1 (reaction.normalizedFlow t.1 t.2)
    finiteVolumeMeasureContinuous :=
      reaction.finiteVolumeMeasureContinuous
    scalarJointContinuous := reaction.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      reaction.tracelessRicciNormSqJointContinuous
    finiteTracelessRicciEnergy :=
      reaction.toMeasureAnalyticData3.finiteTracelessRicciEnergy
    fullCovariantRicciControl := data.fullCovariantRicciControl
    meanScalarLower := reaction.meanScalarLower }

/-- Construct the established compact finite-time positive-Einstein package.
The intermediate finite-energy package applies the bounded-variation theorem
to prove its finite absolute-dissipation field. -/
noncomputable def toFiniteTimePositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M :=
  data.toFiniteTracelessEnergyPositiveEinsteinAnalyticData3
    |>.toFiniteTimePositiveEinsteinAnalyticData3

/-- Reaction domination proves finite total forward traceless-Ricci energy. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.reaction.gt) (Ici 0) := by
  exact
    data.toFiniteTracelessEnergyPositiveEinsteinAnalyticData3.finiteTracelessRicciEnergy

/-- Finite absolute mean-scalar/variance dissipation follows from the proved
finite energy and bounded mean-scalar variation. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedMeanScalarAbsoluteVarianceDissipation data.reaction.gt)
      (Ici 0) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- The reaction-decay extension constructs a positive Einstein metric. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The resulting positive Einstein metric admits a unit-curvature
normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature sphere recognition turns the reaction-decay construction
into the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact data.toFiniteTimePositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3

end Poincare
