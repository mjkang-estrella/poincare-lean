import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayPositiveEinstein
import Poincare.Global.NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint

/-!
# Reaction-decay positive Einstein data from Hausdorff scalar variation

The reaction-decay positive-Einstein package consumes the normalized moving
total-scalar identity.  This file exposes an honest lower-level alternative:
instead of storing that derivative, it stores precisely

* scalar-density domination relative to the corrected finite-atlas
  chart-frame density variation; and
* scalar Laplacian Stokes at every nonnegative flow time.

Joint `C³` metric-entry regularity constructs the global Lichnerowicz
assembly, including the pointwise scalar time derivative.  Normalized flow,
that assembly, scalar-density domination, and Stokes then invoke the
localized Hausdorff first-variation theorem to construct the moving
total-scalar derivative.  Every subsequent finite-energy, finite-dissipation,
Einstein, unit-curvature, and sphere conclusion is reused from the existing
reaction-decay positive-Einstein package.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- Reaction-decay positive-Einstein data with moving total-scalar
differentiation replaced by its two lower-level Hausdorff analytic inputs. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3
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
  scalarDomination :
    GlobalFiniteHausdorffChartFrameScalarDomination
      reaction.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
  scalarStokes : ∀ t : Ici (0 : ℝ),
    ClosedLaplacianStokes (reaction.gt t.1)
      (fun y ↦ (reaction.gt t.1).scalarAt y)

/-- Fixed-target form of the Hausdorff reaction-decay positive-Einstein
package.  The quantified smooth structure is requested only after a
downstream smoothing theorem chooses it. -/
def FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Construct the moving total-scalar identity from scalar-density
domination, automatic Lichnerowicz regularity, normalized flow, and Stokes,
thereby recovering the established reaction-decay positive-Einstein
contract. -/
noncomputable def toReactionDecayPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  let reaction := data.reaction
  letI : ∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (reaction.gt s).leviCivita 1 :=
    fun _s ↦ inferInstance
  let lichnerowicz : GlobalLichnerowiczAssemblyRegularity reaction.gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
      reaction.jointMetricEntries
  exact {
    reaction := reaction
    compactTensorReferenceControl := data.compactTensorReferenceControl
    fullCovariantRicciDerivativeBound :=
      data.fullCovariantRicciDerivativeBound
    fullCovariantRicciControl := data.fullCovariantRicciControl
    differentiateMovingTotalScalar := fun t ↦
      data.scalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
        lichnerowicz t.1
          (reaction.normalizedFlow t.1 t.2) (data.scalarStokes t) }

/-- The Hausdorff package converts to the finite-traceless-energy endpoint
proved by reaction domination. -/
noncomputable def toFiniteTracelessEnergyPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTracelessEnergyPositiveEinsteinAnalyticData3.{u, v}
      M :=
  data.toReactionDecayPositiveEinsteinAnalyticData3
    |>.toFiniteTracelessEnergyPositiveEinsteinAnalyticData3

/-- The Hausdorff package reaches the established compact finite-time
positive-Einstein endpoint. -/
noncomputable def toFiniteTimePositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactFiniteTimePositiveEinsteinAnalyticData3.{u, v}
      M :=
  data.toReactionDecayPositiveEinsteinAnalyticData3
    |>.toFiniteTimePositiveEinsteinAnalyticData3

/-- Reaction domination still proves finite total forward
traceless-Ricci energy. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.reaction.gt) (Ici 0) := by
  exact data.toReactionDecayPositiveEinsteinAnalyticData3.finiteTracelessRicciEnergy

/-- The derived moving total-scalar identity and finite reaction energy give
finite absolute mean-scalar/variance dissipation. -/
theorem finiteAbsoluteDissipation
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedMeanScalarAbsoluteVarianceDissipation data.reaction.gt)
      (Ici 0) := by
  exact data.toReactionDecayPositiveEinsteinAnalyticData3.finiteAbsoluteDissipation

/-- The lower-level Hausdorff package constructs a positive Einstein
metric. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M := by
  exact data.toReactionDecayPositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- The constructed positive Einstein metric has a unit-curvature
normalization. -/
theorem existsUnitConstantCurvature
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  exact
    data.toReactionDecayPositiveEinsteinAnalyticData3.existsUnitConstantCurvature

/-- Unit-curvature recognition yields the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  exact data.toReactionDecayPositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffPositiveEinsteinAnalyticData3

/-- Convert the fixed-target Hausdorff package to the established
fixed-target reaction-decay positive-Einstein contract, pointwise in the
smooth structure chosen downstream. -/
noncomputable def
    fixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3_of_hausdorff
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffPositiveEinsteinAnalyticData3.{u, v}
        M) :
    FixedTargetNormalizedFlowSphereCompactReactionDecayPositiveEinsteinAnalyticData3.{u, v}
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact data.toReactionDecayPositiveEinsteinAnalyticData3

end Poincare
