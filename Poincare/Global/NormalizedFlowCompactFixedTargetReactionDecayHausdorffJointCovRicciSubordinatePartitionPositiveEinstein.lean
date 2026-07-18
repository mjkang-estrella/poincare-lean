import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciPositiveEinstein
import Poincare.Global.NormalizedFlowHausdorffPartitionStokes

/-!
# Subordinate-partition Stokes for the compact Hausdorff reaction endpoint

The compact joint-covariant-Ricci endpoint still accepted
`ClosedLaplacianStokes` directly at every nonnegative time.  This module
replaces that conclusion by its geometric producer: at each nonnegative
slice, a finite smooth partition of unity subordinate to Hausdorff charts,
together with the compactly supported coordinate flux data needed for the
global finite-sum proof of Stokes.

`FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes` proves
the required integral cancellation.  Thus neither this package nor the
strongest end-to-end boundary built from it stores Stokes as an assumption.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/-- Hausdorff reaction-decay data whose scalar Stokes input is replaced by
an actual finite subordinate coordinate geometry on every nonnegative flow
slice.  The geometry contains no integral-cancellation field. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3
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
  covariantRicciNormSqJointContinuous :
    letI : TopologicalSpace reaction.K := reaction.topologicalSpaceK
    Continuous (fun p : reaction.K × M ↦
      covRicciNormSqAt (reaction.metric p.1) p.2)
  scalarDomination :
    GlobalFiniteHausdorffChartFrameScalarDomination
      reaction.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
  scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
    FiniteSubordinateHausdorffLaplacianGeometry
      (reaction.gt t.1) (fun y ↦ (reaction.gt t.1).scalarAt y)

/-- Fixed-target form of the subordinate-partition joint-covariant-Ricci
package. -/
def FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M] : Type (max u (v + 1)) :=
  ∀ [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [SecondCountableTopology M] [ConnectedSpace M],
      letI : MeasurableSpace M := borel M
      letI : BorelSpace M := ⟨rfl⟩
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M

namespace NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3

variable [SimplyConnectedSpace M]

/-- Derive closed scalar-Laplacian Stokes from the finite partition and its
coordinate flux proof, then recover the verified compact joint-covariant-
Ricci Hausdorff endpoint. -/
noncomputable def toJointCovRicciPositiveEinsteinAnalyticData3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
      M :=
  { reaction := data.reaction
    compactTensorReferenceControl := data.compactTensorReferenceControl
    covariantRicciNormSqJointContinuous :=
      data.covariantRicciNormSqJointContinuous
    scalarDomination := data.scalarDomination
    scalarStokes := fun t ↦
      (data.scalarSubordinateGeometry t).closedLaplacianStokes }

/-- The geometric Stokes producer reaches finite forward traceless-Ricci
energy through the verified compact Hausdorff endpoint. -/
theorem finiteTracelessRicciEnergy
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.reaction.gt) (Ici 0) :=
  data.toJointCovRicciPositiveEinsteinAnalyticData3.finiteTracelessRicciEnergy

/-- The subordinate-partition package reaches the positive Einstein
endpoint. -/
theorem positiveEinsteinMetric3
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    PositiveEinsteinMetric3 M :=
  data.toJointCovRicciPositiveEinsteinAnalyticData3.positiveEinsteinMetric3

/-- Unit-curvature recognition turns the geometrically produced Stokes
package into the topological sphere conclusion. -/
theorem sphereConclusion
    (data :
      NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toJointCovRicciPositiveEinsteinAnalyticData3.sphereConclusion
    unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3

/-- Pointwise conversion of the fixed-target subordinate-partition package
to the verified joint-covariant-Ricci Hausdorff endpoint. -/
noncomputable def
    fixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3_of_subordinatePartition
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [SimplyConnectedSpace M]
    (data :
      FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.{u, v}
        M) :
    FixedTargetNormalizedFlowSphereCompactReactionDecayHausdorffJointCovRicciPositiveEinsteinAnalyticData3.{u, v}
      M := by
  intro _chartedSpace _smoothManifold _secondCountable _connected
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact data.toJointCovRicciPositiveEinsteinAnalyticData3

end Poincare
