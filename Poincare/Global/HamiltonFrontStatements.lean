import Poincare.Global.CartanTwoNeighborhoodDevelopment
import Poincare.Global.NormalizedFlowFormalProfilePositiveEinstein

/-!
# Open Hamilton analytic inputs and their checked consequences

The five inputs below remain open. This module registers their simultaneous
existence as an obligation and proves only conditional reductions. In
particular, universal existence includes the task of producing a suitable
normalized flow on every manifold in the statement. Hamilton convergence for
an already supplied positive-Ricci flow does not by itself provide that input.
-/

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

/-- Exactly the open inputs of the compact-tensor formal-profile constructor.
`reaction` stores the normalized flow, compact metric parameterization, positive
mean-scalar floor, and reaction decay. Its existing Hamilton producer requires
open pinching-core data and a positive coefficient gap.
`compactTensorReferenceControl` supplies continuous metric and volume comparison
with a reference metric. `hequicontinuous` controls each scalar third-jet profile
uniformly over forward time. `hpointwiseCompact` bounds those profiles in compact
sets at each point and slot. `scalarSubordinateGeometry` supplies the finite
subordinate Hausdorff Laplacian geometry for scalar curvature at each time.
No input is constructed here. The independent universe `v` is that of the
reaction record's compact parameter space. -/
structure HamiltonFrontInputs (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
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
  hequicontinuous : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Equicontinuous (fun t : Ici (0 : ℝ) =>
        (metricEntryThirdJetProfile (reaction.gt t.1) slot :
          ClosedSmoothModel 3 → ℝ))
  hpointwiseCompact :
      ∀ (slot : MetricEntryThirdJetSlot 3 M) (z : ClosedSmoothModel 3),
        ∃ Q : Set ℝ, IsCompact Q ∧
          ∀ t : Ici (0 : ℝ),
            metricEntryThirdJetProfile (reaction.gt t.1) slot z ∈ Q
  scalarSubordinateGeometry : ∀ t : Ici (0 : ℝ),
      FiniteSubordinateHausdorffLaplacianGeometry
        (reaction.gt t.1) (fun y => (reaction.gt t.1).scalarAt y)

/-- Open universal existence of all five Hamilton inputs, for every compatible
Borel measurable structure and with compact parameter space in `Type v`. -/
def UniversalHamiltonFrontInputsStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      Nonempty (HamiltonFrontInputs.{u, v} N)

/-- Open universal positive-Einstein existence on closed simply connected
smooth three-manifolds. No measurable structure is an endpoint hypothesis. -/
def UniversalPositiveEinsteinStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      PositiveEinsteinMetric3 N

/-- Open universal Hamilton pinched-limit payload: a smooth metric with
differentiable scalar curvature, zero traceless Ricci, and positive scalar
curvature somewhere. This is the analytic endpoint, not sphere recognition. -/
def UniversalHamiltonConvergenceStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonConvergencePinchedLimit3 N

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The five open inputs imply positive-Einstein existence through formal
profiles, finite traceless energy, and finite absolute dissipation. -/
theorem positiveEinsteinMetric3_of_hamiltonFrontInputs
    (inputs : HamiltonFrontInputs.{u, v} M) : PositiveEinsteinMetric3 M :=
  (NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl
    inputs.reaction inputs.compactTensorReferenceControl inputs.hequicontinuous
    inputs.hpointwiseCompact inputs.scalarSubordinateGeometry).positiveEinsteinMetric3

/-- Universal open Hamilton inputs imply universal positive-Einstein existence.
The canonical Borel structure supplies the analytic measurable instances. -/
theorem universalPositiveEinstein_of_universalHamiltonFrontInputs
    (hInputs : UniversalHamiltonFrontInputsStatement.{u, v}) :
    UniversalPositiveEinsteinStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact positiveEinsteinMetric3_of_hamiltonFrontInputs (Classical.choice (hInputs N))

/-- Universal open Hamilton inputs imply the Hamilton pinched-limit endpoint;
this conditional theorem does not construct those inputs. -/
theorem universalHamiltonConvergence_of_universalHamiltonFrontInputs
    (hInputs : UniversalHamiltonFrontInputsStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} :=
  fun N _ _ _ _ _ _ _ _ ↦
    hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3
      (universalPositiveEinstein_of_universalHamiltonFrontInputs hInputs N)

/-- Conditional smooth Poincare composition. The Hamilton inputs and the
Cartan joint successor-data and successor-equality neighborhoods H1 and H2
all remain open universal hypotheses. -/
theorem poincareConjecture_of_hamiltonFrontInputs_of_two_neighborhoods
    (hInputs : UniversalHamiltonFrontInputsStatement.{u, v})
    (hData : CartanTwoNeighborhoodDevelopment.UniversalUnitCurvatureSuccessorDataNeighborhoodStatement.{u})
    (hEquality : CartanTwoNeighborhoodDevelopment.UniversalUnitCurvatureSuccessorEqualityNeighborhoodStatement.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods
    (universalHamiltonConvergence_of_universalHamiltonFrontInputs hInputs)
    hData hEquality

end Poincare
