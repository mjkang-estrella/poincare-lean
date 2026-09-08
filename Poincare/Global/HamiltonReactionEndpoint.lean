import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowStationaryLimit

/-!
# The reaction record alone produces the Hamilton endpoint

Of the five `HamiltonFrontInputs` fields, the `reaction` record already
contains the finite-energy compact-mean data consumed by the landed
`hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower`.
So the tensor-reference, third-jet, and subordinate-geometry inputs are not
needed for the endpoint.  The universal reaction existence statement is the
correspondingly smaller open obligation.  See
`harness/reports/hamilton-front-decomposition_done.md`, section 4, task 1.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The reaction record alone yields the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_reactionDecayAnalyticData3
    (reaction : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M) :
    HamiltonConvergencePinchedLimit3 M := by
  let data := reaction.toMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  apply (hamiltonConvergencePinchedLimit3_iff_core (M := M)).mpr
  exact hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    data.gt data.finiteTracelessRicciEnergy data.metric data.parameter data.realizesFlow
    data.invariantPairContinuous data.meanScalarFloor_pos data.meanScalarLower

/-- The scalar curvature of a supplied reaction record is `C²` at every forward time. -/
theorem scalarAt_contMDiff_two_of_reactionDecayAnalyticData3
    (r : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M)
    (t : Ici (0 : ℝ)) :
    ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun x : M ↦ (r.gt t.1).scalarAt x) := by
  intro x
  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
    (r.normalizedFlow t.1 t.2)
    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (r.jointMetricEntries t.1 y)) x

/-- Open obligation: every closed simply connected smooth 3-manifold, with any
compatible Borel structure, carries a reaction-decay normalized-flow record
with compact parameter space in `Type v`. -/
def UniversalHamiltonReactionExistenceStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      Nonempty (NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} N)

/-- Universal reaction existence discharges universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalHamiltonReactionExistence
    (h : UniversalHamiltonReactionExistenceStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamiltonConvergencePinchedLimit3_of_reactionDecayAnalyticData3 (Classical.choice (h N))

end Poincare
