import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint

/-!
# The finite-energy normalized-flow interface

The smallest sufficient flow-existence boundary identified by the Hamilton
front survey: a forward-time normalized Ricci flow with integrable traceless
Ricci energy, a compact parameter family realizing it with continuous
mean-energy pair, and a positive mean-scalar floor.  It removes the reaction,
moving-density, and jet machinery while reusing the landed analytic endpoint.
Existence remains open; both conditional directions are proved here.  See
`harness/reports/hamilton-front-decomposition_done.md`, section 4, task 3.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare

/-- Forward-time finite-energy normalized-flow existence with compact realization. -/
def HamiltonFiniteEnergyFlowExistence3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (c : ℝ),
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) ∧
      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The finite-energy interface yields the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3
    (h : HamiltonFiniteEnergyFlowExistence3.{u, v} M) :
    HamiltonConvergencePinchedLimit3 M := by
  rcases h with ⟨gt, K, topK, compactK, metric, parameter, c, _flow, hE, hreal, hcont, hc, hlower⟩
  letI : TopologicalSpace K := topK
  letI : CompactSpace K := compactK
  exact (hamiltonConvergencePinchedLimit3_iff_core (M := M)).mpr
    (hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt hE metric parameter hreal hcont hc hlower)

/-- A reaction record supplies the finite-energy interface. -/
theorem finiteEnergyFlowExistence3_of_reactionDecayAnalyticData3
    (r : NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.{u, v} M) :
    HamiltonFiniteEnergyFlowExistence3.{u, v} M := by
  let d := r.toMeasureAnalyticData3.toCompactMeanEnergyAnalyticData3
  exact ⟨d.gt, d.K, d.topologicalSpaceK, d.compactSpaceK, d.metric, d.parameter,
    d.meanScalarFloor, r.normalizedFlow, d.finiteTracelessRicciEnergy,
    d.realizesFlow, d.invariantPairContinuous, d.meanScalarFloor_pos, d.meanScalarLower⟩

/-- Open obligation: the finite-energy interface on every closed simply connected
smooth 3-manifold, for every compatible Borel structure, with compact parameter
space in `Type v`. -/
def UniversalHamiltonFiniteEnergyFlowExistenceStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonFiniteEnergyFlowExistence3.{u, v} N

/-- Universal finite-energy flow existence discharges universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalFiniteEnergyFlowExistence
    (h : UniversalHamiltonFiniteEnergyFlowExistenceStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamiltonConvergencePinchedLimit3_of_finiteEnergyFlowExistence3 (h N)

end Poincare
