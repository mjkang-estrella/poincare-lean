import Poincare.Global.HamiltonChartDensityLocalDomination
import Poincare.Global.HamiltonFamilyVolumeMeasureContinuity

/-!
# The combined reduced reaction core

Both landed clause removals combined: the local density domination clause is
derived from joint C³ metric entries (`HamiltonChartDensityLocalDomination`),
and the three compact-family continuity clauses are derived from joint scalar
third-jet profile continuity (`HamiltonCompactFamilyInvariantContinuity`,
`HamiltonFamilyVolumeMeasureContinuity`).  What remains is the genuine
analytic content: a forward-time normalized Ricci flow with joint C³ metric
entries, a compact realization with jointly continuous jet profiles, a positive
mean-scalar floor, and a uniform reaction domination.  Its existence is the
open obligation; this module only proves the reduction to the endpoint.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare

/-- The reduced reaction core: flow, joint C³ entries, compact realization with
continuous jet profiles, positive mean floor, uniform reaction domination. -/
def HamiltonReactionCore3Final (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (c rate : ℝ),
      Continuous parameter ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
      0 < rate ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
          -rate * (gt t).tracelessRicciNormSqAt x) ∧
      (∀ slot : MetricEntryThirdJetSlot 3 M,
        Continuous (fun p : K × ClosedSmoothModel 3 ↦
          metricEntryThirdJetProfile (metric p.1) slot p.2))

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The combined core reconstructs the domination-free core with its three
continuity clauses. -/
theorem hamiltonReactionCore3'_of_final
    (h : HamiltonReactionCore3Final.{u, v} M) :
    HamiltonChartDensityLocalDomination.HamiltonReactionCore3'.{u, v} M := by
  rcases h with ⟨K, topK, compactK, gt, metric, parameter, c, rate,
    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction, hjet⟩
  letI : TopologicalSpace K := topK
  haveI : CompactSpace K := compactK
  have hcurv :=
    HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous
      K metric hjet
  have hmeas :=
    HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
      K metric hjet
  exact ⟨K, topK, compactK, gt, metric, parameter, c, rate,
    hparam, hreal, hc, hlower, hflow, hjoint, hrate, hreaction, hmeas, hcurv.1, hcurv.2⟩

/-- The combined core reconstructs the original reaction core. -/
theorem hamiltonReactionCore3_of_final
    (h : HamiltonReactionCore3Final.{u, v} M) : HamiltonReactionCore3.{u, v} M :=
  HamiltonChartDensityLocalDomination.hamiltonReactionCore3_of_core'
    (hamiltonReactionCore3'_of_final h)

/-- The combined core reaches the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
    (h : HamiltonReactionCore3Final.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3 (hamiltonReactionCore3_of_final h)

/-- Open obligation: the combined reduced core on every closed simply connected
smooth 3-manifold, for every compatible Borel structure. -/
def UniversalHamiltonReactionCoreFinalStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonReactionCore3Final.{u, v} N

/-- The combined reduced core discharges universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreFinal
    (h : UniversalHamiltonReactionCoreFinalStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final (h N)

end Poincare
