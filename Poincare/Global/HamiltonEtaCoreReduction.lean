import Poincare.Global.HamiltonInitialPinchingReactionCoreReduction
import Poincare.Global.HamiltonStokesFreeReactionCore

/-!
# Hamilton convergence from a uniform normalization gap

The gap supplies both the positive mean floor and the reaction rate.
Existence of a flow and compact realization with this gap remains an input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonEtaCoreReduction
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- Eta bounds the mean scalar from below on every positive-scalar slice.
The arithmetic only needs `d ≤ 2`, hence applies to the core's `0 < d ≤ 1`. -/
theorem meanFloorFromEta
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (d eta : ℝ)
    (hd : d ≤ 2) (heta : 0 < eta)
    (hp : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hgap : ∀ t ∈ Ici (0 : ℝ), ∀ x,
      2*(2-d)*(gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
        (4/3 : ℝ)*meanScalar (gt t)) :
    0 < (3/4 : ℝ)*eta ∧ ∀ t : Ici (0 : ℝ), (3/4 : ℝ)*eta ≤ meanScalar (gt t.1) := by
  classical
  constructor
  · positivity
  · intro t
    let x : M := Classical.choice (inferInstance : Nonempty M)
    have hU := (gt t.1).tracelessRicciNormSqAt_nonneg x (by norm_num)
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq] at hU
    have hN : 0 ≤ (gt t.1).ricciNormSqAt x := by
      norm_num at hU
      exact (div_nonneg (by positivity) (by norm_num)).trans hU
    have hterm : 0 ≤ 2*(2-d)*(gt t.1).ricciNormSqAt x / (gt t.1).scalarAt x :=
      div_nonneg (mul_nonneg (by linarith) hN) (hp t.1 t.2 x).le
    have h := hgap t.1 t.2 x
    linarith

/-- The initial-pinching Eta core with the Stokes and variance-energy clauses
removed. The uniform normalization gap is the sole residual estimate. -/
def HamiltonReactionCore3Eta (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (epsilon delta : ℝ),
      Continuous parameter ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      (∀ slot : MetricEntryThirdJetSlot 3 M,
        Continuous (fun p : K × ClosedSmoothModel 3 ↦
          metricEntryThirdJetProfile (metric p.1) slot p.2)) ∧
      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      (∀ x, 0 < (gt 0).scalarAt x) ∧
      1/6 < epsilon ∧ epsilon ≤ 1/3 ∧
      GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
      0 < delta ∧ delta ≤ 1 ∧
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) ∧
      (∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
        2 * (2-delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
          (4/3 : ℝ) * meanScalar (gt t))

/-- Eta supplies the final core with mean floor `3 * eta / 4` and rate `eta`. -/
theorem hamiltonReactionCore3Final_of_eta
    (h : HamiltonReactionCore3Eta.{u, v} M) :
    HamiltonReactionCore3Final.{u, v} M := by
  rcases h with ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta,
    hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
    hdpos, hdle, hadm, eta, heta, hgap⟩
  letI : TopologicalSpace K := topK
  haveI : CompactSpace K := compactK
  have hpos := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
    gt hjoint hflow hinit
  obtain ⟨hc, hmean⟩ := meanFloorFromEta gt delta eta (by linarith) heta hpos hgap
  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
    gt epsilon hjoint hflow hinit hele hpin
  refine ⟨K, topK, compactK, gt, metric, parameter, (3/4 : ℝ) * eta, eta,
    hparam, hreal, hc, hmean, hflow, hjoint, heta, ?_, hjet⟩
  intro t ht x
  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
    (gt t) x (by linarith) (by linarith) hdpos.le hadm (hpos t ht x)
    ((hpres t ht).1 x) (hgap t ht x)

/-- The Eta-only core reaches the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta
    (h : HamiltonReactionCore3Eta.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
    (hamiltonReactionCore3Final_of_eta h)

/-- Open existence obligation for Eta-only cores on closed simply connected
smooth three-manifolds with compatible Borel structures. -/
def UniversalHamiltonReactionCoreEtaStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonReactionCore3Eta.{u, v} N

/-- Universal Eta-only cores imply universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEta
    (h : UniversalHamiltonReactionCoreEtaStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Eta (h N)

end Poincare.HamiltonEtaCoreReduction
