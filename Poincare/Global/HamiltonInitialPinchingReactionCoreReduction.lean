import Poincare.Global.NormalizedFlowInitialPinchingPreservation
import Poincare.Global.HamiltonMeanFloorFromEnergyDomination
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination

/-!
# Reaction core from initial pinching and explicit residual estimates

Initial pinching supplies the forward eigenvalue floor and Ricci quotient
bound. Energy domination and scalar Stokes supply the positive mean floor.
The scalar-to-mean comparison and strict coefficient gap supply a uniform
reaction rate. Existence of these data remains an input.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonInitialPinchingReactionCoreReduction

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The survey's initial-data core, with all residual estimates displayed. -/
def HamiltonReactionCore3InitialPinching (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (epsilon delta C : ℝ),
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
      (∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) ∧
      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
      0 < (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C

/-- Initial pinching and the residual estimates reconstruct the final core,
with rate equal to the coefficient gap times the initial mean scalar. -/
theorem hamiltonReactionCore3Final_of_initialPinching
    (h : HamiltonReactionCore3InitialPinching.{u, v} M) :
    HamiltonReactionCore3Final.{u, v} M := by
  rcases h with ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta, C,
    hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
    hdpos, hdle, hadm, hstokes, henergy, hcompare, hgap⟩
  letI : TopologicalSpace K := topK
  haveI : CompactSpace K := compactK
  let c : ℝ := meanScalar (gt 0)
  let gamma : ℝ := (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C
  have hfloor := HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy
    gt hjoint hflow hstokes hinit henergy
  have hpos := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
    gt hjoint hflow hinit
  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
    gt epsilon hjoint hflow hinit hele hpin
  refine ⟨K, topK, compactK, gt, metric, parameter, c, gamma * c,
    hparam, hreal, hfloor.1, hfloor.2, hflow, hjoint,
    mul_pos hgap hfloor.1, ?_, hjet⟩
  intro t ht
  exact normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
    (gt t) (by linarith) (by linarith) hdpos.le (by linarith) hadm
    (pinchingQuotientCoefficient_pos epsilon).le (hpos t ht)
    (hpres t ht).1 (hpres t ht).2 (hcompare t ht)
    (mul_le_mul_of_nonneg_left (hfloor.2 ⟨t, ht⟩) hgap.le)

end Poincare.HamiltonInitialPinchingReactionCoreReduction
