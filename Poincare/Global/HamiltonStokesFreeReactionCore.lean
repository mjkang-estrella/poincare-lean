import Poincare.Global.HamiltonInitialPinchingReactionCoreReduction
import Poincare.Global.IntrinsicLaplacianCoordinateForm

/-!
# The reaction core without the Stokes premise

`IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow`
proves the closed Laplacian Stokes property for the scalar curvature of a
forward normalized Ricci flow with joint C³ metric entries, which are already
clauses of the initial-pinching core.  So that premise can be dropped: the
remaining residual estimates are the scalar-to-mean comparison with its
coefficient gap and the variance-energy domination.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonStokesFreeReactionCore

open HamiltonInitialPinchingReactionCoreReduction

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The initial-pinching core with the Stokes premise removed. -/
def HamiltonReactionCore3InitialPinchingNS (M : Type u)
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
      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
      0 < (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C


/-- The Stokes premise is automatic for the scalar curvature of the flow. -/
theorem hamiltonReactionCore3InitialPinching_of_NS
    (h : HamiltonReactionCore3InitialPinchingNS.{u, v} M) :
    HamiltonReactionCore3InitialPinching.{u, v} M := by
  obtain ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta, C,
    hparam, hreal, hjet, hjoint, hflow, hinit, heps1, heps2, hfloor,
    hdelta1, hdelta2, hadm, henergy, hcomp, hgap⟩ := h
  exact ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta, C,
    hparam, hreal, hjet, hjoint, hflow, hinit, heps1, heps2, hfloor,
    hdelta1, hdelta2, hadm,
    IntrinsicLaplacianCoordinateForm.closedLaplacianStokes_scalarAt_of_normalizedRicciFlow
      gt hflow hjoint,
    henergy, hcomp, hgap⟩

/-- The Stokes-free core reaches the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_NS
    (h : HamiltonReactionCore3InitialPinchingNS.{u, v} M) :
    HamiltonConvergencePinchedLimit3 M :=
  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching
    (hamiltonReactionCore3InitialPinching_of_NS h)

/-- Open obligation: the Stokes-free initial-pinching core on every closed
simply connected smooth three-manifold. -/
def UniversalHamiltonReactionCoreInitialPinchingNSStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonReactionCore3InitialPinchingNS.{u, v} N

/-- The Stokes-free core discharges universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_NS
    (h : UniversalHamiltonReactionCoreInitialPinchingNSStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} := by
  intro N _ _ _ _ _ _ _ _
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  exact hamiltonConvergencePinchedLimit3_of_NS (h N)

end Poincare.HamiltonStokesFreeReactionCore
