import Poincare.Global.DeTurckBUCJointSpacetimeMetricAssembly
import Poincare.Global.DeTurckPointFlowMetricTwoRestartPackage

/-!
# Joint C5 boundary for the reconstructed inverse-gauge metric

The chartwise metric assembly is exact, but its existing `hsmooth` premise is
slice-wise in time.  This module records the precise additional joint
spacetime regularity needed by the inverse DeTurck point-flow construction.

If the reconstructed chart coefficient is jointly `C⁵`, exact chartwise
realization transfers that regularity to `MetricEntriesJointContDiffAt ... 5`.
The concrete `C⁵` metric-to-`C⁴` field bridge can then construct the full
two-restart point-flow package.  No theorem here asserts that slice-wise
spatial smoothness supplies the missing time derivatives.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section ChartMetricRegularityTransfer

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Joint regularity of the genuine transported chart metric implies the
canonical-frame entry regularity used by the DeTurck coordinate estimates. -/
theorem metricEntriesJointContDiffAt_of_anchorChartMetricFlow_contDiffAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {anchor : M} {k : ℕ∞ω}
    (hChart : ContDiffAt ℝ k
      (Function.uncurry (anchorChartMetricFlow gt anchor))
      (t₀, extChartAt I anchor anchor)) :
    MetricEntriesJointContDiffAt gt t₀ anchor k := by
  intro b c
  change E at b c
  have hb : ContDiffAt ℝ k
      (fun _ : ℝ × E ↦ b) (t₀, extChartAt I anchor anchor) :=
    contDiffAt_const
  have hc : ContDiffAt ℝ k
      (fun _ : ℝ × E ↦ c) (t₀, extChartAt I anchor anchor) :=
    contDiffAt_const
  have hEntry : ContDiffAt ℝ k
      (fun p : ℝ × E ↦ anchorChartMetricFlow gt anchor p.1 p.2 b c)
      (t₀, extChartAt I anchor anchor) := by
    simpa only [Function.uncurry] using (hChart.clm_apply hb).clm_apply hc
  exact hEntry.congr_of_eventuallyEq
    (anchorChartMetricFlow_apply_eventuallyEq_metricEntryJointChart
      gt t₀ anchor b c).symm

end ChartMetricRegularityTransfer

section ReconstructedJointFiveTransfer

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable { ι κ : Type* }

/-- Exact chartwise realization transfers joint `C⁵` regularity of the
reconstructed coefficient to joint `C⁵` entries of the assembled metric.

The `hJointReconstruction` premise is the exact currently-unproved boundary:
the existing chartwise assembly retains spatial smoothness separately at each
time, but does not manufacture five joint time--space derivatives. -/
theorem metricEntriesJointContDiffAt_five_of_chartwiseReconstruction
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (t₀ : ℝ) (anchor : M)
    (hJointReconstruction : ContDiffAt ℝ 5
      (fun q : ℝ × E ↦
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi q.1 anchor q.2)
      (t₀, extChartAt I anchor anchor))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z) :
    MetricEntriesJointContDiffAt rt t₀ anchor 5 := by
  have htarget :
      (fun q : ℝ × E ↦ q.2) ⁻¹' (extChartAt I anchor).target ∈
        nhds (t₀, extChartAt I anchor anchor) :=
    continuousAt_snd.eventually
      ((isOpen_extChartAt_target anchor).mem_nhds
        (mem_extChartAt_target anchor))
  have heq :
      Function.uncurry (anchorChartMetricFlow rt anchor) =ᶠ[
          nhds (t₀, extChartAt I anchor anchor)]
        (fun q : ℝ × E ↦
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi q.1 anchor q.2) := by
    filter_upwards [htarget] with q hq
    simpa only [Function.uncurry, anchorChartMetricFlow] using
      hrealize q.1 q.2 hq
  have hChart : ContDiffAt ℝ 5
      (Function.uncurry (anchorChartMetricFlow rt anchor))
      (t₀, extChartAt I anchor anchor) :=
    hJointReconstruction.congr_of_eventuallyEq heq
  exact metricEntriesJointContDiffAt_of_anchorChartMetricFlow_contDiffAt
    hChart

/-- At initial time zero, the exact joint-`C⁵` reconstruction premise is
sufficient to construct the complete inverse DeTurck two-restart point-flow
package used by the supplied physical-flow assembly. -/
theorem exists_inverseDeTurck_twoRestartPointFlowPackage_of_chartwiseReconstruction_five
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi₀ : M → ℝ → E → E)
    (DPhi₀ : M → ℝ → E → E →L[ℝ] E)
    (anchor : M) (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hJointReconstruction : ContDiffAt ℝ 5
      (fun q : ℝ × E ↦
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi₀ DPhi₀ q.1 anchor q.2)
      (0, extChartAt I anchor anchor))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi₀ DPhi₀ s anchor z) :
    ∃ t ∈ Ioo (0 : ℝ) Tmax,
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        Nonempty (TwoRestartPointFlowPackage
          (fun s ↦ inverseDeTurckChartCoordinateField rt bg anchor s)
          Phi Psi t (extChartAt I anchor anchor) y₁) := by
  have hJoint : MetricEntriesJointContDiffAt rt 0 anchor 5 :=
    metricEntriesJointContDiffAt_five_of_chartwiseReconstruction
      rt D K u₀ Phi₀ DPhi₀ 0 anchor
        hJointReconstruction hrealize
  exact exists_inverseDeTurck_twoRestartPointFlowPackage_of_metricEntries_five
    rt bg anchor Tmax hTmax hJoint

end ReconstructedJointFiveTransfer

end Poincare
