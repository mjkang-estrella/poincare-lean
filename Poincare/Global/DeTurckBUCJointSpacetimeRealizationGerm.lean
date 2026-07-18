import Poincare.Global.DeTurckBUCJointSpacetimeMetricAssembly

/-!
# Exact chart realization gives the inverse-gauge spacetime germ

The global chartwise assembly theorem realizes every reconstructed coefficient
at every genuine chart point.  This file records the local consequence needed
by the interior Ricci and Hamilton bridges: at a fixed chart point, exact
realization restricts first to a joint spacetime germ and then to the ordinary
time germ of the same supplied endpoint and variational families.

No endpoint trajectory is selected here.  In particular, these lemmas apply
to the caller-supplied physical point flow rather than to an independently
restarted existential flow.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/-- Exact realization of a chartwise reconstructed family on the preferred
chart target gives the corresponding joint spacetime germ at every genuine
chart point. -/
theorem reconstructedInverseGaugeMetricSpacetime_eventuallyEq_chartMetric_of_chartwiseRealization
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (anchor : M) {t : ℝ} {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z) :
    reconstructedInverseGaugeMetricSpacetime
        (D anchor) K (u₀ anchor) (Phi anchor) (DPhi anchor) =ᶠ[
          nhds (t, z₀)]
      (fun q : ℝ × E ↦
        CovariantDerivative.chartMetric (rt q.1).inner anchor q.2) := by
  have htarget :
      (fun q : ℝ × E ↦ q.2) ⁻¹' (extChartAt I anchor).target ∈
        nhds (t, z₀) := by
    exact continuousAt_snd
      ((isOpen_extChartAt_target anchor).mem_nhds hz₀)
  filter_upwards [htarget] with q hq
  simpa only [chartwiseReconstructedInverseGaugeMetricSpacetime] using
    (hrealize q.1 q.2 hq).symm

/-- Restrict exact chartwise realization to the supplied endpoint trajectory
and variational differential at one initial coordinate point. -/
theorem reconstructedInverseGaugeMetric_form_eventuallyEq_chartMetric_of_chartwiseRealization
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (anchor : M) {t : ℝ} {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z) :
    reconstructedInverseGaugeMetric
        (D anchor) K (u₀ anchor)
        (fun s : ℝ ↦ Phi anchor s z₀)
        (fun s : ℝ ↦ DPhi anchor s z₀) =ᶠ[nhds t]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀) := by
  apply reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm
    (D anchor) K (u₀ anchor) (Phi anchor) (DPhi anchor)
      (fun s : ℝ ↦ Phi anchor s z₀)
      (fun s : ℝ ↦ DPhi anchor s z₀)
      rt anchor z₀
  · exact
      reconstructedInverseGaugeMetricSpacetime_eventuallyEq_chartMetric_of_chartwiseRealization
        rt D K u₀ Phi DPhi anchor hz₀ hrealize
  · exact Filter.Eventually.of_forall fun _ ↦ rfl
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Slotwise form of
`reconstructedInverseGaugeMetric_form_eventuallyEq_chartMetric_of_chartwiseRealization`,
in the quantifier order used by the interior Hamilton assembly theorem. -/
theorem reconstructedInverseGaugeMetric_eventuallyEq_chartMetric_of_chartwiseRealization
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (anchor : M) {t : ℝ} {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi s anchor z) :
    ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        (D anchor) K (u₀ anchor)
        (fun tau : ℝ ↦ Phi anchor tau z₀)
        (fun tau : ℝ ↦ DPhi anchor tau z₀) s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀ p q) := by
  have hform :=
    reconstructedInverseGaugeMetric_form_eventuallyEq_chartMetric_of_chartwiseRealization
      rt D K u₀ Phi DPhi anchor (t := t) (z₀ := z₀) hz₀ hrealize
  intro p q
  filter_upwards [hform] with s hs
  exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B p q) hs

end Poincare
