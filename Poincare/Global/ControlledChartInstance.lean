import Poincare.Global.RiemannianContext
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Uniformly controlled preferred charts

A finite subcover of the original chart sources supplies a Lebesgue number.
Selecting one of these charts at each anchor gives a uniform source ball.
The charts themselves are unchanged; only the atlas and preferred selection
are replaced. This controls source membership, not joint smoothness of the
selection or of the exponential maps built from it.

The metric section uses the topology bundled in `MetricSpace`. The final
compatible-metric theorem retains a separately supplied topology explicitly.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare.ControlledChartInstance

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

section Metric

variable {M : Type u} [MetricSpace M] [ChartedSpace E M] [CompactSpace M]

/-- A finite family of original preferred charts contains a uniform ball
around every point, including when the manifold is empty. -/
theorem exists_finite_uniform_chart_cover :
    ∃ (s : Finset M) (δ : ℝ), 0 < δ ∧
      ∀ x : M, ∃ i : s, ball x δ ⊆ (chartAt E (i : M)).source := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (chartAt E x).source) (fun x ↦ (chartAt E x).open_source)
    (by intro x _; exact mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  have hcover : (univ : Set M) ⊆ ⋃ i : s, (chartAt E (i : M)).source := by
    simpa only [iUnion_subtype] using hs
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i : s ↦ (chartAt E (i : M)).open_source) hcover
  exact ⟨s, δ, hδ, fun x ↦ hballs x (mem_univ x)⟩

end Metric

end Poincare.ControlledChartInstance
