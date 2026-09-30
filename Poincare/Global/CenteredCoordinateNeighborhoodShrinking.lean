import Poincare.Global.RiemannianContext
import Mathlib.Topology.Separation.Regular

/-!
# Centered coordinate neighborhood shrinking

Compact Hausdorff normality shrinks a coordinate neighborhood around its
chart anchor. The closed manifold region stays in the genuine chart source,
so its coordinate image is compact and lies in the prescribed neighborhood.
-/

set_option autoImplicit false

open Set
open scoped Manifold

universe u

namespace Poincare.CenteredCoordinateNeighborhoodShrinking

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]

/-- Every open coordinate neighborhood of the anchor contains the compact
coordinate image of a smaller open manifold neighborhood's closure. -/
theorem exists_centered_chart_shrinking
    (p : M) (V : Set (ClosedSmoothModel 3)) (hV : IsOpen V)
    (hpV : extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p p ∈ V) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      closure U ⊆ (extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p).source ∧
      IsCompact ((extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p) ''
        closure U) ∧
      (extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p) '' closure U ⊆ V := by
  let W : Set M :=
    (extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p).source ∩
      extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p ⁻¹' V
  have hW : IsOpen W := isOpen_extChartAt_preimage' p hV
  have hpW : p ∈ W := ⟨mem_extChartAt_source p, hpV⟩
  obtain ⟨U, hU, hpU, hUW⟩ := normal_exists_closure_subset
    (isClosed_singleton : IsClosed ({p} : Set M)) hW (singleton_subset_iff.mpr hpW)
  have hsource : closure U ⊆
      (extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p).source :=
    hUW.trans inter_subset_left
  refine ⟨U, hU, hpU (mem_singleton p), hsource, ?_, ?_⟩
  · exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt p).mono hsource)
  · exact image_subset_iff.mpr fun x hx => (hUW hx).2

end Poincare.CenteredCoordinateNeighborhoodShrinking
