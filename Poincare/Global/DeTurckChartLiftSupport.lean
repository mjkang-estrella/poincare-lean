import Poincare.Global.DeTurckChartLiftDefinitions

noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckChartLift

/-- The true coefficient support transports to a compact set in the chart
source, containing the closed nonzero locus of the actual tangent tensor.
The tensor vanishes on a neighborhood of each point outside that set. -/
theorem compact_source_support
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (anchor : M) (F : E → Bilin)
    (hcompact : HasCompactSupport F)
    (htarget : tsupport F ⊆ (extChartAt I anchor).target) :
    IsCompact (sourceSupport anchor F) ∧
      sourceSupport anchor F ⊆ (extChartAt I anchor).source ∧
      (∀ x : M, x ∉ sourceSupport anchor F → chartLift anchor F x = 0) ∧
      IsCompact (closure {x : M | chartLift anchor F x ≠ 0}) ∧
      closure {x : M | chartLift anchor F x ≠ 0} ⊆ sourceSupport anchor F ∧
      ∀ x : M, x ∉ sourceSupport anchor F →
        Filter.Eventually (fun y => chartLift anchor F y = 0) (nhds x) := by
  classical
  have hK : IsCompact (sourceSupport anchor F) :=
    hcompact.image_of_continuousOn
      ((continuousOn_extChartAt_symm anchor).mono htarget)
  have hsource : sourceSupport anchor F ⊆ (extChartAt I anchor).source := by
    rintro x ⟨z, hz, rfl⟩
    exact (extChartAt I anchor).map_target (htarget hz)
  have hzero : ∀ x : M, x ∉ sourceSupport anchor F → chartLift anchor F x = 0 := by
    intro x hx
    by_cases hxs : x ∈ (extChartAt I anchor).source
    · have hcx : extChartAt I anchor x ∉ tsupport F := by
        intro hcx
        apply hx
        exact ⟨extChartAt I anchor x, hcx, (extChartAt I anchor).left_inv hxs⟩
      have hFzero : F (extChartAt I anchor x) = 0 :=
        image_eq_zero_of_notMem_tsupport hcx
      simp only [chartLift, if_pos hxs]
      rw [localPullback, hFzero]
      ext v w
      rfl
    · simp only [chartLift, if_neg hxs]
  have hclosed : IsClosed (sourceSupport anchor F) := hK.isClosed
  have hnonzero : {x : M | chartLift anchor F x ≠ 0} ⊆ sourceSupport anchor F := by
    intro x hx
    by_contra hnot
    exact hx (hzero x hnot)
  have hclosure : closure {x : M | chartLift anchor F x ≠ 0} ⊆
      sourceSupport anchor F := closure_minimal hnonzero hclosed
  refine ⟨hK, hsource, hzero, hK.of_isClosed_subset isClosed_closure hclosure,
    hclosure, ?_⟩
  intro x hx
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  exact hzero y hy

end Poincare.DeTurckChartLift
