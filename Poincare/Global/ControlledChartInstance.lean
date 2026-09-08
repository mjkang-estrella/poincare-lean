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

section SmoothStructure

variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]

/-- Any charted atlas contained in the original smooth maximal atlas defines
a smooth structure with exactly that maximal atlas. -/
theorem isManifold_and_maximalAtlas_eq
    (inst' : ChartedSpace E M)
    (h : inst'.atlas ⊆ @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I)) :
    (letI := inst'; IsManifold I ∞ M) ∧
      @StructureGroupoid.maximalAtlas E M _ _ inst' (contDiffGroupoid ∞ I) =
        @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I) := by
  letI := inst
  have hcompat : ∀ {e e' : OpenPartialHomeomorph M E},
      e ∈ inst'.atlas → e' ∈ inst'.atlas → e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
    fun he he' ↦ StructureGroupoid.compatible_of_mem_maximalAtlas (h he) (h he')
  have hsmooth : letI := inst'; IsManifold I ∞ M := by
    letI := inst'
    exact { compatible := hcompat }
  refine ⟨hsmooth, ?_⟩
  have hold : @StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I) ⊆
      @StructureGroupoid.maximalAtlas E M _ _ inst' (contDiffGroupoid ∞ I) := by
    intro e he e' he'
    exact ⟨StructureGroupoid.compatible_of_mem_maximalAtlas he (h he'),
      StructureGroupoid.compatible_of_mem_maximalAtlas (h he') he⟩
  apply Subset.antisymm _ hold
  intro e he e' he'
  -- An original atlas chart is compatible with every original atlas chart:
  -- obtain this from the covering new atlas and compatibility with its members.
  have he'new : e' ∈
      @StructureGroupoid.maximalAtlas E M _ _ inst' (contDiffGroupoid ∞ I) := by
    intro c hc
    exact ⟨(h hc e' he').2, (h hc e' he').1⟩
  letI := inst'
  exact ⟨StructureGroupoid.compatible_of_mem_maximalAtlas he he'new,
    StructureGroupoid.compatible_of_mem_maximalAtlas he'new he⟩

end SmoothStructure

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

omit [CompactSpace M] in
/-- Select an original chart containing the supplied uniform ball. The new
atlas is precisely the image of the finite family, not the maximal atlas. -/
@[implicit_reducible]
def chartedSpaceOfCover (s : Finset M) (δ : ℝ) (hδ : 0 < δ)
    (hballs : ∀ x : M, ∃ i : s, ball x δ ⊆ (chartAt E (i : M)).source) :
    ChartedSpace E M where
  atlas := (chartAt E) '' (s : Set M)
  chartAt x := chartAt E (Classical.choose (hballs x)).val
  mem_chart_source x := Classical.choose_spec (hballs x) (mem_ball_self hδ)
  chart_mem_atlas x := ⟨_, (Classical.choose (hballs x)).property, rfl⟩

omit [CompactSpace M] in
theorem chartedSpaceOfCover_ball_subset (s : Finset M) (δ : ℝ) (hδ : 0 < δ)
    (hballs : ∀ x : M, ∃ i : s, ball x δ ⊆ (chartAt E (i : M)).source) (x : M) :
    ball x δ ⊆ (@chartAt E _ M _ (chartedSpaceOfCover s δ hδ hballs) x).source :=
  Classical.choose_spec (hballs x)

end Metric

end Poincare.ControlledChartInstance
