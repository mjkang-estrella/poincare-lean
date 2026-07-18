import Poincare.Global.SmoothabilityFinitePrecompactTopologicalAtlasReduction

/-!
# Finite atlas-nerve and transition reduction

A finite precompact preferred-chart atlas has only finitely many ordered
pairs of inner domains with nonempty overlap.  For every such pair, the
closure of the overlap is compact and lies in both actual chart sources.
Consequently its image in the first chart is a compact set contained in the
source of the genuine topological coordinate transition to the second chart.

The final package records exactly these finitely many compact transition
domains and open partial homeomorphisms.  It makes no differentiability,
smoothing, triangulation, or manifold-recognition claim.
-/

noncomputable section

open Set
open scoped Topology

namespace Poincare
namespace SmoothabilityFiniteAtlasNerveReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

abbrev PrecompactAtlas3 :=
  SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3

end SmoothabilityFiniteAtlasNerveReduction

namespace SmoothabilityFinitePrecompactTopologicalAtlasReduction
namespace FinitePrecompactTopologicalChartAtAtlas3

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

variable
  (data : SmoothabilityFiniteAtlasNerveReduction.PrecompactAtlas3 M)

/-- The actual overlap of two selected inner chart domains. -/
def overlap (i j : data.Index) : Set M :=
  data.innerDomain i ∩ data.innerDomain j

/-- The one-dimensional nerve relation: two ordered vertices are related
exactly when their selected inner domains overlap. -/
def NerveRel (i j : data.Index) : Prop :=
  (data.overlap i j).Nonempty

@[simp]
theorem nerveRel_iff (i j : data.Index) :
    data.NerveRel i j ↔ (data.innerDomain i ∩ data.innerDomain j).Nonempty :=
  Iff.rfl

/-- Every selected chart vertex is related to itself because its center lies
in its inner domain. -/
theorem nerveRel_refl (i : data.Index) : data.NerveRel i i := by
  exact ⟨(i : M), data.center_mem_innerDomain i,
    data.center_mem_innerDomain i⟩

/-- The overlap relation is symmetric, although ordered pairs are retained
because coordinate transitions have a direction. -/
theorem nerveRel_symm {i j : data.Index} :
    data.NerveRel i j → data.NerveRel j i := by
  rintro ⟨x, hxi, hxj⟩
  exact ⟨x, hxj, hxi⟩

/-- The finite set of ordered chart pairs with nonempty inner-domain
overlap. -/
noncomputable def orderedOverlapPairs :
    Finset (data.Index × data.Index) := by
  classical
  exact Finset.univ.filter fun p ↦ data.NerveRel p.1 p.2

@[simp]
theorem mem_orderedOverlapPairs (p : data.Index × data.Index) :
    p ∈ data.orderedOverlapPairs ↔ data.NerveRel p.1 p.2 := by
  classical
  simp [orderedOverlapPairs]

/-- Every actual nonempty selected overlap is represented by the ordered
pair finset. -/
theorem orderedPair_mem_of_overlap_nonempty (i j : data.Index)
    (h : (data.overlap i j).Nonempty) :
    (i, j) ∈ data.orderedOverlapPairs :=
  (data.mem_orderedOverlapPairs (i, j)).2 h

/-- Conversely, every represented ordered pair has an actual nonempty
inner-domain overlap. -/
theorem overlap_nonempty_of_orderedPair_mem (i j : data.Index)
    (h : (i, j) ∈ data.orderedOverlapPairs) :
    (data.overlap i j).Nonempty :=
  (data.mem_orderedOverlapPairs (i, j)).1 h

/-- The relation cut out by nonempty overlap is precisely the coercion of
the finite ordered-pair set. -/
theorem coe_orderedOverlapPairs :
    (↑data.orderedOverlapPairs : Set (data.Index × data.Index)) =
      {p | data.NerveRel p.1 p.2} := by
  classical
  ext p
  simp

/-- In particular, the adjacency relation has finite support. -/
theorem finite_nerveRelation :
    Set.Finite {p : data.Index × data.Index |
      data.NerveRel p.1 p.2} := by
  rw [← data.coe_orderedOverlapPairs]
  exact data.orderedOverlapPairs.finite_toSet

/-- The closure of an overlap remains in the source of its first actual
preferred chart. -/
theorem closure_overlap_subset_left_chart_source (i j : data.Index) :
    closure (data.overlap i j) ⊆ (data.chart i).source :=
  Subset.trans (closure_mono inter_subset_left)
    (data.closure_innerDomain_subset_chart_source i)

/-- The closure of an overlap remains in the source of its second actual
preferred chart. -/
theorem closure_overlap_subset_right_chart_source (i j : data.Index) :
    closure (data.overlap i j) ⊆ (data.chart j).source :=
  Subset.trans (closure_mono inter_subset_right)
    (data.closure_innerDomain_subset_chart_source j)

/-- Every selected overlap has compact closure. -/
theorem isCompact_closure_overlap (i j : data.Index) :
    IsCompact (closure (data.overlap i j)) :=
  isClosed_closure.isCompact

/-- The compact coordinate transition domain associated to an ordered
overlap, expressed in the first chart. -/
def overlapCoordinateImage (i j : data.Index) : Set E₃ :=
  data.chart i '' closure (data.overlap i j)

/-- Each overlap-coordinate image is compact. -/
theorem isCompact_overlapCoordinateImage (i j : data.Index) :
    IsCompact (data.overlapCoordinateImage i j) := by
  exact (data.isCompact_closure_overlap i j).image_of_continuousOn
    ((data.chart i).continuousOn.mono
      (data.closure_overlap_subset_left_chart_source i j))

/-- Each overlap-coordinate image is a closed Euclidean set. -/
theorem isClosed_overlapCoordinateImage (i j : data.Index) :
    IsClosed (data.overlapCoordinateImage i j) :=
  (data.isCompact_overlapCoordinateImage i j).isClosed

/-- A represented overlap has a nonempty compact coordinate image. -/
theorem overlapCoordinateImage_nonempty {i j : data.Index}
    (h : data.NerveRel i j) :
    (data.overlapCoordinateImage i j).Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨data.chart i x, x, subset_closure hx, rfl⟩

/-- The actual topological coordinate change from the first selected chart
to the second. -/
def transition (i j : data.Index) : OpenPartialHomeomorph E₃ E₃ :=
  (data.chart i).symm.trans (data.chart j)

/-- The source of the actual coordinate transition. -/
theorem transition_source (i j : data.Index) :
    (data.transition i j).source =
      (data.chart i).target ∩
        (data.chart i).symm ⁻¹' (data.chart j).source := by
  exact OpenPartialHomeomorph.trans_source _ _

/-- The compact coordinate image of an overlap lies inside the source of
the corresponding actual topological chart transition. -/
theorem overlapCoordinateImage_subset_transition_source
    (i j : data.Index) :
    data.overlapCoordinateImage i j ⊆ (data.transition i j).source := by
  rintro _ ⟨x, hx, rfl⟩
  rw [data.transition_source i j]
  have hxi := data.closure_overlap_subset_left_chart_source i j hx
  have hxj := data.closure_overlap_subset_right_chart_source i j hx
  refine ⟨(data.chart i).map_source hxi, ?_⟩
  change (data.chart i).symm (data.chart i x) ∈ (data.chart j).source
  rw [(data.chart i).left_inv hxi]
  exact hxj

/-- On the compact overlap closure, the transition sends first-chart
coordinates to second-chart coordinates. -/
theorem transition_chart_apply_on_overlapClosure (i j : data.Index)
    {x : M} (hx : x ∈ closure (data.overlap i j)) :
    data.transition i j (data.chart i x) = data.chart j x := by
  rw [transition, OpenPartialHomeomorph.trans_apply,
    (data.chart i).left_inv
      (data.closure_overlap_subset_left_chart_source i j hx)]

end FinitePrecompactTopologicalChartAtAtlas3
end SmoothabilityFinitePrecompactTopologicalAtlasReduction

namespace SmoothabilityFiniteAtlasNerveReduction

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

/-- A proof-bearing finite family of compact transition domains and actual
topological coordinate changes for a fixed finite precompact atlas. -/
structure FiniteAtlasNerveTransitionPackage3 (data : PrecompactAtlas3 M) where
  orderedPairs : Finset (data.Index × data.Index)
  pair_mem_iff : ∀ p, p ∈ orderedPairs ↔ data.NerveRel p.1 p.2
  transitionDomain : ↑orderedPairs → Set E₃
  transitionMap : ↑orderedPairs → OpenPartialHomeomorph E₃ E₃
  transitionDomain_eq : ∀ p,
    transitionDomain p =
      data.overlapCoordinateImage (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2
  transitionMap_eq : ∀ p,
    transitionMap p =
      data.transition (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2
  isCompact_transitionDomain : ∀ p, IsCompact (transitionDomain p)
  transitionDomain_subset_source : ∀ p,
    transitionDomain p ⊆ (transitionMap p).source
  transition_agrees_on_overlapClosure : ∀ (p : ↑orderedPairs) (x : M),
    x ∈ closure
      (data.overlap (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2) →
    transitionMap p
        (data.chart (p : data.Index × data.Index).1 x) =
      data.chart (p : data.Index × data.Index).2 x

/-- The canonical finite transition package attached to a precompact
preferred-chart atlas. -/
noncomputable def canonicalTransitionPackage
    (data : PrecompactAtlas3 M) :
    FiniteAtlasNerveTransitionPackage3 data := by
  classical
  exact {
    orderedPairs := data.orderedOverlapPairs
    pair_mem_iff := data.mem_orderedOverlapPairs
    transitionDomain := fun p ↦
      data.overlapCoordinateImage p.1.1 p.1.2
    transitionMap := fun p ↦ data.transition p.1.1 p.1.2
    transitionDomain_eq := fun _ ↦ rfl
    transitionMap_eq := fun _ ↦ rfl
    isCompact_transitionDomain := fun p ↦
      data.isCompact_overlapCoordinateImage p.1.1 p.1.2
    transitionDomain_subset_source := fun p ↦
      data.overlapCoordinateImage_subset_transition_source p.1.1 p.1.2
    transition_agrees_on_overlapClosure := fun p x hx ↦
      data.transition_chart_apply_on_overlapClosure p.1.1 p.1.2 hx
  }

/-- The full finite nerve reduction pairs the precompact atlas with its
canonical proof-bearing transition package. -/
structure FiniteAtlasNerveReduction3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace E₃ M] where
  atlas : PrecompactAtlas3 M
  transitions : FiniteAtlasNerveTransitionPackage3 atlas

/-- Every compact Hausdorff topological three-charted space admits the finite
atlas-nerve transition reduction. -/
theorem exists_finiteAtlasNerveReduction3 :
    Nonempty (FiniteAtlasNerveReduction3 M) := by
  obtain ⟨data⟩ :=
    SmoothabilityFinitePrecompactTopologicalAtlasReduction.exists_finitePrecompactTopologicalChartAtAtlas3
      (M := M)
  exact ⟨⟨data, canonicalTransitionPackage data⟩⟩

end SmoothabilityFiniteAtlasNerveReduction
end Poincare
