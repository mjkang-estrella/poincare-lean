import Poincare.Global.SmoothabilityFiniteTopologicalAtlasReduction
import Mathlib.Topology.ShrinkingLemma

/-!
# Finite precompact topological-atlas reduction

On a compact Hausdorff space, normality shrinks the preferred topological
chart around each point to an open neighborhood whose closure remains in the
source of that actual `chartAt`.  Compactness then extracts finitely many of
these inner domains while preserving their chosen chart centers.

This is only a topological reduction.  In particular, no smoothing,
differentiability, or manifold-recognition statement is asserted.
-/

noncomputable section

open Set
open scoped Topology

namespace Poincare
namespace SmoothabilityFinitePrecompactTopologicalAtlasReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace E₃ M]

/-- A finite family of actual preferred charts equipped with centered open
inner domains whose closures remain inside their respective chart sources.
The inner domains, rather than merely the larger chart sources, cover `M`. -/
structure FinitePrecompactTopologicalChartAtAtlas3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace E₃ M] where
  centers : Finset M
  innerDomain : ↑centers → Set M
  isOpen_innerDomain : ∀ i, IsOpen (innerDomain i)
  center_mem_innerDomain : ∀ i, (i : M) ∈ innerDomain i
  closure_innerDomain_subset_chart_source :
    ∀ i, closure (innerDomain i) ⊆ (chartAt E₃ (i : M)).source
  innerDomain_cover : (⋃ i, innerDomain i) = Set.univ

namespace FinitePrecompactTopologicalChartAtAtlas3

/-- The finite type indexing the selected centered domains. -/
abbrev Index (data : FinitePrecompactTopologicalChartAtAtlas3 M) :=
  ↑data.centers

/-- The preferred ambient chart attached to a selected center. -/
def chart (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) : OpenPartialHomeomorph M E₃ :=
  chartAt E₃ (i : M)

@[simp]
theorem chart_eq_chartAt
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    data.chart i = chartAt E₃ (i : M) :=
  rfl

/-- Every selected inner domain is contained in the source of its actual
preferred chart. -/
theorem innerDomain_subset_chart_source
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    data.innerDomain i ⊆ (data.chart i).source :=
  Subset.trans subset_closure
    (data.closure_innerDomain_subset_chart_source i)

/-- Every selected inner-domain closure is compact. -/
theorem isCompact_closure_innerDomain
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    IsCompact (closure (data.innerDomain i)) :=
  isClosed_closure.isCompact

/-- The compact coordinate set obtained by mapping an inner-domain closure
through its actual preferred chart. -/
def compactCoordinateImage
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) : Set E₃ :=
  data.chart i '' closure (data.innerDomain i)

/-- The coordinate image of every selected inner-domain closure is compact. -/
theorem isCompact_compactCoordinateImage
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    IsCompact (data.compactCoordinateImage i) := by
  exact (data.isCompact_closure_innerDomain i).image_of_continuousOn
    ((data.chart i).continuousOn.mono
      (data.closure_innerDomain_subset_chart_source i))

/-- Each compact coordinate image lies in the target of its preferred chart. -/
theorem compactCoordinateImage_subset_chart_target
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    data.compactCoordinateImage i ⊆ (data.chart i).target := by
  rintro _ ⟨x, hx, rfl⟩
  exact (data.chart i).map_source
    (data.closure_innerDomain_subset_chart_source i hx)

/-- In Euclidean coordinates, each compact coordinate image is closed. -/
theorem isClosed_compactCoordinateImage
    (data : FinitePrecompactTopologicalChartAtAtlas3 M)
    (i : data.Index) :
    IsClosed (data.compactCoordinateImage i) :=
  (data.isCompact_compactCoordinateImage i).isClosed

/-- Forgetting the inner domains gives the finite preferred-chart source
cover constructed in the preceding topological reduction. -/
def toFiniteTopologicalChartAtAtlas3
    (data : FinitePrecompactTopologicalChartAtAtlas3 M) :
    SmoothabilityFiniteTopologicalAtlasReduction.FiniteTopologicalChartAtAtlas3 M where
  centers := data.centers
  source_cover := by
    intro x _hx
    have hx : x ∈ ⋃ i : data.Index, data.innerDomain i := by
      rw [data.innerDomain_cover]
      exact Set.mem_univ x
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    exact Set.mem_iUnion.2 ⟨(i : M), Set.mem_iUnion.2 ⟨i.property,
      data.innerDomain_subset_chart_source i hxi⟩⟩

end FinitePrecompactTopologicalChartAtAtlas3

/-- Compact Hausdorff normality first supplies a centered open shrinking of
every preferred chart source, and compactness then selects finitely many of
those shrinkings that still cover the whole space. -/
theorem exists_finitePrecompactTopologicalChartAtAtlas3 :
    Nonempty (FinitePrecompactTopologicalChartAtAtlas3 M) := by
  have hshrinking : ∀ x : M, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧ closure U ⊆ (chartAt E₃ x).source := by
    intro x
    obtain ⟨U, hUopen, hxU, hUclosure⟩ :=
      normal_exists_closure_subset (isClosed_singleton : IsClosed ({x} : Set M))
        (chartAt E₃ x).open_source
        (Set.singleton_subset_iff.2 (mem_chart_source E₃ x))
    exact ⟨U, hUopen, hxU (Set.mem_singleton x), hUclosure⟩
  choose U hUopen hxU hUclosure using hshrinking
  obtain ⟨centers, hcover⟩ :=
    isCompact_univ.elim_finite_subcover U hUopen (by
      intro x _hx
      exact Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨{
    centers := centers
    innerDomain := fun i ↦ U (i : M)
    isOpen_innerDomain := fun i ↦ hUopen (i : M)
    center_mem_innerDomain := fun i ↦ hxU (i : M)
    closure_innerDomain_subset_chart_source := fun i ↦ hUclosure (i : M)
    innerDomain_cover := ?_
  }⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx := hcover (Set.mem_univ x)
  rcases Set.mem_iUnion.1 hx with ⟨center, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hcenter, hxUcenter⟩
  exact Set.mem_iUnion.2 ⟨⟨center, hcenter⟩, hxUcenter⟩

end SmoothabilityFinitePrecompactTopologicalAtlasReduction
end Poincare
