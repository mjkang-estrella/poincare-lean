import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Finite topological-atlas reduction on compact three-manifolds

An ambient topological `ChartedSpace` already supplies an actual preferred
chart `chartAt` around every point.  On a compact space, the open cover by
their sources has a finite subcover.  This file packages precisely that
finite topological datum.

No smoothing statement is made.  The coordinate changes below are only
open partial homeomorphisms between Euclidean chart targets; no
differentiability or recognition property is asserted.
-/

noncomputable section

open Set
open scoped Topology

namespace Poincare
namespace SmoothabilityFiniteTopologicalAtlasReduction

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E₃ M]

/-- A proof-bearing finite subatlas made only from the ambient preferred
charts.  `centers` is finite by construction, and `source_cover` records that
their actual `chartAt` sources cover all of `M`. -/
structure FiniteTopologicalChartAtAtlas3 (M : Type u)
    [TopologicalSpace M] [ChartedSpace E₃ M] where
  centers : Finset M
  source_cover :
    Set.univ ⊆ ⋃ x ∈ centers, (chartAt E₃ x).source

namespace FiniteTopologicalChartAtAtlas3

/-- The finite index type carried by the selected center finset. -/
abbrev Index (data : FiniteTopologicalChartAtAtlas3 M) := ↑data.centers

/-- Every selected chart is definitionally an actual preferred ambient
`chartAt`, rather than an independently supplied local homeomorphism. -/
def chart (data : FiniteTopologicalChartAtAtlas3 M) (i : data.Index) :
    OpenPartialHomeomorph M E₃ :=
  chartAt E₃ (i : M)

@[simp]
theorem chart_eq_chartAt
    (data : FiniteTopologicalChartAtAtlas3 M) (i : data.Index) :
    data.chart i = chartAt E₃ (i : M) :=
  rfl

/-- The selected preferred chart remains a member of the ambient atlas. -/
theorem chart_mem_ambient_atlas
    (data : FiniteTopologicalChartAtAtlas3 M) (i : data.Index) :
    data.chart i ∈ atlas E₃ M :=
  chart_mem_atlas E₃ (i : M)

/-- Every selected chart source is open. -/
theorem isOpen_chart_source
    (data : FiniteTopologicalChartAtAtlas3 M) (i : data.Index) :
    IsOpen (data.chart i).source :=
  (data.chart i).open_source

/-- The chosen center belongs to its selected chart source. -/
@[simp]
theorem center_mem_chart_source
    (data : FiniteTopologicalChartAtAtlas3 M) (i : data.Index) :
    (i : M) ∈ (data.chart i).source :=
  mem_chart_source E₃ (i : M)

/-- Every point lies in the source of one chart indexed by the finite
selected-center type. -/
theorem exists_mem_chart_source
    (data : FiniteTopologicalChartAtAtlas3 M) (x : M) :
    ∃ i : data.Index, x ∈ (data.chart i).source := by
  have hx := data.source_cover (Set.mem_univ x)
  rcases Set.mem_iUnion.1 hx with ⟨center, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hcenter, hxsource⟩
  exact ⟨⟨center, hcenter⟩, hxsource⟩

/-- The sources of the finitely indexed selected charts cover `M`. -/
@[simp]
theorem iUnion_chart_source
    (data : FiniteTopologicalChartAtAtlas3 M) :
    (⋃ i : data.Index, (data.chart i).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := data.exists_mem_chart_source x
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- The topological overlap of two selected chart sources. -/
def overlap (data : FiniteTopologicalChartAtAtlas3 M)
    (i j : data.Index) : Set M :=
  (data.chart i).source ∩ (data.chart j).source

/-- Selected chart overlaps are open. -/
theorem isOpen_overlap
    (data : FiniteTopologicalChartAtAtlas3 M) (i j : data.Index) :
    IsOpen (data.overlap i j) :=
  (data.isOpen_chart_source i).inter (data.isOpen_chart_source j)

/-- The topological coordinate change from chart `i` to chart `j`, defined
on the actual overlap portion of the first chart target. -/
def transition (data : FiniteTopologicalChartAtAtlas3 M)
    (i j : data.Index) : OpenPartialHomeomorph E₃ E₃ :=
  (data.chart i).symm.trans (data.chart j)

/-- The transition source is exactly the part of chart `i`'s target whose
inverse image lies in chart `j`'s source. -/
theorem transition_source
    (data : FiniteTopologicalChartAtAtlas3 M) (i j : data.Index) :
    (data.transition i j).source =
      (data.chart i).target ∩
        (data.chart i).symm ⁻¹' (data.chart j).source := by
  exact OpenPartialHomeomorph.trans_source _ _

/-- A manifold point in both selected sources gives a point in the source of
the corresponding coordinate transition. -/
theorem chart_image_mem_transition_source
    (data : FiniteTopologicalChartAtAtlas3 M) (i j : data.Index)
    {x : M} (hxi : x ∈ (data.chart i).source)
    (hxj : x ∈ (data.chart j).source) :
    data.chart i x ∈ (data.transition i j).source := by
  rw [data.transition_source i j]
  refine ⟨(data.chart i).map_source hxi, ?_⟩
  change (data.chart i).symm (data.chart i x) ∈ (data.chart j).source
  rw [(data.chart i).left_inv hxi]
  exact hxj

/-- On an overlap, the transition sends the `i`-coordinate of a point to its
`j`-coordinate. -/
theorem transition_chart_apply
    (data : FiniteTopologicalChartAtAtlas3 M) (i j : data.Index)
    {x : M} (hxi : x ∈ (data.chart i).source) :
    data.transition i j (data.chart i x) = data.chart j x := by
  rw [transition, OpenPartialHomeomorph.trans_apply,
    (data.chart i).left_inv hxi]

end FiniteTopologicalChartAtAtlas3

/-- Compactness extracts a finite subcover from the open cover by preferred
ambient chart sources. -/
theorem exists_finiteTopologicalChartAtAtlas3
    [CompactSpace M] :
    Nonempty (FiniteTopologicalChartAtAtlas3 M) := by
  obtain ⟨centers, hcover⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : M ↦ (chartAt E₃ x).source)
      (fun x ↦ (chartAt E₃ x).open_source) (by
        intro x _hx
        exact Set.mem_iUnion.2 ⟨x, mem_chart_source E₃ x⟩)
  exact ⟨⟨centers, hcover⟩⟩

end SmoothabilityFiniteTopologicalAtlasReduction
end Poincare
