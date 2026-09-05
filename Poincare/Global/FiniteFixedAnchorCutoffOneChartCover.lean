import Mathlib.Topology.ShrinkingLemma
import Poincare.Global.MetricFamilyCovRicciNormContinuity

/-!
# Finite fixed-anchor cutoff-one chart covers

On a compact Hausdorff manifold, the cutoff-one germ around each preferred
chart anchor pulls back to an open manifold neighborhood. Normality shrinks
these neighborhoods, and compactness selects finitely many whose inner
domains still cover the manifold.

The anchors are fixed once and for all. This avoids asking the scalar-profile
topology to control chart expressions jointly in a moving anchor, a continuity
property that topology does not provide.
-/

noncomputable section

open Bundle Filter Function Set
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The part of the preferred chart source on which the fixed anchor's
blending cutoff is locally equal to one. -/
def fixedAnchorCutoffOneChartNeighborhood (x : M) : Set M :=
  (extChartAt I x).source ∩
    (extChartAt I x) ⁻¹' {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}

omit [T2Space M] [CompactSpace M] in
/-- The fixed-anchor cutoff-one chart neighborhood is open. -/
theorem isOpen_fixedAnchorCutoffOneChartNeighborhood (x : M) :
    IsOpen (fixedAnchorCutoffOneChartNeighborhood (n := n) x) := by
  exact isOpen_extChartAt_preimage' x isOpen_setOf_eventually_nhds

omit [T2Space M] [CompactSpace M] in
/-- The anchor belongs to its fixed-anchor cutoff-one chart neighborhood. -/
theorem self_mem_fixedAnchorCutoffOneChartNeighborhood (x : M) :
    x ∈ fixedAnchorCutoffOneChartNeighborhood (n := n) x := by
  refine ⟨mem_extChartAt_source x, ?_⟩
  exact GeodesicTransport.cutoff_eventuallyEq_one (n := n) x

/-- A finite family of fixed preferred-chart anchors with precompact open
inner domains. Each inner-domain closure stays where the anchor chart is
valid and the anchor cutoff is locally one. Fixing finitely many anchors
avoids any need for joint continuity in the anchor variable. -/
structure FiniteFixedAnchorCutoffOneChartCover
    (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M] where
  anchors : Finset M
  innerDomain : ↑anchors → Set M
  isOpen_innerDomain : ∀ i, IsOpen (innerDomain i)
  anchor_mem_innerDomain : ∀ i, (i : M) ∈ innerDomain i
  closure_innerDomain_subset_cutoffOneChartNeighborhood :
    ∀ i, closure (innerDomain i) ⊆
      fixedAnchorCutoffOneChartNeighborhood (n := n) (i : M)
  innerDomain_cover : (⋃ i, innerDomain i) = Set.univ

/-- Compact Hausdorff normality shrinks every fixed-anchor cutoff-one
neighborhood, after which compactness extracts a finite subcover. -/
theorem exists_finiteFixedAnchorCutoffOneChartCover :
    Nonempty (FiniteFixedAnchorCutoffOneChartCover n M) := by
  have hshrinking : ∀ x : M, ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧
        closure U ⊆ fixedAnchorCutoffOneChartNeighborhood (n := n) x := by
    intro x
    obtain ⟨U, hUopen, hxU, hUclosure⟩ :=
      normal_exists_closure_subset
        (isClosed_singleton : IsClosed ({x} : Set M))
        (isOpen_fixedAnchorCutoffOneChartNeighborhood (n := n) x)
        (Set.singleton_subset_iff.2
          (self_mem_fixedAnchorCutoffOneChartNeighborhood (n := n) x))
    exact ⟨U, hUopen, hxU (Set.mem_singleton x), hUclosure⟩
  choose U hUopen hxU hUclosure using hshrinking
  obtain ⟨anchors, hcover⟩ :=
    isCompact_univ.elim_finite_subcover U hUopen (by
      intro x _hx
      exact Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨{
    anchors := anchors
    innerDomain := fun i ↦ U (i : M)
    isOpen_innerDomain := fun i ↦ hUopen (i : M)
    anchor_mem_innerDomain := fun i ↦ hxU (i : M)
    closure_innerDomain_subset_cutoffOneChartNeighborhood :=
      fun i ↦ hUclosure (i : M)
    innerDomain_cover := ?_
  }⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx := hcover (Set.mem_univ x)
  rcases Set.mem_iUnion.1 hx with ⟨anchor, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨hanchor, hxUanchor⟩
  exact Set.mem_iUnion.2 ⟨⟨anchor, hanchor⟩, hxUanchor⟩

namespace FiniteFixedAnchorCutoffOneChartCover

/-- The finite type indexing the selected fixed anchors. -/
abbrev Index (data : FiniteFixedAnchorCutoffOneChartCover n M) :=
  ↑data.anchors

/-- The compact coordinate image of one inner-domain closure. -/
def compactCoordinateSet
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) : Set E :=
  extChartAt I (i : M) '' closure (data.innerDomain i)

/-- Every selected inner-domain closure is compact. -/
theorem isCompact_closure_innerDomain
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    IsCompact (closure (data.innerDomain i)) :=
  isClosed_closure.isCompact

/-- Each compact coordinate set is compact. -/
theorem isCompact_compactCoordinateSet
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    IsCompact (data.compactCoordinateSet i) := by
  exact (data.isCompact_closure_innerDomain i).image_of_continuousOn
    ((continuousOn_extChartAt (i : M)).mono (fun y hy ↦
      (data.closure_innerDomain_subset_cutoffOneChartNeighborhood i hy).1))

/-- Each compact coordinate set lies in its fixed anchor's chart target. -/
theorem compactCoordinateSet_subset_chart_target
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    data.compactCoordinateSet i ⊆ (extChartAt I (i : M)).target := by
  rintro z ⟨y, hy, rfl⟩
  exact (extChartAt I (i : M)).map_source
    (data.closure_innerDomain_subset_cutoffOneChartNeighborhood i hy).1

/-- Every point of a compact coordinate set lies in the fixed anchor's
cutoff-one germ locus. -/
theorem compactCoordinateSet_subset_cutoffOneGermLocus
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (i : data.Index) :
    data.compactCoordinateSet i ⊆
      {z | ∀ᶠ z' in nhds z,
        GeodesicTransport.cutoff (n := n) (i : M) z' = 1} := by
  rintro z ⟨y, hy, rfl⟩
  exact (data.closure_innerDomain_subset_cutoffOneChartNeighborhood i hy).2

/-- Every manifold point has a selected fixed chart whose inner domain
contains it. The theorem also supplies source membership, membership of its
coordinate in the compact coordinate set and chart target, and the cutoff-one
germ needed by fixed-anchor coordinate identities. -/
theorem exists_chart_of_point
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    (y : M) :
    ∃ i : data.Index,
      y ∈ data.innerDomain i ∧
      y ∈ (extChartAt I (i : M)).source ∧
      extChartAt I (i : M) y ∈ data.compactCoordinateSet i ∧
      extChartAt I (i : M) y ∈ (extChartAt I (i : M)).target ∧
      ∀ᶠ z' in nhds (extChartAt I (i : M) y),
        GeodesicTransport.cutoff (n := n) (i : M) z' = 1 := by
  have hy : y ∈ ⋃ i : data.Index, data.innerDomain i := by
    rw [data.innerDomain_cover]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.1 hy with ⟨i, hyDomain⟩
  have hyClosure : y ∈ closure (data.innerDomain i) :=
    subset_closure hyDomain
  have hyNeighborhood :=
    data.closure_innerDomain_subset_cutoffOneChartNeighborhood i hyClosure
  have hyCoord :
      extChartAt I (i : M) y ∈ data.compactCoordinateSet i :=
    ⟨y, hyClosure, rfl⟩
  exact ⟨i, hyDomain, hyNeighborhood.1, hyCoord,
    (extChartAt I (i : M)).map_source hyNeighborhood.1,
    hyNeighborhood.2⟩

/-- On one of the finitely many fixed charts covering `y`, the coordinate
covariant-Ricci norm contraction for any metric family equals the intrinsic
squared norm at `y`. No continuity in a moving chart anchor is used. -/
theorem exists_chart_anchorCovRicciNormSqFamily_eq_intrinsic
    (data : FiniteFixedAnchorCutoffOneChartCover n M)
    {K : Type v} (g : K → ClosedSmoothRiemannianMetric n M)
    (k : K) (y : M) :
    ∃ i : data.Index,
      y ∈ data.innerDomain i ∧
      y ∈ (extChartAt I (i : M)).source ∧
      extChartAt I (i : M) y ∈ data.compactCoordinateSet i ∧
      anchorChartCovRicciNormSqFamily g (i : M) k
          (extChartAt I (i : M) y) =
        covRicciNormSqAt (g k) y := by
  obtain ⟨i, hyDomain, hySource, hyCoordinate, hyTarget, hyCutoff⟩ :=
    data.exists_chart_of_point y
  refine ⟨i, hyDomain, hySource, hyCoordinate, ?_⟩
  calc
    anchorChartCovRicciNormSqFamily g (i : M) k
        (extChartAt I (i : M) y) =
        covRicciNormSqAt (g k)
          ((extChartAt I (i : M)).symm (extChartAt I (i : M) y)) :=
      anchorChartCovRicciNormSqFamily_eq_covRicciNormSqAt_zone
        g (i : M) k hyTarget hyCutoff
    _ = covRicciNormSqAt (g k) y := by
      rw [(extChartAt I (i : M)).left_inv hySource]

end FiniteFixedAnchorCutoffOneChartCover
end Poincare
