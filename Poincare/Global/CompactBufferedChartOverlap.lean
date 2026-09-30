import Poincare.Global.FiniteAtlasParabolicTensorSpace
import Poincare.Global.GeodesicTransport

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.CompactBufferedChartOverlap

open FiniteAtlasParabolicTensorSpace

universe u
/-- The actual buffered transport support is compact inside an open good chart overlap. -/
theorem isCompact_subset_good_overlap
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (hcompact : ∀ k, HasCompactSupport (ξ k))
    (htarget : ∀ k, tsupport (ξ k) ⊆ (chart A k).target)
    (houter : ∀ k, ∀ z ∈ tsupport (ξ k),
      ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1)
    (hpartition : ∀ k, ∀ z ∈ coordSupport A k,
      ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1)
    (i j : Fin A.cover.chartCount) :
    let K := (chart A i) ''
      (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport (ξ j))
    let O := ((chart A i).symm.trans (chart A j)).source ∩
      (fun z : ClosedSmoothModel 3 =>
        ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor i) y = 1) ∩
      (change A i j) ⁻¹' (fun z : ClosedSmoothModel 3 =>
        ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor j) y = 1)
    IsCompact K ∧ IsOpen O ∧ K ⊆ O := by
  dsimp only
  have hsource : tsupport (A.partition i) ∩ (chart A j).symm '' tsupport (ξ j) ⊆
      (chart A i).source := fun _ hx => partition_support_source A i hx.1
  have hinverseCompact : IsCompact ((chart A j).symm '' tsupport (ξ j)) :=
    (hcompact j).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor j)).mono (htarget j))
  have hoverlapOpen : IsOpen ((chart A i).symm.trans (chart A j)).source := by
    change IsOpen ((chart A i).target ∩ (chart A i).symm ⁻¹' (chart A j).source)
    exact (continuousOn_extChartAt_symm (A.cover.anchor i)).isOpen_inter_preimage
      (isOpen_extChartAt_target (A.cover.anchor i))
      (isOpen_extChartAt_source (A.cover.anchor j))
  have hchange : ContinuousOn (change A i j)
      ((chart A i).symm.trans (chart A j)).source :=
    (contDiffOn_ext_coord_change (I := closedSmoothModelWithCorners 3) (n := ∞)
      (A.cover.anchor j) (A.cover.anchor i)).continuousOn
  have hone (k : Fin A.cover.chartCount) : IsOpen
      {z : ClosedSmoothModel 3 |
        ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1} :=
    isOpen_setOf_eventually_nhds
  refine ⟨(hinverseCompact.inter_left (isClosed_tsupport _)).image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono hsource),
    (hchange.mono inter_subset_left).isOpen_inter_preimage
      (hoverlapOpen.inter (hone i)) (hone j), ?_⟩
  rintro z ⟨x, ⟨hxp, hxξ⟩, rfl⟩
  have hxi : x ∈ (chart A i).source := partition_support_source A i hxp
  obtain ⟨y, hy, hyx⟩ := hxξ
  have hxj : x ∈ (chart A j).source := by
    rw [← hyx]
    exact (chart A j).map_target (htarget j hy)
  have htransition : chart A i x ∈ ((chart A i).symm.trans (chart A j)).source :=
    PartialEquiv.mem_symm_trans_source (e := chart A i) hxi hxj
  refine ⟨⟨htransition, hpartition i _ ⟨x, hxp, rfl⟩⟩, ?_⟩
  change ∀ᶠ w in 𝓝 (change A i j (chart A i x)),
    GeodesicTransport.cutoff (n := 3) (A.cover.anchor j) w = 1
  rw [change_chart A i j x hxi, ← hyx, (chart A j).right_inv (htarget j hy)]
  exact houter j y hy

end Poincare.CompactBufferedChartOverlap
