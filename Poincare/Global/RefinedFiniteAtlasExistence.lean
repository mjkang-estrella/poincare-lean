import Poincare.Global.CenteredCoordinateNeighborhoodShrinking
import Poincare.Global.FiniteAtlasParabolicTensorSpace

/-!
# Finite atlases refined by centered coordinate neighborhoods

Shrink around every preferred chart anchor before extracting a finite
subcover. The selected regions retain their anchors, their compact coordinate
closures stay in the prescribed neighborhoods, and a smooth partition of
unity is constructed subordinate to these regions.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace Poincare.RefinedFiniteAtlasExistence

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) ∞ M]

/-- Every family of open coordinate neighborhoods of the preferred chart
centers admits a finite atlas with compact coordinate closures inside that
family and a smooth subordinate partition of unity. -/
theorem exists_refined_atlasData
    (V : M → Set (ClosedSmoothModel 3)) (hV : ∀ p, IsOpen (V p))
    (hpV : ∀ p, extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) p p ∈ V p) :
    ∃ A : FiniteAtlasParabolicTensorSpace.AtlasData M,
      (∀ i, A.cover.anchor i ∈ A.region i) ∧
      ∀ i, FiniteAtlasParabolicTensorSpace.chart A i '' closure (A.region i) ⊆
        V (A.cover.anchor i) := by
  classical
  have hshrinking := fun p : M =>
    CenteredCoordinateNeighborhoodShrinking.exists_centered_chart_shrinking p (V p)
      (hV p) (hpV p)
  choose U hUopen hpU hUsource hUcompact hUV using hshrinking
  obtain ⟨anchors, hcover⟩ := isCompact_univ.elim_finite_subcover U hUopen (by
    intro p _hp
    exact mem_iUnion.mpr ⟨p, hpU p⟩)
  let anchor : Fin anchors.card → M := fun i => (anchors.equivFin.symm i).1
  let region : Fin anchors.card → Set M := fun i => U (anchor i)
  have hregion_cover : (⋃ i, region i) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    let a' : anchors := ⟨a, ha⟩
    refine mem_iUnion.mpr ⟨anchors.equivFin a', ?_⟩
    simpa [region, anchor, a'] using hxa
  let C : FiniteExtendedChartCover (n := 3) (M := M) := {
    chartCount := anchors.card
    anchor := anchor
    sources_cover := by
      apply eq_univ_of_forall
      intro x
      have hx : x ∈ ⋃ i, region i := hregion_cover.symm ▸ mem_univ x
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, hUsource (anchor i) (subset_closure hxi)⟩ }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity (Fin anchors.card)
      (closedSmoothModelWithCorners 3) M univ, ρ.IsSubordinate region := by
    apply SmoothPartitionOfUnity.exists_isSubordinate _ isClosed_univ region
      (fun i => hUopen (anchor i))
    rw [hregion_cover]
  let A : FiniteAtlasParabolicTensorSpace.AtlasData M := {
    cover := C
    region := region
    region_open := fun i => hUopen (anchor i)
    region_cover := hregion_cover
    closure_source := fun i => hUsource (anchor i)
    coordinate_compact := fun i => hUcompact (anchor i)
    partition := ρ
    subordinate := hρ }
  exact ⟨A, fun i => hpU (anchor i), fun i => hUV (anchor i)⟩

end Poincare.RefinedFiniteAtlasExistence
