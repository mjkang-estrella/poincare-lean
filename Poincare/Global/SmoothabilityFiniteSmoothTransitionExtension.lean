import Poincare.Global.SmoothabilityFiniteTransitionSmoothingBoundary

/-!
# Finite smooth extensions of compact transition data

The finite transition-smoothing boundary can be reduced one step further to
an explicitly Euclidean extension problem.  After choosing one coordinate
correction at each vertex of the finite precompact atlas, every compact nerve
edge carries a corrected topological transition.  The lower contract in this
file asks for a Euclidean function smooth on an open neighborhood of that
corrected compact domain and agreeing there with the genuine transition.

From this compact-domain agreement we prove smoothness of the actual
transition between the corrected inner charts.  The proof uses neither a
stored smooth atlas nor a stored `ContDiffOn` assertion about that transition:
the atlas and transition regularity are derived.

Mathlib's smooth-approximation theorem is intentionally not used to invent
the extensions.  It approximates continuous maps but does not preserve local
homeomorphism, exact overlap agreement, inverse compatibility, or finite
cocycle identities.  Producing the compatible extensions below from PL data
is therefore the remaining finite smoothing theorem.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityFiniteSmoothTransitionExtension

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ambientChartedSpace : ChartedSpace E₃ M]

open SmoothabilityFiniteTransitionSmoothingBoundary
open SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3

abbrev PrecompactAtlas3 :=
  SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3
    data

/-- Strictly lower finite Euclidean smoothing data.

The vertex corrections are defined on neighborhoods of the compact chart
closures.  For each member of the finite ordered nerve, `smoothExtension` is
smooth on a supplied open neighborhood of the corrected compact transition
domain and agrees with the genuine topological transition on the compact set.

No `ChartedSpace`, `IsManifold`, corrected-chart transition, or
`ContDiffOn` statement about a corrected-chart transition is a field. -/
structure FiniteCompatibleSmoothTransitionExtensions3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  correction : data.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    data.compactCoordinateImage i ⊆ (correction i).source
  extensionNeighborhood : ↑nerve.orderedPairs → Set E₃
  isOpen_extensionNeighborhood : ∀ p,
    IsOpen (extensionNeighborhood p)
  correctedCompactDomain_subset_extensionNeighborhood : ∀ p,
    correction p.1.1 '' nerve.transitionDomain p ⊆
      extensionNeighborhood p
  smoothExtension : ↑nerve.orderedPairs → E₃ → E₃
  smoothExtension_contDiffOn : ∀ p,
    ContDiffOn ℝ ∞ (smoothExtension p) (extensionNeighborhood p)
  smoothExtension_agrees_on_compactDomain :
    ∀ (p : ↑nerve.orderedPairs) (u : E₃),
      u ∈ nerve.transitionDomain p →
        smoothExtension p (correction p.1.1 u) =
          correction p.1.2 (nerve.transitionMap p u)

namespace FiniteCompatibleSmoothTransitionExtensions3

variable {data : PrecompactAtlas3 M}
variable {nerve : NerveTransitionPackage3 data}

/-- On a represented overlap closure, the Euclidean extension agrees with
the two corrected inner-chart values. -/
theorem smoothExtension_correctedInnerChart_eq_on_overlapClosure
    (extension : FiniteCompatibleSmoothTransitionExtensions3 data nerve)
    (p : ↑nerve.orderedPairs) (x : M)
    (hx : x ∈ closure
      (data.overlap (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2)) :
    extension.smoothExtension p
        (correctedInnerChart data extension.correction p.1.1 x) =
      correctedInnerChart data extension.correction p.1.2 x := by
  have hu : data.chart p.1.1 x ∈ nerve.transitionDomain p := by
    rw [nerve.transitionDomain_eq p]
    exact ⟨x, hx, rfl⟩
  have hagree :=
    extension.smoothExtension_agrees_on_compactDomain p
      (data.chart p.1.1 x) hu
  rw [nerve.transition_agrees_on_overlapClosure p x hx] at hagree
  simpa [SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart,
    OpenPartialHomeomorph.trans_apply] using hagree

/-- Compact-domain extension agreement implies agreement with the actual
corrected-chart transition everywhere on its open source. -/
theorem smoothExtension_eq_correctedTransition_on_source
    (extension : FiniteCompatibleSmoothTransitionExtensions3 data nerve)
    (p : ↑nerve.orderedPairs) :
    Set.EqOn (extension.smoothExtension p)
      ((correctedInnerChart data extension.correction p.1.1).symm.trans
        (correctedInnerChart data extension.correction p.1.2))
      (((correctedInnerChart data extension.correction p.1.1).symm.trans
        (correctedInnerChart data extension.correction p.1.2)).source) := by
  intro y hy
  let leftChart :=
    correctedInnerChart data extension.correction p.1.1
  let rightChart :=
    correctedInnerChart data extension.correction p.1.2
  rw [OpenPartialHomeomorph.trans_source] at hy
  let x : M := leftChart.symm y
  have hxleft : x ∈ leftChart.source := by
    exact leftChart.symm.map_source hy.1
  have hxright : x ∈ rightChart.source := hy.2
  have hleftSource : leftChart.source = data.innerDomain p.1.1 := by
    simpa [leftChart] using
      (SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart_source
        data extension.correction extension.correction_neighborhood p.1.1)
  have hrightSource : rightChart.source = data.innerDomain p.1.2 := by
    simpa [rightChart] using
      (SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart_source
        data extension.correction extension.correction_neighborhood p.1.2)
  have hxleftInner : x ∈ data.innerDomain p.1.1 := by
    rw [← hleftSource]
    exact hxleft
  have hxrightInner : x ∈ data.innerDomain p.1.2 := by
    rw [← hrightSource]
    exact hxright
  have hxclosure : x ∈ closure
      (data.overlap (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2) :=
    subset_closure ⟨hxleftInner, hxrightInner⟩
  have hagree :=
    extension.smoothExtension_correctedInnerChart_eq_on_overlapClosure
      p x hxclosure
  have hleft : leftChart x = y :=
    leftChart.symm.left_inv hy.1
  calc
    extension.smoothExtension p y =
        extension.smoothExtension p (leftChart x) := by rw [hleft]
    _ = rightChart x := by simpa [leftChart, rightChart] using hagree
    _ = (leftChart.symm.trans rightChart) y := by
      rw [OpenPartialHomeomorph.trans_apply]

/-- The source of the actual corrected transition lies in the supplied open
neighborhood of the corrected compact transition domain. -/
theorem correctedTransition_source_subset_extensionNeighborhood
    (extension : FiniteCompatibleSmoothTransitionExtensions3 data nerve)
    (p : ↑nerve.orderedPairs) :
    (((correctedInnerChart data extension.correction p.1.1).symm.trans
        (correctedInnerChart data extension.correction p.1.2)).source) ⊆
      extension.extensionNeighborhood p := by
  intro y hy
  let leftChart :=
    correctedInnerChart data extension.correction p.1.1
  let rightChart :=
    correctedInnerChart data extension.correction p.1.2
  rw [OpenPartialHomeomorph.trans_source] at hy
  let x : M := leftChart.symm y
  have hxleft : x ∈ leftChart.source :=
    leftChart.symm.map_source hy.1
  have hxright : x ∈ rightChart.source := hy.2
  have hleftSource : leftChart.source = data.innerDomain p.1.1 := by
    simpa [leftChart] using
      (SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart_source
        data extension.correction extension.correction_neighborhood p.1.1)
  have hrightSource : rightChart.source = data.innerDomain p.1.2 := by
    simpa [rightChart] using
      (SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart_source
        data extension.correction extension.correction_neighborhood p.1.2)
  have hxclosure : x ∈ closure
      (data.overlap (p : data.Index × data.Index).1
        (p : data.Index × data.Index).2) := by
    apply subset_closure
    constructor
    · rw [← hleftSource]
      exact hxleft
    · rw [← hrightSource]
      exact hxright
  have hu : data.chart p.1.1 x ∈ nerve.transitionDomain p := by
    rw [nerve.transitionDomain_eq p]
    exact ⟨x, hxclosure, rfl⟩
  apply extension.correctedCompactDomain_subset_extensionNeighborhood p
  refine ⟨data.chart p.1.1 x, hu, ?_⟩
  have hleft : leftChart x = y :=
    leftChart.symm.left_inv hy.1
  calc
    extension.correction p.1.1 (data.chart p.1.1 x) =
        leftChart x := by
      simp [leftChart,
        SmoothabilityFiniteTransitionSmoothingBoundary.PrecompactAtlas3.correctedInnerChart,
        OpenPartialHomeomorph.trans_apply]
    _ = y := hleft

/-- The finite smooth-extension datum constructs the preceding finite
simultaneous transition-smoothing contract. -/
noncomputable def toFiniteSimultaneousTransitionSmoothingExtension3
    (extension : FiniteCompatibleSmoothTransitionExtensions3 data nerve) :
    FiniteSimultaneousTransitionSmoothingExtension3 data nerve where
  correction := extension.correction
  correction_neighborhood := extension.correction_neighborhood
  transitionContDiffOn := fun p ↦ by
    let leftChart :=
      correctedInnerChart data extension.correction p.1.1
    let rightChart :=
      correctedInnerChart data extension.correction p.1.2
    have htransition : ContDiffOn ℝ ∞
        (leftChart.symm.trans rightChart)
        ((leftChart.symm.trans rightChart).source) :=
      ((extension.smoothExtension_contDiffOn p).mono
        (by
          simpa [leftChart, rightChart] using
            extension.correctedTransition_source_subset_extensionNeighborhood p)).congr
          (by
            intro y hy
            simpa [leftChart, rightChart] using
              (extension.smoothExtension_eq_correctedTransition_on_source
                p hy).symm)
    simpa only [closedSmoothModelWithCorners,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, preimage_id_eq, range_id,
      inter_univ] using htransition

/-- Consequently, compatible smooth extensions on the finitely many compact
nerve domains construct the existing proof-bearing local `C∞` atlas package. -/
noncomputable def toCInfinityLocalTransitionAtlasData3
    (extension : FiniteCompatibleSmoothTransitionExtensions3 data nerve) :
    CInfinityLocalTransitionAtlasData3 M :=
  extension.toFiniteSimultaneousTransitionSmoothingExtension3
    |>.toCInfinityLocalTransitionAtlasData3

end FiniteCompatibleSmoothTransitionExtensions3

/-- A finite nerve reduction plus compatible smooth Euclidean extensions is
enough for existence of the selected proof-bearing smooth-transition atlas. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteCompatibleSmoothTransitionExtensions3
    (reduction : SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M)
    (extension : FiniteCompatibleSmoothTransitionExtensions3
      reduction.atlas reduction.transitions) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  ⟨extension.toCInfinityLocalTransitionAtlasData3⟩

/-- A universal solver for the finite compact-domain extension problem closes
the selected smooth-transition-atlas boundary.  Compactness first supplies a
finite nerve reduction; the provider is used only on that extracted finite
datum. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteCompatibleSmoothTransitionExtensionsProvider3
    (provider : ∀ reduction :
      SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3 M,
      Nonempty (FiniteCompatibleSmoothTransitionExtensions3
        reduction.atlas reduction.transitions)) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨reduction⟩ :=
    SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
      (M := M)
  exact
    nonempty_cInfinityLocalTransitionAtlasData3_of_finiteCompatibleSmoothTransitionExtensions3
      reduction (provider reduction).some

end SmoothabilityFiniteSmoothTransitionExtension
end Poincare
