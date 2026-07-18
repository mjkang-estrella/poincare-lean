import Poincare.Global.SmoothabilityFiniteAtlasNerveReduction
import Poincare.Global.SmoothabilityProofBearingAtlasUpgrade

/-!
# Finite transition-smoothing boundary

The finite precompact atlas reduction leaves a genuinely finite smoothing
problem.  For each selected chart, choose a coordinate correction defined on
an open neighborhood of the compact image of the chart-domain closure.  On
each edge of the finite atlas nerve, require the transition between the
corrected, inner-domain-restricted charts to be `C∞`.

This file proves that this finite simultaneous correction contract constructs
`CInfinityLocalTransitionAtlasData3`.  It does not store a `ChartedSpace`, an
`IsManifold` proof, or a recognition homeomorphism in the contract.  The
charted space is assembled below from the finite corrected charts; pairs not
present in the nerve have empty transition source, so their smoothness is
automatic.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SmoothabilityFiniteTransitionSmoothingBoundary

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "I₃" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ambientChartedSpace : ChartedSpace E₃ M]

abbrev PrecompactAtlas3 :=
  SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3

abbrev NerveTransitionPackage3 (data : PrecompactAtlas3 M) :=
  SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3
    data

abbrev NerveReduction3 :=
  SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveReduction3

namespace PrecompactAtlas3

/-- Restrict a selected preferred chart to its open inner domain, then apply
the supplied Euclidean coordinate correction. -/
def correctedInnerChart (data : PrecompactAtlas3 M)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (i : data.Index) : OpenPartialHomeomorph M E₃ :=
  ((data.chart i).restrOpen (data.innerDomain i)
    (data.isOpen_innerDomain i)).trans (correction i)

/-- If a correction is defined on the compact coordinate image of the whole
inner-domain closure, then the corrected chart has exactly the selected inner
domain as its source. -/
theorem correctedInnerChart_source
    (data : PrecompactAtlas3 M)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (hsource : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    (i : data.Index) :
    (data.correctedInnerChart correction i).source =
      data.innerDomain i := by
  rw [correctedInnerChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.restrOpen_source]
  ext x
  constructor
  · rintro ⟨⟨_hchart, hx⟩, _hcorr⟩
    exact hx
  · intro hx
    have hchart : x ∈ (data.chart i).source :=
      data.innerDomain_subset_chart_source i hx
    refine ⟨⟨hchart, hx⟩, ?_⟩
    exact hsource i ⟨x, subset_closure hx, rfl⟩

/-- The transition source between two corrected charts is empty whenever the
corresponding inner domains do not meet. -/
theorem correctedInnerChart_transition_source_eq_empty_of_not_nerveRel
    (data : PrecompactAtlas3 M)
    (correction : data.Index → OpenPartialHomeomorph E₃ E₃)
    (hsource : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source)
    {i j : data.Index} (hij : ¬ data.NerveRel i j) :
    ((data.correctedInnerChart correction i).symm.trans
      (data.correctedInnerChart correction j)).source = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  intro y hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hiSource :
      (data.correctedInnerChart correction i).symm y ∈
        (data.correctedInnerChart correction i).source := by
    exact (data.correctedInnerChart correction i).symm.map_source hy.1
  have hjSource :
      (data.correctedInnerChart correction i).symm y ∈
        (data.correctedInnerChart correction j).source :=
    hy.2
  rw [data.correctedInnerChart_source correction hsource i] at hiSource
  rw [data.correctedInnerChart_source correction hsource j] at hjSource
  exact (hij ⟨_, hiSource, hjSource⟩).elim

end PrecompactAtlas3

/-- The genuine finite simultaneous smoothing/extension obligation.

The correction attached to vertex `i` is an open partial homeomorphism on
Euclidean coordinates.  `correction_neighborhood` says that it is defined on
an open neighborhood of the compact image of the entire inner-domain
closure.  The only regularity field ranges over the finite subtype of nerve
edges and concerns the actual transition of the corrected restricted charts.

In particular, this structure contains neither a charted-space instance nor
an `IsManifold` proof. -/
structure FiniteSimultaneousTransitionSmoothingExtension3
    (data : PrecompactAtlas3 M)
    (nerve : NerveTransitionPackage3 data) where
  correction : data.Index → OpenPartialHomeomorph E₃ E₃
  correction_neighborhood : ∀ i,
    data.compactCoordinateImage i ⊆ (correction i).source
  transitionContDiffOn : ∀ p : ↑nerve.orderedPairs,
    let i : data.Index := (p : data.Index × data.Index).1
    let j : data.Index := (p : data.Index × data.Index).2
    ContDiffOn ℝ ∞
      (I₃ ∘
        (data.correctedInnerChart correction i).symm ≫ₕ
          data.correctedInnerChart correction j ∘ (I₃).symm)
      ((I₃).symm ⁻¹'
        ((data.correctedInnerChart correction i).symm ≫ₕ
          data.correctedInnerChart correction j).source ∩ Set.range I₃)

namespace FiniteSimultaneousTransitionSmoothingExtension3

variable {data :
  @SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3
    M _ _ _ ambientChartedSpace}
variable {nerve :
  @SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3
    M _ _ _ ambientChartedSpace data}

/-- The corrected inner charts form a charted space.  Coverage is derived
from the precompact atlas cover and the correction-neighborhood field. -/
@[implicit_reducible] noncomputable def toChartedSpace
    (smoothing : FiniteSimultaneousTransitionSmoothingExtension3 data nerve) :
    ChartedSpace E₃ M := by
  classical
  let chooseIndex : M → data.Index := fun x ↦
    Classical.choose (by
      have hx : x ∈ ⋃ i : data.Index, data.innerDomain i := by
        rw [data.innerDomain_cover]
        exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx)
  have chooseIndex_mem : ∀ x, x ∈ data.innerDomain (chooseIndex x) := by
    intro x
    exact Classical.choose_spec (by
      have hx : x ∈ ⋃ i : data.Index, data.innerDomain i := by
        rw [data.innerDomain_cover]
        exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx)
  exact {
    atlas := Set.range
      (PrecompactAtlas3.correctedInnerChart data smoothing.correction)
    chartAt := fun x ↦
      PrecompactAtlas3.correctedInnerChart data smoothing.correction
        (chooseIndex x)
    mem_chart_source := fun x ↦ by
      rw [PrecompactAtlas3.correctedInnerChart_source data
        smoothing.correction smoothing.correction_neighborhood]
      exact chooseIndex_mem x
    chart_mem_atlas := fun x ↦ ⟨chooseIndex x, rfl⟩
  }

/-- Every transition in the assembled finite charted space is `C∞`.

For a represented nerve edge this is exactly the finite contract.  If the
edge is absent, the two inner domains are disjoint, hence the transition
source (and therefore the differentiability domain) is empty. -/
theorem toChartedSpace_transitionContDiffOn
    (smoothing : FiniteSimultaneousTransitionSmoothingExtension3 data nerve) :
    letI : ChartedSpace E₃ M := smoothing.toChartedSpace
    ∀ e e' : OpenPartialHomeomorph M E₃,
      e ∈ atlas E₃ M →
      e' ∈ atlas E₃ M →
        ContDiffOn ℝ ∞
          (I₃ ∘ e.symm ≫ₕ e' ∘ (I₃).symm)
          ((I₃).symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I₃) := by
  let correction : data.Index → OpenPartialHomeomorph E₃ E₃ :=
    @FiniteSimultaneousTransitionSmoothingExtension3.correction
      M _ _ _ ambientChartedSpace data nerve smoothing
  have correction_neighborhood : ∀ i,
      data.compactCoordinateImage i ⊆ (correction i).source :=
    @FiniteSimultaneousTransitionSmoothingExtension3.correction_neighborhood
      M _ _ _ ambientChartedSpace data nerve smoothing
  letI : ChartedSpace E₃ M := smoothing.toChartedSpace
  intro e e' he he'
  change e ∈ Set.range
    (@PrecompactAtlas3.correctedInnerChart M _ _ _ ambientChartedSpace
      data correction) at he
  change e' ∈ Set.range
    (@PrecompactAtlas3.correctedInnerChart M _ _ _ ambientChartedSpace
      data correction) at he'
  rcases he with ⟨i, rfl⟩
  rcases he' with ⟨j, rfl⟩
  by_cases hij :
      @SmoothabilityFinitePrecompactTopologicalAtlasReduction.FinitePrecompactTopologicalChartAtAtlas3.NerveRel
        M _ _ _ ambientChartedSpace data i j
  · let p :
        ↑(@SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.orderedPairs
          M _ _ _ ambientChartedSpace data nerve) :=
      ⟨(i, j),
        (@SmoothabilityFiniteAtlasNerveReduction.FiniteAtlasNerveTransitionPackage3.pair_mem_iff
          M _ _ _ ambientChartedSpace data nerve (i, j)).2 hij⟩
    exact @FiniteSimultaneousTransitionSmoothingExtension3.transitionContDiffOn
      M _ _ _ ambientChartedSpace data nerve smoothing p
  · have hempty :
        ((@PrecompactAtlas3.correctedInnerChart M _ _ _ ambientChartedSpace
            data correction i).symm ≫ₕ
          @PrecompactAtlas3.correctedInnerChart M _ _ _ ambientChartedSpace
            data correction j).source = ∅ :=
      @PrecompactAtlas3.correctedInnerChart_transition_source_eq_empty_of_not_nerveRel
        M _ _ _ ambientChartedSpace data correction correction_neighborhood
          i j hij
    rw [hempty]
    simp

/-- A finite simultaneous correction witness constructs the existing
proof-bearing `C∞` local-transition atlas package. -/
noncomputable def toCInfinityLocalTransitionAtlasData3
    (smoothing : FiniteSimultaneousTransitionSmoothingExtension3 data nerve) :
    CInfinityLocalTransitionAtlasData3 M where
  smoothAtlas := smoothing.toChartedSpace
  transitionContDiffOn :=
    smoothing.toChartedSpace_transitionContDiffOn

end FiniteSimultaneousTransitionSmoothingExtension3

/-- A fixed-target witness consists of the already-proved finite topological
nerve reduction and solutions of its finite coordinate-correction problem.
It still contains no smooth atlas or recognition result. -/
structure FiniteAtlasNerveTransitionSmoothingWitness3
    (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace E₃ M] where
  reduction : NerveReduction3 M
  smoothing :
    FiniteSimultaneousTransitionSmoothingExtension3
      reduction.atlas reduction.transitions

/-- The finite atlas-nerve smoothing witness closes precisely the selected
`C∞` local-transition-atlas existence boundary. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteAtlasNerveTransitionSmoothingWitness3
    (witness : FiniteAtlasNerveTransitionSmoothingWitness3 M) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) :=
  ⟨witness.smoothing.toCInfinityLocalTransitionAtlasData3⟩

/-- It is enough to solve the finite simultaneous correction problem for
every finite nerve reduction: compactness supplies a reduction, after which
the preceding construction supplies the smooth-transition atlas. -/
theorem nonempty_cInfinityLocalTransitionAtlasData3_of_finiteAtlasNerveTransitionSmoothingProvider3
    (provider : ∀ reduction : NerveReduction3 M,
      Nonempty (FiniteSimultaneousTransitionSmoothingExtension3
        reduction.atlas reduction.transitions)) :
    Nonempty (CInfinityLocalTransitionAtlasData3 M) := by
  obtain ⟨reduction⟩ :=
    SmoothabilityFiniteAtlasNerveReduction.exists_finiteAtlasNerveReduction3
      (M := M)
  exact
    nonempty_cInfinityLocalTransitionAtlasData3_of_finiteAtlasNerveTransitionSmoothingWitness3
      ⟨reduction, (provider reduction).some⟩

end SmoothabilityFiniteTransitionSmoothingBoundary
end Poincare
