import Poincare.Global.CartanGenericSuccessorDataLocalCover

/-!
# A preferred-chart obstruction to fixed-chart successor persistence

The frozen curvature-only persistence claim requires joint control of the
selected charts, even before derivatives are considered.  In particular, a
fixed endpoint must belong to the preferred charts of all nearby anchors.
This module proves that necessary condition and constructs compatible smooth
chart restrictions for which it fails at every nonisolated chosen center.

The frozen theorem is not declared here.  The chart restriction construction
does not transport a constant-curvature metric to the new charted structure;
the accompanying blocked report distinguishes this from a full formal
counterexample to the curvature-only statement.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace FixedChartSuccessorDataPersistence

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanGenericSuccessorDataLocalCover
open CartanAtlasRootedPathCurvatureSuccessorRadius

/-- A necessary source-chart condition for a joint successor-data
neighborhood.  The endpoint stays fixed while the preferred chart moves. -/
def PreferredChartSourcePersistence (x₀ : M) : Prop :=
  {y : M | x₀ ∈ (extChartAt I y).source} ∈ 𝓝 x₀

/-- Pull back the joint data neighborhood along `y ↦ ((y, p₀), x₀)`.
The actual datum's source membership forces persistence of preferred charts. -/
theorem preferredChartSourcePersistence_of_universalSuccessorDataNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hdata : UniversalSuccessorDataNeighborhood g)
    (x₀ : M) (p₀ : RoundSphere3) :
    PreferredChartSourcePersistence x₀ := by
  have hdiagonal : ((x₀, p₀), x₀) ∈ successorParameterDiagonal (M := M) :=
    ⟨(x₀, p₀), Set.mem_univ _, rfl⟩
  have hnhds : UniversalSuccessorDataLocus g ∈ 𝓝 ((x₀, p₀), x₀) :=
    mem_nhdsSet_iff_forall.mp hdata _ hdiagonal
  have hcont : Continuous (fun y : M ↦ ((y, p₀), x₀)) := by fun_prop
  filter_upwards [hcont.continuousAt.preimage_mem_nhds hnhds] with y hy
  obtain ⟨L⟩ := CartanMap.tangentAlignment_nonempty g y p₀
  obtain ⟨d⟩ := hy L
  exact d.source_mem_oldChart

/-- Failure of the preferred-chart condition rules out the frozen
fixed-chart persistence conclusion for any metric. -/
theorem not_fixedChartLocalGenericDataPersistence_of_not_preferredChartSourcePersistence
    (g : ClosedSmoothRiemannianMetric 3 M)
    (x₀ : M) (p₀ : RoundSphere3)
    (hsource : ¬ PreferredChartSourcePersistence x₀) :
    ¬ FixedChartLocalGenericDataPersistence g := by
  intro hfixed
  exact hsource
    (preferredChartSourcePersistence_of_universalSuccessorDataNeighborhood
      g (universalSuccessorDataNeighborhood_of_fixedChartLocalGenericDataPersistence
        hfixed) x₀ p₀)

section Reselection

variable [T1Space M]

/-- Keep the center's chart; remove the center from every other chart. -/
def centerAvoidingSet (x₀ y : M) : Set M := by
  classical
  exact if y = x₀ then univ else {x₀}ᶜ

omit [ChartedSpace E M] [IsManifold I ∞ M] in
theorem isOpen_centerAvoidingSet (x₀ y : M) :
    IsOpen (centerAvoidingSet x₀ y) := by
  classical
  by_cases h : y = x₀ <;>
    simp [centerAvoidingSet, h]

/-- These are restrictions of the original smooth charts. -/
def centerAvoidingChart (x₀ y : M) : OpenPartialHomeomorph M E :=
  (chartAt E y).restr (centerAvoidingSet x₀ y)

omit [IsManifold I ∞ M] in
theorem self_mem_centerAvoidingChart_source (x₀ y : M) :
    y ∈ (centerAvoidingChart x₀ y).source := by
  classical
  rw [centerAvoidingChart, OpenPartialHomeomorph.restr_source'
    _ _ (isOpen_centerAvoidingSet x₀ y)]
  refine ⟨mem_chart_source E y, ?_⟩
  by_cases h : y = x₀ <;> simp [centerAvoidingSet, h]

omit [IsManifold I ∞ M] in
theorem center_mem_centerAvoidingChart_source_iff (x₀ y : M) :
    x₀ ∈ (centerAvoidingChart x₀ y).source ↔ y = x₀ := by
  classical
  rw [centerAvoidingChart, OpenPartialHomeomorph.restr_source'
    _ _ (isOpen_centerAvoidingSet x₀ y)]
  by_cases h : y = x₀
  · subst y
    simp [centerAvoidingSet]
  · simp [centerAvoidingSet, h]

/-- The restricted charts remain in the original smooth maximal atlas. -/
theorem centerAvoidingChart_mem_maximalAtlas (x₀ y : M) :
    centerAvoidingChart x₀ y ∈ IsManifold.maximalAtlas I ∞ M := by
  exact restr_mem_maximalAtlas (contDiffGroupoid ∞ I)
    (IsManifold.chart_mem_maximalAtlas y) (isOpen_centerAvoidingSet x₀ y)

/-- Change only the preferred chart selection, using the original maximal
smooth atlas.  No topological structure is changed. -/
@[implicit_reducible]
def centerAvoidingChartedSpace (x₀ : M) : ChartedSpace E M where
  atlas := IsManifold.maximalAtlas I ∞ M
  chartAt := centerAvoidingChart x₀
  mem_chart_source := self_mem_centerAvoidingChart_source x₀
  chart_mem_atlas := centerAvoidingChart_mem_maximalAtlas x₀

/-- Compatibility of the original maximal atlas proves smoothness for the
reselected charted structure. -/
theorem centerAvoidingChartedSpace_isManifold (x₀ : M) :
    letI := centerAvoidingChartedSpace x₀
    IsManifold I ∞ M := by
  have hcompatible : ∀ {e e' : OpenPartialHomeomorph M E},
      e ∈ IsManifold.maximalAtlas I ∞ M →
      e' ∈ IsManifold.maximalAtlas I ∞ M →
      e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
    fun he he' ↦ IsManifold.compatible_of_mem_maximalAtlas he he'
  letI := centerAvoidingChartedSpace x₀
  exact { compatible := hcompatible }

omit [IsManifold I ∞ M] in
/-- The fixed-endpoint source slice is exactly the singleton center. -/
theorem centerAvoidingChart_source_slice (x₀ : M) :
    {y : M | x₀ ∈ (centerAvoidingChart x₀ y).source} = {x₀} := by
  ext y
  exact center_mem_centerAvoidingChart_source_iff x₀ y

/-- At a nonisolated center the reselected smooth charts violate the
necessary preferred-chart condition. -/
theorem not_preferredChartSourcePersistence_centerAvoiding
    (x₀ : M) [(𝓝[≠] x₀).NeBot] :
    letI := centerAvoidingChartedSpace x₀
    ¬ PreferredChartSourcePersistence x₀ := by
  simp only [PreferredChartSourcePersistence, extChartAt_source]
  change ¬ ({y : M | x₀ ∈ (centerAvoidingChart x₀ y).source} ∈ 𝓝 x₀)
  rw [centerAvoidingChart_source_slice]
  intro h
  apply not_isOpen_singleton x₀
  exact isOpen_iff_mem_nhds.mpr (by
    intro y hy
    obtain rfl := mem_singleton_iff.mp hy
    exact h)

/-- No metric on the compatible reselected smooth atlas can satisfy the
fixed-chart persistence conclusion at a nonisolated center. -/
theorem not_fixedChartLocalGenericDataPersistence_centerAvoiding
    (x₀ : M) [(𝓝[≠] x₀).NeBot] (p₀ : RoundSphere3) :
    let smooth := centerAvoidingChartedSpace_isManifold x₀
    letI := centerAvoidingChartedSpace x₀
    letI := smooth
    ∀ g : ClosedSmoothRiemannianMetric 3 M,
      ¬ FixedChartLocalGenericDataPersistence g := by
  dsimp only
  have hsource := not_preferredChartSourcePersistence_centerAvoiding x₀
  have smooth := centerAvoidingChartedSpace_isManifold x₀
  letI := centerAvoidingChartedSpace x₀
  letI := smooth
  intro g
  exact not_fixedChartLocalGenericDataPersistence_of_not_preferredChartSourcePersistence
    g x₀ p₀ hsource

end Reselection

end FixedChartSuccessorDataPersistence
end Poincare
