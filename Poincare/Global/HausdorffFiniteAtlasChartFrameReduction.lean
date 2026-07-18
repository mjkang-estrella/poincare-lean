import Poincare.Global.HausdorffPullbackAreaFormulaReduction
import Poincare.Global.HausdorffChartFrameFirstVariation

/-!
# Compact finite-atlas reduction for chart-frame Hausdorff variation

The chart-frame first-variation package still starts from an abstract finite
measurable coordinate decomposition.  On a compact manifold, the topological
part of that decomposition is automatic.  Extended-chart sources form an
open cover; compactness selects finitely many of them; and `disjointed`
turns that finite cover into measurable pairwise-disjoint manifold pieces.

For each piece, this module restricts the genuine inverse extended chart to
the corresponding coordinate subset.  It proves the coordinate-domain and
manifold-piece measurability, inverse-chart measurability, pairwise
disjointness, cover, and range identity.  Consequently, the decomposition's
`chartMeasure` field follows automatically from the restricted inverse-chart
pullback area formula.

What remains visible is exactly the analytic boundary:

* the variable-metric Hausdorff area formula on each restricted inverse
  chart;
* integrability of its Gram density;
* local dominated-differentiation bounds; and
* time differentiability of the metric in the selected chart frames.

No equality with `coordinateGramVolumeDensityAt` is used.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- A finite family of genuine extended charts whose open sources cover the
compact manifold. -/
structure FiniteExtendedChartCover where
  chartCount : ℕ
  anchor : Fin chartCount → M
  sources_cover :
    (⋃ i : Fin chartCount, (extChartAt I (anchor i)).source) = Set.univ

/-- Compactness extracts a finite subcover from the canonical extended-chart
source cover. -/
theorem exists_finiteExtendedChartCover :
    Nonempty (FiniteExtendedChartCover (n := n) (M := M)) := by
  classical
  obtain ⟨anchors, hanchors⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : M ↦ (extChartAt I x).source)
      (fun x ↦ isOpen_extChartAt_source x)
      (fun x _hx ↦ Set.mem_iUnion.mpr
        ⟨x, mem_extChartAt_source x⟩)
  refine ⟨
    { chartCount := anchors.card
      anchor := fun i ↦ (anchors.equivFin.symm i).1
      sources_cover := ?_ }⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hanchors (Set.mem_univ x))
  let a' : anchors := ⟨a, ha⟩
  refine Set.mem_iUnion.mpr ⟨anchors.equivFin a', ?_⟩
  simpa [a'] using hxa

/-- A fixed noncomputable finite extended-chart cover chosen from
compactness.  All later analytic hypotheses can be stated directly on this
canonical choice. -/
noncomputable def compactFiniteExtendedChartCover :
    FiniteExtendedChartCover (n := n) (M := M) :=
  Classical.choice exists_finiteExtendedChartCover

namespace FiniteExtendedChartCover

/-- The open source of the selected inverse chart. -/
def chartSource (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) : Set M :=
  (extChartAt I (C.anchor i)).source

/-- Canonical measurable disjointization of the finite chart-source cover. -/
def manifoldPiece (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) : Set M :=
  disjointed C.chartSource i

/-- Each disjointized manifold piece stays inside its original genuine chart
source. -/
theorem manifoldPiece_subset_chartSource
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    C.manifoldPiece i ⊆ C.chartSource i :=
  disjointed_subset C.chartSource i

/-- Disjointization of finitely many open chart sources is measurable. -/
theorem manifoldPiece_measurable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    MeasurableSet (C.manifoldPiece i) := by
  apply disjointedRec
  · intro t j ht
    exact ht.diff (isOpen_extChartAt_source (C.anchor j)).measurableSet
  · exact (isOpen_extChartAt_source (C.anchor i)).measurableSet

/-- The disjointized chart pieces are pairwise disjoint. -/
theorem manifoldPieces_pairwise
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    Set.univ.PairwiseDisjoint C.manifoldPiece := by
  intro i _hi j _hj hij
  exact (disjoint_disjointed C.chartSource) hij

/-- Disjointization preserves the union of the finite chart cover. -/
theorem manifoldPieces_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    (⋃ i, C.manifoldPiece i) = Set.univ := by
  change (⋃ i, disjointed C.chartSource i) = Set.univ
  rw [iUnion_disjointed]
  exact C.sources_cover

/-- The coordinate subset of the `i`-th genuine target chart which maps into
the `i`-th disjointized manifold piece. -/
def coordinateDomain
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) : Set E :=
  (extChartAt I (C.anchor i)).target ∩
    (extChartAt I (C.anchor i)).symm ⁻¹' C.manifoldPiece i

/-- The restricted coordinate domain lies in the genuine extended-chart
target. -/
theorem coordinateDomain_subset_target
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    C.coordinateDomain i ⊆ (extChartAt I (C.anchor i)).target :=
  inter_subset_left

/-- Regard a restricted coordinate point as a point of the full genuine
extended-chart target. -/
def coordinateTargetPoint
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) (z : C.coordinateDomain i) :
    (extChartAt I (C.anchor i)).target :=
  Set.inclusion (C.coordinateDomain_subset_target i) z

/-- The genuine inverse extended chart restricted to one disjoint coordinate
piece. -/
def inverseChart
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) : C.coordinateDomain i → M :=
  fun z ↦ inverseExtendedChartParametrization
    (n := n) (M := M) (C.anchor i) (C.coordinateTargetPoint i z)

/-- Restricting a genuine inverse extended chart preserves topological
embedding. -/
theorem inverseChart_isEmbedding
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    Topology.IsEmbedding (C.inverseChart i) := by
  exact
    (inverseExtendedChartParametrization_isEmbedding
      (n := n) (M := M) (C.anchor i)).comp
      (Topology.IsEmbedding.inclusion (C.coordinateDomain_subset_target i))

/-- The range of the restricted inverse chart is exactly its disjointized
manifold piece. -/
theorem range_inverseChart
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    Set.range (C.inverseChart i) = C.manifoldPiece i := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    exact z.2.2
  · intro x hx
    have hxsource : x ∈ (extChartAt I (C.anchor i)).source :=
      C.manifoldPiece_subset_chartSource i hx
    have htarget :
        (extChartAt I (C.anchor i)) x ∈
          (extChartAt I (C.anchor i)).target :=
      (extChartAt I (C.anchor i)).map_source hxsource
    let z : C.coordinateDomain i :=
      ⟨(extChartAt I (C.anchor i)) x,
        ⟨htarget, by
          change (extChartAt I (C.anchor i)).symm
              ((extChartAt I (C.anchor i)) x) ∈ C.manifoldPiece i
          rw [(extChartAt I (C.anchor i)).left_inv hxsource]
          exact hx⟩⟩
    refine ⟨z, ?_⟩
    exact (extChartAt I (C.anchor i)).left_inv hxsource

/-- The restricted inverse-chart coordinate domain is measurable. -/
theorem coordinateDomain_measurable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    MeasurableSet (C.coordinateDomain i) := by
  let T : Set E := (extChartAt I (C.anchor i)).target
  let ψ : T → M :=
    inverseExtendedChartParametrization
      (n := n) (M := M) (C.anchor i)
  have hT : MeasurableSet T :=
    (isOpen_extChartAt_target (C.anchor i)).measurableSet
  have hψContinuous : Continuous ψ :=
    continuous_subtype_val.comp
      (inverseExtendedChartHomeomorph
        (n := n) (M := M) (C.anchor i)).continuous
  have hpre : MeasurableSet (ψ ⁻¹' C.manifoldPiece i) :=
    hψContinuous.measurable (C.manifoldPiece_measurable i)
  have himage : MeasurableSet
      (((↑) : T → E) '' (ψ ⁻¹' C.manifoldPiece i)) :=
    (MeasurableEmbedding.subtype_coe hT).measurableSet_image' hpre
  rw [show C.coordinateDomain i =
      ((↑) : T → E) '' (ψ ⁻¹' C.manifoldPiece i) by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
      exact hz.2
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩]
  exact himage

/-- The restricted genuine inverse chart is measurable. -/
theorem inverseChart_measurable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (i : Fin C.chartCount) :
    Measurable (C.inverseChart i) :=
  (C.inverseChart_isEmbedding i).continuous.measurable

/-- The honest inverse-chart Gram density on a disjointized coordinate
piece. -/
def inverseChartDensity
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount) (z : C.coordinateDomain i) : ℝ :=
  inverseChartPullbackVolumeDensity g (C.anchor i)
    (C.coordinateTargetPoint i z)

/-- Honest inverse-chart Gram densities are nonnegative. -/
theorem inverseChartDensity_nonneg
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount) (z : C.coordinateDomain i) :
    0 ≤ C.inverseChartDensity g i z :=
  VolumeDensity.chartVolumeDensity_nonneg _

/-- The precise variable-metric area formula on one restricted genuine
inverse chart.  This remains an explicit analytic input. -/
def RestrictedInverseChartPullbackHausdorffAreaFormula
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount) : Prop :=
  PullbackMetricHausdorffDensityFormula g (C.coordinateDomain i)
    (C.inverseChart i) (C.inverseChart_isEmbedding i)
    (C.inverseChartDensity g i)

/-- A restricted inverse-chart area formula automatically supplies the local
Hausdorff chart-measure equality for the disjointized manifold piece. -/
theorem hausdorffChartDensityEquality_of_restrictedAreaFormula
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin C.chartCount)
    (harea : C.RestrictedInverseChartPullbackHausdorffAreaFormula g i) :
    HausdorffChartDensityEquality g (C.coordinateDomain i)
      (C.inverseChart i) (C.manifoldPiece i)
      (C.inverseChartDensity g i) := by
  exact hausdorffChartDensityEquality_of_pullbackMetricFormula
    g (C.coordinateDomain i) (C.inverseChart i)
      (C.inverseChart_isEmbedding i) (C.manifoldPiece i)
      (C.inverseChartDensity g i) (C.range_inverseChart i).symm harea

/-- The intrinsic first variation of the restricted honest inverse-chart
density. -/
theorem hasDerivAt_inverseChartDensity
    (C : FiniteExtendedChartCover (n := n) (M := M))
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} (i : Fin C.chartCount) (z : C.coordinateDomain i)
    (hgt : TimeDifferentiableAt gt t₀ (C.inverseChart i z)) :
    HasDerivAt (fun t ↦ C.inverseChartDensity (gt t) i z)
      ((1 / 2 : ℝ) * C.inverseChartDensity (gt t₀) i z *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
          (C.inverseChart i z)) t₀ := by
  exact hasDerivAt_inverseChartPullbackVolumeDensity
    (C.coordinateTargetPoint i z) hgt

end FiniteExtendedChartCover

/-- Area-formula and density-integrability inputs for one time neighborhood
on a fixed compactness-selected finite inverse atlas. -/
structure FiniteExtendedChartFrameMeasureData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (s : Set ℝ) where
  density_integrable : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    Integrable (C.inverseChartDensity (gt t) i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  areaFormula : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    C.RestrictedInverseChartPullbackHausdorffAreaFormula (gt t) i

/-- The finite decomposition bookkeeping is automatic from a finite genuine
inverse-atlas cover.  Only the variable-metric area formula and density
integrability are supplied by `H`. -/
def FiniteExtendedChartFrameMeasureData.toDecomposition
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (H : FiniteExtendedChartFrameMeasureData C gt s) :
    FiniteHausdorffChartDensityDecomposition gt s where
  chartCount := C.chartCount
  coordinateDomain := C.coordinateDomain
  coordinateDomain_measurable := C.coordinateDomain_measurable
  inverseChart := C.inverseChart
  inverseChart_measurable := C.inverseChart_measurable
  manifoldPiece := C.manifoldPiece
  manifoldPiece_measurable := C.manifoldPiece_measurable
  pieces_pairwise := C.manifoldPieces_pairwise
  pieces_cover := C.manifoldPieces_cover
  density := fun t i ↦ C.inverseChartDensity (gt t) i
  density_nonneg := fun t _ht i ↦
    Eventually.of_forall fun z ↦ C.inverseChartDensity_nonneg (gt t) i z
  density_integrable := H.density_integrable
  chartMeasure := fun t ht i ↦
    C.hausdorffChartDensityEquality_of_restrictedAreaFormula
      (gt t) i (H.areaFormula t ht i)

/-- The explicit intrinsic derivative used by dominated differentiation on
the compactness-selected inverse atlas. -/
def finiteExtendedChartFrameDensityDerivative
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (t : ℝ) (i : Fin C.chartCount) (z : C.coordinateDomain i) : ℝ :=
  (1 / 2 : ℝ) * C.inverseChartDensity (gt t) i z *
    traceMetricVariationAt (gt t) (timeDerivAt gt t) (C.inverseChart i z)

/-- The remaining local dominated-differentiation hypotheses.  The density
derivative itself is no longer a witness: it is the explicit intrinsic
inverse-chart derivative above. -/
structure FiniteExtendedChartFrameDensityDominationAt
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (s : Set ℝ) (t₀ : ℝ) where
  timeSet_mem : s ∈ 𝓝 t₀
  densityDerivative_aestronglyMeasurable_at : ∀ i,
    AEStronglyMeasurable
      (finiteExtendedChartFrameDensityDerivative C gt t₀ i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  dominatingFunction :
    (i : Fin C.chartCount) → C.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  densityDerivative_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
      ∀ t ∈ s,
        ‖finiteExtendedChartFrameDensityDerivative C gt t i z‖ ≤
          dominatingFunction i z
  timeDifferentiable : ∀ i (z : C.coordinateDomain i) t,
    t ∈ s → TimeDifferentiableAt gt t (C.inverseChart i z)

/-- The explicit domination data reconstruct the repository's full local
dominated-differentiation package; pointwise density differentiation follows
from the inverse-chart frame theorem. -/
def FiniteExtendedChartFrameDensityDominationAt.toDominatedDifferentiation
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {s : Set ℝ} {t₀ : ℝ}
    (A : FiniteExtendedChartFrameDensityDominationAt C gt s t₀)
    (H : FiniteExtendedChartFrameMeasureData C gt s) :
    FiniteChartDensityDominatedDifferentiationAt H.toDecomposition t₀ where
  timeSet_mem := A.timeSet_mem
  densityDerivative := finiteExtendedChartFrameDensityDerivative C gt
  densityDerivative_aestronglyMeasurable_at :=
    A.densityDerivative_aestronglyMeasurable_at
  dominatingFunction := A.dominatingFunction
  dominatingFunction_integrable := A.dominatingFunction_integrable
  densityDerivative_bound := A.densityDerivative_bound
  hasDerivAt_density := fun i ↦ Eventually.of_forall fun z t ht ↦
    C.hasDerivAt_inverseChartDensity i z (A.timeDifferentiable i z t ht)

/-- Global area-formula and analytic domination data on one fixed finite
genuine inverse atlas. -/
structure GlobalFiniteExtendedChartFrameDensityData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) where
  timeSet : ℝ → Set ℝ
  measureData : ∀ t : ℝ,
    FiniteExtendedChartFrameMeasureData C gt (timeSet t)
  domination : ∀ t : ℝ,
    FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t

/-- The compact finite-atlas reduction: inverse-chart area formulas and
explicit analytic domination construct the corrected global Hausdorff
chart-frame density-variation package. -/
def GlobalFiniteExtendedChartFrameDensityData.toChartFrameDensityVariation
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalFiniteExtendedChartFrameDensityData C gt) :
    GlobalFiniteHausdorffChartFrameDensityVariation gt where
  timeSet := H.timeSet
  decomposition t := (H.measureData t).toDecomposition
  differentiation t :=
    (H.domination t).toDominatedDifferentiation (H.measureData t)
  intrinsicDensityFirstVariation t := by
    intro i z
    exact C.hasDerivAt_inverseChartDensity i z
      ((H.domination t).timeDifferentiable i z t
        (mem_of_mem_nhds (H.domination t).timeSet_mem))
  timeDifferentiable t i z :=
    (H.domination t).timeDifferentiable i z t
      (mem_of_mem_nhds (H.domination t).timeSet_mem)

/-- Analytic data stated on the compactness-chosen finite inverse atlas. -/
abbrev CompactFiniteAtlasChartFrameDensityData
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) :=
  GlobalFiniteExtendedChartFrameDensityData
    (compactFiniteExtendedChartCover (n := n) (M := M)) gt

/-- The user-facing reduction with the finite atlas itself chosen
automatically by compactness. -/
def CompactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : CompactFiniteAtlasChartFrameDensityData gt) :
    GlobalFiniteHausdorffChartFrameDensityVariation gt :=
  GlobalFiniteExtendedChartFrameDensityData.toChartFrameDensityVariation H

end Poincare
