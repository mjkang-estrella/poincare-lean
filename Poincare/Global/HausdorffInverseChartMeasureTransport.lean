import Poincare.Global.HausdorffInverseChartLocalVariableDensitySqueeze

/-!
# Measure transport for nested inverse-chart domains

The local metric comparison is naturally proved on an ambient Euclidean
subset, whereas the global pullback formula is stated on the full extended
chart target.  This file supplies the two transport identities needed to
move between those presentations:

* raw coordinate-density measure on a measurable nested subtype maps to the
  restriction of the measure on the larger subtype;
* pullback Hausdorff measure on the full chart target evaluates a set as the
  manifold Hausdorff measure of its inverse-chart image.
-/

noncomputable section

open Bundle MeasureTheory Metric Set
open scoped Manifold MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-- A measurable embedding commutes with adding a density pulled back along
that embedding.  No measurability hypothesis on the density is needed: the
embedding form of the `lintegral_map` theorem applies to arbitrary
`ℝ≥0∞`-valued functions. -/
theorem map_withDensity_comp_of_measurableEmbedding
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α)
    (ρ : β → ℝ≥0∞) :
    Measure.map f (μ.withDensity (ρ ∘ f)) =
      (Measure.map f μ).withDensity ρ := by
  ext s hs
  rw [hf.map_apply]
  rw [withDensity_apply _ (hs.preimage hf.measurable),
    withDensity_apply _ hs]
  rw [hf.restrict_map, hf.lintegral_map]
  simp only [Function.comp_apply]

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- Raw Hausdorff-normalized coordinate-density measure is compatible with
restriction to a nested measurable coordinate subtype. -/
theorem map_rawHausdorffCoordinateDensityMeasure_inclusion
    {U V : Set E} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (δ : U → ℝ) :
    Measure.map (Set.inclusion hVU)
        (rawHausdorffCoordinateDensityMeasure V
          (fun z ↦ δ (Set.inclusion hVU z))) =
      (rawHausdorffCoordinateDensityMeasure U δ).restrict
        (Set.range (Set.inclusion hVU)) := by
  let ι : V → U := Set.inclusion hVU
  have hιEmbedding : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.inclusion hVU
  have hι : MeasurableEmbedding ι := by
    apply hιEmbedding.measurableEmbedding
    rw [Set.range_inclusion]
    exact hV.preimage measurable_subtype_coe
  have hbase :
      Measure.map ι (coordinateLebesgueMeasure V) =
        (coordinateLebesgueMeasure U).restrict (Set.range ι) := by
    ext s hs
    rw [hι.map_apply]
    rw [Measure.restrict_apply hs]
    rw [coordinateLebesgueMeasure,
      comap_subtype_coe_apply hV]
    rw [coordinateLebesgueMeasure,
      comap_subtype_coe_apply hU]
    congr 1
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨ι z, ⟨hz, ⟨z, rfl⟩⟩, ?_⟩
      exact Set.coe_inclusion hVU z
    · rintro ⟨z, ⟨hz, ⟨w, hw⟩⟩, rfl⟩
      subst z
      refine ⟨w, hz, ?_⟩
      exact (Set.coe_inclusion hVU w).symm
  let ρ : U → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) * δ z)
  change Measure.map ι
      ((coordinateLebesgueMeasure V).withDensity (ρ ∘ ι)) =
    ((coordinateLebesgueMeasure U).withDensity ρ).restrict
      (Set.range ι)
  rw [map_withDensity_comp_of_measurableEmbedding hι]
  rw [hbase]
  exact (restrict_withDensity hι.measurableSet_range ρ).symm

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n)
  ((⊤ : ℕ∞) : WithTop ℕ∞) M]

local notation "I" => closedSmoothModelWithCorners n

/-- The full inverse extended chart has exactly the genuine chart source as
its range in the manifold. -/
theorem range_inverseExtendedChartParametrization (x₀ : M) :
    Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀) =
      (extChartAt I x₀).source := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    exact
      (inverseExtendedChartHomeomorph
        (n := n) (M := M) x₀ z).2
  · intro x hx
    have htarget :
        (extChartAt I x₀) x ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source hx
    let z : (extChartAt I x₀).target :=
      ⟨(extChartAt I x₀) x, htarget⟩
    refine ⟨z, ?_⟩
    exact (extChartAt I x₀).left_inv hx

/-- Under the metric pulled back by the inverse extended chart, Hausdorff
measure of every source set is the manifold Hausdorff measure of its image.
The assertion is valid for arbitrary sets, not only measurable ones. -/
theorem pullbackHausdorffMeasure_eq_inverseChart_image
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    let U : Set E := (extChartAt I x₀).target
    let ψ : U → M :=
      inverseExtendedChartParametrization (n := n) (M := M) x₀
    letI : MetricSpace M := g.toMetricSpace
    let hψ : Topology.IsEmbedding ψ :=
      inverseExtendedChartParametrization_isEmbedding
        (n := n) (M := M) x₀
    let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
    let pullbackEMetric : EMetricSpace U :=
      @MetricSpace.toEMetricSpace U pullbackMetric
    letI : EMetricSpace U := pullbackEMetric
    letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
    ∀ s : Set U,
      (μH[(n : ℝ)] : Measure U) s = μH[(n : ℝ)] (ψ '' s) := by
  let U : Set E := (extChartAt I x₀).target
  let ψ : U → M :=
    inverseExtendedChartParametrization (n := n) (M := M) x₀
  letI : MetricSpace M := g.toMetricSpace
  let hψ : Topology.IsEmbedding ψ :=
    inverseExtendedChartParametrization_isEmbedding
      (n := n) (M := M) x₀
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  have hψMeas : MeasurableEmbedding ψ := by
    apply hψ.measurableEmbedding
    rw [show Set.range ψ = (extChartAt I x₀).source by
      exact range_inverseExtendedChartParametrization x₀]
    exact (isOpen_extChartAt_source x₀).measurableSet
  have hψiso : Isometry ψ := by
    intro z w
    rfl
  have hmap :
      Measure.map ψ (μH[(n : ℝ)] : Measure U) =
        (μH[(n : ℝ)] : Measure M).restrict (Set.range ψ) := by
    exact hψiso.map_hausdorffMeasure
      (Or.inl (by positivity : (0 : ℝ) ≤ n))
  dsimp only
  intro s
  calc
    (μH[(n : ℝ)] : Measure U) s =
        Measure.map ψ (μH[(n : ℝ)] : Measure U) (ψ '' s) := by
      rw [hψMeas.map_apply]
      rw [Set.preimage_image_eq _ hψMeas.injective]
    _ = (μH[(n : ℝ)] : Measure M).restrict
          (Set.range ψ) (ψ '' s) := by rw [hmap]
    _ = μH[(n : ℝ)] (ψ '' s) :=
      Measure.restrict_eq_self _ (Set.image_subset_range ψ s)

end Poincare
