import Poincare.Global.HausdorffInverseChartMeasureTransport

/-!
# Local restriction inequalities on the full inverse-chart target

This module transports the common-radius local squeeze from its small ambient
Euclidean subtype to restrictions of two measures on the full genuine chart
target.  The result is stated in the form needed for countable localization:
on a measurable neighborhood of every coordinate point, fixed scalar
multiples of the pullback Hausdorff measure and the variable coordinate
density measure dominate one another.
-/

noncomputable section

set_option maxHeartbeats 800000

open Bundle MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n)
  ((⊤ : ℕ∞) : WithTop ℕ∞) M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Every point of the full inverse-chart target has a measurable
neighborhood on which the variable density measure and pullback Hausdorff
measure satisfy the direct two-sided epsilon inequalities.

The lower inequality is deliberately left in cancellation-free form.  Both
scalar factors tend to one as `ε → 0`, and this form remains valid even when
a set has infinite mass. -/
theorem exists_inverseChart_local_restriction_measure_squeeze
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
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
    let μ : Measure U := rawHausdorffCoordinateDensityMeasure U
      (inverseChartPullbackVolumeDensity g x₀)
    let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
    let K : ℝ≥0 := C⁻¹
    let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
    letI : EMetricSpace U := pullbackEMetric
    letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
    ∃ W : Set U,
      W ∈ 𝓝 z₀ ∧ MeasurableSet W ∧
        ENNReal.ofReal (1 - ε) •
              (μH[(n : ℝ)] : Measure U).restrict W ≤
            (L : ℝ≥0∞) ^ (n : ℝ) • μ.restrict W ∧
          μ.restrict W ≤
            (ENNReal.ofReal (1 + ε) *
                (K : ℝ≥0∞) ^ (n : ℝ)) •
              (μH[(n : ℝ)] : Measure U).restrict W := by
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
  let μ : Measure U := rawHausdorffCoordinateDensityMeasure U
    (inverseChartPullbackVolumeDensity g x₀)
  let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
  let K : ℝ≥0 := C⁻¹
  let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  rcases exists_inverseChart_local_variableDensity_hausdorff_squeeze
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hlocal⟩
  let V : Set E :=
    (extChartAt I x₀).target ∩ Metric.ball (z₀ : E) r
  have hU : MeasurableSet U :=
    (isOpen_extChartAt_target x₀).measurableSet
  have hV : MeasurableSet V :=
    (isOpen_extChartAt_target x₀).measurableSet.inter
      Metric.isOpen_ball.measurableSet
  have hVU : V ⊆ U := inter_subset_left
  let ι : V → U := Set.inclusion hVU
  let W : Set U := Set.range ι
  have hW_eq_ball : W = Metric.ball z₀ r := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      rw [Metric.mem_ball, Subtype.dist_eq]
      exact Metric.mem_ball.mp w.2.2
    · intro hz
      have hzE : (z : E) ∈ Metric.ball (z₀ : E) r := by
        simpa only [Metric.mem_ball, Subtype.dist_eq] using hz
      let w : V := ⟨(z : E), ⟨z.2, hzE⟩⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      rfl
  have hW : MeasurableSet W := by
    rw [hW_eq_ball]
    exact Metric.isOpen_ball.measurableSet
  have hWnhds : W ∈ 𝓝 z₀ := by
    rw [hW_eq_ball]
    exact Metric.ball_mem_nhds z₀ hr
  have hιEmbedding : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.inclusion hVU
  have hι : MeasurableEmbedding ι := by
    apply hιEmbedding.measurableEmbedding
    exact hW
  let variableDensityMeasure : Measure V :=
    rawHausdorffCoordinateDensityMeasure V
      (fun z ↦ inverseChartPullbackVolumeDensity g x₀
        ⟨(z : E), z.2.1⟩)
  let frozenDensityMeasure : Measure V :=
    rawHausdorffCoordinateDensityMeasure V
      (fun _ ↦ inverseChartPullbackVolumeDensity g x₀ z₀)
  have hrawMap :
      Measure.map ι variableDensityMeasure = μ.restrict W := by
    simpa only [ι, W, variableDensityMeasure, μ, U, V] using
      (map_rawHausdorffCoordinateDensityMeasure_inclusion
        hU hV hVU (inverseChartPullbackVolumeDensity g x₀))
  have hsourceImage : ∀ s : Set U,
      (μH[(n : ℝ)] : Measure U) s = μH[(n : ℝ)] (ψ '' s) := by
    simpa only [U, ψ, hψ, pullbackMetric, pullbackEMetric] using
      (pullbackHausdorffMeasure_eq_inverseChart_image g x₀)
  let ψV : V → M := fun z ↦ (extChartAt I x₀).symm (z : E)
  have hψV : ψV = ψ ∘ ι := by
    funext z
    rfl
  dsimp only at hlocal
  rcases hlocal with ⟨hDensityLower, hDensityUpper, hArea⟩
  refine ⟨W, hWnhds, hW, ?_, ?_⟩
  · apply Measure.le_iff.2
    intro s hs
    let t : Set V := ι ⁻¹' s
    have hrawValue :
        variableDensityMeasure t = μ.restrict W s := by
      have heval := congrArg (fun ν : Measure U ↦ ν s) hrawMap
      change Measure.map ι variableDensityMeasure s = μ.restrict W s at heval
      rw [hι.map_apply] at heval
      exact heval
    have himage : ψ '' (s ∩ W) = ψV '' t := by
      calc
        ψ '' (s ∩ W) = ψ '' (ι '' t) := by
          congr 1
          exact (show ι '' t = s ∩ W by
            simpa only [t, W] using
              (Set.image_preimage_eq_inter_range :
                ι '' (ι ⁻¹' s) = s ∩ Set.range ι)).symm
        _ = (ψ ∘ ι) '' t := Set.image_image ψ ι t
        _ = ψV '' t := by rw [hψV]
    have hhausdorff :
        (μH[(n : ℝ)] : Measure U).restrict W s =
          μH[(n : ℝ)] (ψV '' t) := by
      rw [Measure.restrict_apply hs, hsourceImage, himage]
    have hdensity := hDensityLower t
    simp only [Measure.smul_apply, smul_eq_mul] at hdensity
    have harea := (hArea t).2
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hhausdorff, ← hrawValue]
    calc
      ENNReal.ofReal (1 - ε) * μH[(n : ℝ)] (ψV '' t) ≤
          ENNReal.ofReal (1 - ε) *
            ((L : ℝ≥0∞) ^ (n : ℝ) * frozenDensityMeasure t) :=
        mul_le_mul_left' harea _
      _ = (L : ℝ≥0∞) ^ (n : ℝ) *
          (ENNReal.ofReal (1 - ε) * frozenDensityMeasure t) := by
        ac_rfl
      _ ≤ (L : ℝ≥0∞) ^ (n : ℝ) * variableDensityMeasure t :=
        mul_le_mul_left' hdensity _
  · apply Measure.le_iff.2
    intro s hs
    let t : Set V := ι ⁻¹' s
    have hrawValue :
        variableDensityMeasure t = μ.restrict W s := by
      have heval := congrArg (fun ν : Measure U ↦ ν s) hrawMap
      change Measure.map ι variableDensityMeasure s = μ.restrict W s at heval
      rw [hι.map_apply] at heval
      exact heval
    have himage : ψ '' (s ∩ W) = ψV '' t := by
      calc
        ψ '' (s ∩ W) = ψ '' (ι '' t) := by
          congr 1
          exact (show ι '' t = s ∩ W by
            simpa only [t, W] using
              (Set.image_preimage_eq_inter_range :
                ι '' (ι ⁻¹' s) = s ∩ Set.range ι)).symm
        _ = (ψ ∘ ι) '' t := Set.image_image ψ ι t
        _ = ψV '' t := by rw [hψV]
    have hhausdorff :
        (μH[(n : ℝ)] : Measure U).restrict W s =
          μH[(n : ℝ)] (ψV '' t) := by
      rw [Measure.restrict_apply hs, hsourceImage, himage]
    have hdensity := hDensityUpper t
    simp only [Measure.smul_apply, smul_eq_mul] at hdensity
    have harea := (hArea t).1
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [← hrawValue, hhausdorff]
    calc
      variableDensityMeasure t ≤
          ENNReal.ofReal (1 + ε) * frozenDensityMeasure t := hdensity
      _ ≤ ENNReal.ofReal (1 + ε) *
          ((K : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] (ψV '' t)) :=
        mul_le_mul_left' harea _
      _ = (ENNReal.ofReal (1 + ε) *
          (K : ℝ≥0∞) ^ (n : ℝ)) *
            μH[(n : ℝ)] (ψV '' t) := by
        rw [mul_assoc]

end Poincare
