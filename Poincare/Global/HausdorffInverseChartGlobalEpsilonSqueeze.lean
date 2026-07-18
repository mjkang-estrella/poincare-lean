import Poincare.Global.HausdorffMeasureCountableLocalization

/-!
# Global epsilon bounds for inverse-chart Hausdorff measure

The pointwise common-radius comparison has already been transported to
restriction inequalities on the full inverse-chart target.  Second
countability now globalizes those inequalities without requiring a finite
subcover or finiteness of either measure.
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

/-- For every fixed `0 < ε < 1`, the local inverse-chart measure
comparisons globalize to the entire genuine chart target.  The constants
are kept in the cancellation-free form needed when one of the measures has
infinite mass. -/
theorem inverseChart_global_measure_squeeze
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {ε : ℝ}
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
    ENNReal.ofReal (1 - ε) •
          (μH[(n : ℝ)] : Measure U) ≤
        (L : ℝ≥0∞) ^ (n : ℝ) • μ ∧
      μ ≤
        (ENNReal.ofReal (1 + ε) *
            (K : ℝ≥0∞) ^ (n : ℝ)) •
          (μH[(n : ℝ)] : Measure U) := by
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
  constructor
  · apply measure_le_of_restrict_le_on_nhds
    intro z
    rcases exists_inverseChart_local_restriction_measure_squeeze
        g x₀ z hε0 hε1 with ⟨W, hWnhds, hWmeas, hlo, _hup⟩
    refine ⟨W, hWnhds, hWmeas, ?_⟩
    simpa only [Measure.restrict_smul] using hlo
  · apply measure_le_of_restrict_le_on_nhds
    intro z
    rcases exists_inverseChart_local_restriction_measure_squeeze
        g x₀ z hε0 hε1 with ⟨W, hWnhds, hWmeas, _hlo, hup⟩
    refine ⟨W, hWnhds, hWmeas, ?_⟩
    simpa only [Measure.restrict_smul] using hup

end Poincare
