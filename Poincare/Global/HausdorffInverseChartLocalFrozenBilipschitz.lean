import Poincare.Global.HausdorffInverseChartLocalFrozenLower

/-!
# Local frozen-metric bi-Lipschitz and Hausdorff sandwich

The upper and lower inverse-chart comparisons are first placed on one common
target ball.  That ball is equipped with the metric pulled back by the frozen
positive Gram factor.  The genuine inverse chart is then simultaneously
`sqrt (1 + ε)`-Lipschitz and `(sqrt (1 - ε))⁻¹`-anti-Lipschitz.

The final statement records both Mathlib Hausdorff inequalities on every
subset of the common ball.  It is the precise local epsilon sandwich needed
to compare the variable Riemannian Hausdorff measure with the exact frozen
constant-density model.
-/

noncomputable section

set_option maxHeartbeats 800000

open Bundle Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- On one sufficiently small inverse-chart ball, the genuine inverse chart
has both sharp frozen comparison constants.  The two resulting Hausdorff
inequalities hold simultaneously for every subset of that ball. -/
theorem exists_inverseChart_frozen_bilipschitzWith_and_hausdorff_sandwich
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0,
      let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
      let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
      let hφ :=
        frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
      let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
      let frozenEMetric : EMetricSpace U :=
        @MetricSpace.toEMetricSpace U frozenMetric
      let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
      let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
      let K : ℝ≥0 := C⁻¹
      let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
      letI : EMetricSpace U := frozenEMetric
      letI : PseudoEMetricSpace U := frozenEMetric.toPseudoEMetricSpace
      letI : MetricSpace M := g.toMetricSpace
      @AntilipschitzWith U M frozenEMetric.toPseudoEMetricSpace
          g.toEMetricSpace.toPseudoEMetricSpace K ψ ∧
        @LipschitzWith U M frozenEMetric.toPseudoEMetricSpace
          g.toEMetricSpace.toPseudoEMetricSpace L ψ ∧
        ∀ s : Set U,
          μH[(n : ℝ)] s ≤
              (K : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] (ψ '' s) ∧
            μH[(n : ℝ)] (ψ '' s) ≤
              (L : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] s := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChart_frozenEDist_le_riemannianEDist
      g x₀ z₀ hε0 hε1 with ⟨rLower, hrLower, hLower⟩
  rcases exists_inverseChart_riemannianEDist_le_frozenEDist
      g x₀ z₀ hε0 hε1 with ⟨rUpper, hrUpper, hUpper⟩
  let r := min rLower rUpper
  have hr : 0 < r := lt_min hrLower hrUpper
  refine ⟨r, hr, ?_⟩
  let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
  let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
  let hφ :=
    frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
  let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
  let frozenEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U frozenMetric
  let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
  let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
  let K : ℝ≥0 := C⁻¹
  let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
  have hCpos : 0 < C := by
    change 0 < Real.sqrt (1 - ε)
    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
  have hcoefLower :
      ENNReal.ofReal (Real.sqrt (1 - ε)) = (C : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)]
    apply ENNReal.coe_inj.mpr
    apply Subtype.ext
    rfl
  have hcoefUpper :
      ENNReal.ofReal (Real.sqrt (1 + ε)) = (L : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)]
    apply ENNReal.coe_inj.mpr
    apply Subtype.ext
    rfl
  letI : EMetricSpace U := frozenEMetric
  letI : PseudoEMetricSpace U := frozenEMetric.toPseudoEMetricSpace
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  have hφiso : Isometry φ := by
    intro z w
    rfl
  have hfrozen : ∀ z w : U,
      frozenInverseChartEDist g x₀ z₀ z.1 w.1 =
        @edist U frozenEMetric.toEDist z w := by
    intro z w
    rw [show frozenInverseChartEDist g x₀ z₀ z.1 w.1 =
        edist (φ w) (φ z) by
      simp only [frozenInverseChartEDist, φ,
        frozenInverseChartLinearParametrizationAt,
        edist_eq_enorm_sub, map_sub]]
    rw [edist_comm, hφiso.edist_eq]
  have htarget : ∀ z w : U,
      edist (ψ z) (ψ w) =
        Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (z.1 : E))
          ((extChartAt I x₀).symm (w.1 : E)) := by
    intro z w
    exact GeodesicTransport.induced_edist_eq_riemannianEDist
      (g := g) (ψ z) (ψ w)
  have hanti : @AntilipschitzWith U M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace K ψ := by
    intro z w
    have hzLower : dist z.1 z₀ < rLower :=
      z.2.trans_le (min_le_left rLower rUpper)
    have hwLower : dist w.1 z₀ < rLower :=
      w.2.trans_le (min_le_left rLower rUpper)
    have hriem := hLower z.1 w.1 hzLower hwLower
    have hlower :
        (C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w ≤
          edist (ψ z) (ψ w) := by
      calc
        (C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w =
            ENNReal.ofReal (Real.sqrt (1 - ε)) *
              frozenInverseChartEDist g x₀ z₀ z.1 w.1 := by
          rw [hcoefLower, hfrozen z w]
        _ ≤ Manifold.riemannianEDist I
              ((extChartAt I x₀).symm (z.1 : E))
              ((extChartAt I x₀).symm (w.1 : E)) := hriem
        _ = edist (ψ z) (ψ w) := (htarget z w).symm
    have hCzero : (C : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hCpos.ne'
    have hKcoe : (K : ℝ≥0∞) = (C : ℝ≥0∞)⁻¹ := by
      exact ENNReal.coe_inv hCpos.ne'
    calc
      @edist U frozenEMetric.toEDist z w = (C : ℝ≥0∞)⁻¹ *
          ((C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w) := by
        exact (ENNReal.inv_mul_cancel_left hCzero ENNReal.coe_ne_top).symm
      _ ≤ (C : ℝ≥0∞)⁻¹ * edist (ψ z) (ψ w) :=
        mul_le_mul_left' hlower _
      _ = (K : ℝ≥0∞) * edist (ψ z) (ψ w) := by
        rw [hKcoe]
  have hlip : @LipschitzWith U M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace L ψ := by
    intro z w
    have hzUpper : dist z.1 z₀ < rUpper :=
      z.2.trans_le (min_le_right rLower rUpper)
    have hwUpper : dist w.1 z₀ < rUpper :=
      w.2.trans_le (min_le_right rLower rUpper)
    have hriem := hUpper z.1 w.1 hzUpper hwUpper
    calc
      edist (ψ z) (ψ w) =
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (z.1 : E))
            ((extChartAt I x₀).symm (w.1 : E)) := htarget z w
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + ε)) *
          frozenInverseChartEDist g x₀ z₀ z.1 w.1 := hriem
      _ = (L : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w := by
        rw [hcoefUpper, hfrozen z w]
  refine ⟨hanti, hlip, ?_⟩
  intro s
  exact hausdorffMeasure_image_bilipschitz_bounds
    hanti hlip (by positivity) s

end Poincare
