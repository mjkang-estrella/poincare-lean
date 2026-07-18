import Poincare.Global.HausdorffInverseChartLocalAreaSandwich
import Poincare.Global.HausdorffCoordinateDensityComparison

/-!
# Local variable-density Hausdorff squeeze

The frozen inverse-chart metric gives an exact constant-density coordinate
area measure.  Continuity of the actual pullback volume density lets us shrink
the same coordinate ball once more so that the variable-density measure is
trapped between the `(1 - ε)` and `(1 + ε)` scalar multiples of that frozen
measure.

Combining this pointwise density comparison with the local bi-Lipschitz area
sandwich produces one neighborhood carrying all four inequalities needed for
the eventual localization-and-squeeze proof of the inverse-chart Hausdorff
area formula.
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

/-- On one sufficiently small inverse-chart ball, the variable coordinate
density measure is relatively close to the exact frozen coordinate measure,
and the latter is simultaneously bi-Lipschitz comparable with manifold
Hausdorff measure.

The first two conclusions are inequalities of measures, so they apply without
an extra measurability assumption on a chosen set.  The final two inequalities
hold for every set in the common coordinate source. -/
theorem exists_inverseChart_local_variableDensity_hausdorff_squeeze
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0,
      let V : Set E :=
        (extChartAt I x₀).target ∩ Metric.ball (z₀ : E) r
      let toTarget : V → (extChartAt I x₀).target :=
        fun z ↦ ⟨(z : E), z.2.1⟩
      let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
      let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
      let e := positiveDefiniteGramLinearEquiv G₀ hG₀
      let φ := linearPullbackParametrization e V
      let hφ := linearPullbackParametrization_isEmbedding e V
      let frozenMetric : MetricSpace V := hφ.comapMetricSpace φ
      let frozenEMetric : EMetricSpace V :=
        @MetricSpace.toEMetricSpace V frozenMetric
      let ψ : V → M := fun z ↦ (extChartAt I x₀).symm (z : E)
      let frozenDensityMeasure : Measure V :=
        rawHausdorffCoordinateDensityMeasure V
          (fun _ ↦ inverseChartPullbackVolumeDensity g x₀ z₀)
      let variableDensityMeasure : Measure V :=
        rawHausdorffCoordinateDensityMeasure V
          (fun z ↦ inverseChartPullbackVolumeDensity g x₀ (toTarget z))
      let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
      let K : ℝ≥0 := C⁻¹
      let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
      letI : EMetricSpace V := frozenEMetric
      letI : PseudoEMetricSpace V := frozenEMetric.toPseudoEMetricSpace
      letI : MetricSpace M := g.toMetricSpace
      ENNReal.ofReal (1 - ε) • frozenDensityMeasure ≤
          variableDensityMeasure ∧
        variableDensityMeasure ≤
          ENNReal.ofReal (1 + ε) • frozenDensityMeasure ∧
        ∀ s : Set V,
          frozenDensityMeasure s ≤
              (K : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] (ψ '' s) ∧
            μH[(n : ℝ)] (ψ '' s) ≤
              (L : ℝ≥0∞) ^ (n : ℝ) * frozenDensityMeasure s := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChart_frozenEDist_le_riemannianEDist
      g x₀ z₀ hε0 hε1 with ⟨rLower, hrLower, hLower⟩
  rcases exists_inverseChart_riemannianEDist_le_frozenEDist
      g x₀ z₀ hε0 hε1 with ⟨rUpper, hrUpper, hUpper⟩
  rcases Metric.eventually_nhds_iff.mp
      (inverseChartPullbackVolumeDensity_eventually_relative_bounds
        g x₀ z₀ hε0) with ⟨rDensity, hrDensity, hDensity⟩
  let r := min rLower (min rUpper rDensity)
  have hr : 0 < r := lt_min hrLower (lt_min hrUpper hrDensity)
  refine ⟨r, hr, ?_⟩
  let V : Set E :=
    (extChartAt I x₀).target ∩ Metric.ball (z₀ : E) r
  have hV : MeasurableSet V :=
    (isOpen_extChartAt_target x₀).measurableSet.inter
      Metric.isOpen_ball.measurableSet
  let toTarget : V → (extChartAt I x₀).target :=
    fun z ↦ ⟨(z : E), z.2.1⟩
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  let φ := linearPullbackParametrization e V
  let hφ := linearPullbackParametrization_isEmbedding e V
  let frozenMetric : MetricSpace V := hφ.comapMetricSpace φ
  let frozenEMetric : EMetricSpace V :=
    @MetricSpace.toEMetricSpace V frozenMetric
  let ψ : V → M := fun z ↦ (extChartAt I x₀).symm (z : E)
  let frozenDensityMeasure : Measure V :=
    rawHausdorffCoordinateDensityMeasure V
      (fun _ ↦ inverseChartPullbackVolumeDensity g x₀ z₀)
  let variableDensityMeasure : Measure V :=
    rawHausdorffCoordinateDensityMeasure V
      (fun z ↦ inverseChartPullbackVolumeDensity g x₀ (toTarget z))
  let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
  let K : ℝ≥0 := C⁻¹
  let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
  have hrLower' : r ≤ rLower := min_le_left _ _
  have hrUpper' : r ≤ rUpper :=
    (min_le_right rLower (min rUpper rDensity)).trans
      (min_le_left rUpper rDensity)
  have hrDensity' : r ≤ rDensity :=
    (min_le_right rLower (min rUpper rDensity)).trans
      (min_le_right rUpper rDensity)
  have hDensityPointwise : ∀ z : V,
      (1 - ε) * inverseChartPullbackVolumeDensity g x₀ z₀ ≤
          inverseChartPullbackVolumeDensity g x₀ (toTarget z) ∧
        inverseChartPullbackVolumeDensity g x₀ (toTarget z) ≤
          (1 + ε) * inverseChartPullbackVolumeDensity g x₀ z₀ := by
    intro z
    have hzDensity : dist (toTarget z) z₀ < rDensity := by
      rw [Subtype.dist_eq]
      exact (Metric.mem_ball.mp z.2.2).trans_le hrDensity'
    have hz := hDensity hzDensity
    exact ⟨hz.1.le, hz.2.le⟩
  have hDensityMeasures :
      ENNReal.ofReal (1 - ε) • frozenDensityMeasure ≤
          variableDensityMeasure ∧
        variableDensityMeasure ≤
          ENNReal.ofReal (1 + ε) • frozenDensityMeasure := by
    exact rawHausdorffCoordinateDensityMeasure_relative_bounds
      V
      (fun z ↦ inverseChartPullbackVolumeDensity g x₀ (toTarget z))
      (inverseChartPullbackVolumeDensity g x₀ z₀)
      (1 - ε) (1 + ε)
      (sub_nonneg.mpr hε1.le) (by linarith) hDensityPointwise
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
  letI : EMetricSpace V := frozenEMetric
  letI : PseudoEMetricSpace V := frozenEMetric.toPseudoEMetricSpace
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  have hφiso : Isometry φ := by
    intro z w
    rfl
  have hfrozen : ∀ z w : V,
      frozenInverseChartEDist g x₀ z₀ (toTarget z) (toTarget w) =
        @edist V frozenEMetric.toEDist z w := by
    intro z w
    rw [show frozenInverseChartEDist g x₀ z₀
          (toTarget z) (toTarget w) = edist (φ w) (φ z) by
      simp only [frozenInverseChartEDist, toTarget, φ, G₀, hG₀, e,
        linearPullbackParametrization, edist_eq_enorm_sub, map_sub]]
    rw [edist_comm, hφiso.edist_eq]
  have htarget : ∀ z w : V,
      edist (ψ z) (ψ w) =
        Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (toTarget z : E))
          ((extChartAt I x₀).symm (toTarget w : E)) := by
    intro z w
    exact GeodesicTransport.induced_edist_eq_riemannianEDist
      (g := g) (ψ z) (ψ w)
  have hanti : @AntilipschitzWith V M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace K ψ := by
    intro z w
    have hzLower : dist (toTarget z) z₀ < rLower := by
      rw [Subtype.dist_eq]
      exact (Metric.mem_ball.mp z.2.2).trans_le hrLower'
    have hwLower : dist (toTarget w) z₀ < rLower := by
      rw [Subtype.dist_eq]
      exact (Metric.mem_ball.mp w.2.2).trans_le hrLower'
    have hriem := hLower (toTarget z) (toTarget w) hzLower hwLower
    have hlower :
        (C : ℝ≥0∞) * @edist V frozenEMetric.toEDist z w ≤
          edist (ψ z) (ψ w) := by
      calc
        (C : ℝ≥0∞) * @edist V frozenEMetric.toEDist z w =
            ENNReal.ofReal (Real.sqrt (1 - ε)) *
              frozenInverseChartEDist g x₀ z₀
                (toTarget z) (toTarget w) := by
          rw [hcoefLower, hfrozen z w]
        _ ≤ Manifold.riemannianEDist I
              ((extChartAt I x₀).symm (toTarget z : E))
              ((extChartAt I x₀).symm (toTarget w : E)) := hriem
        _ = edist (ψ z) (ψ w) := (htarget z w).symm
    have hCzero : (C : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hCpos.ne'
    have hKcoe : (K : ℝ≥0∞) = (C : ℝ≥0∞)⁻¹ := by
      exact ENNReal.coe_inv hCpos.ne'
    calc
      @edist V frozenEMetric.toEDist z w = (C : ℝ≥0∞)⁻¹ *
          ((C : ℝ≥0∞) * @edist V frozenEMetric.toEDist z w) := by
        exact (ENNReal.inv_mul_cancel_left hCzero ENNReal.coe_ne_top).symm
      _ ≤ (C : ℝ≥0∞)⁻¹ * edist (ψ z) (ψ w) :=
        mul_le_mul_left' hlower _
      _ = (K : ℝ≥0∞) * edist (ψ z) (ψ w) := by
        rw [hKcoe]
  have hlip : @LipschitzWith V M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace L ψ := by
    intro z w
    have hzUpper : dist (toTarget z) z₀ < rUpper := by
      rw [Subtype.dist_eq]
      exact (Metric.mem_ball.mp z.2.2).trans_le hrUpper'
    have hwUpper : dist (toTarget w) z₀ < rUpper := by
      rw [Subtype.dist_eq]
      exact (Metric.mem_ball.mp w.2.2).trans_le hrUpper'
    have hriem := hUpper (toTarget z) (toTarget w) hzUpper hwUpper
    calc
      edist (ψ z) (ψ w) =
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (toTarget z : E))
            ((extChartAt I x₀).symm (toTarget w : E)) := htarget z w
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + ε)) *
          frozenInverseChartEDist g x₀ z₀
            (toTarget z) (toTarget w) := hriem
      _ = (L : ℝ≥0∞) * @edist V frozenEMetric.toEDist z w := by
        rw [hcoefUpper, hfrozen z w]
  have harea :
      (μH[(n : ℝ)] : Measure V) = frozenDensityMeasure := by
    have hrawArea := positiveDefiniteConstantGramHausdorffAreaFormula
      hV G₀ hG₀
    simpa only [frozenDensityMeasure,
      inverseChartPullbackVolumeDensity] using hrawArea
  dsimp only
  refine ⟨hDensityMeasures.1, hDensityMeasures.2, ?_⟩
  intro s
  have hsandwich := hausdorffMeasure_image_bilipschitz_bounds
    (d := (n : ℝ)) hanti hlip (by positivity) s
  rw [harea] at hsandwich
  exact hsandwich

end Poincare
