import Poincare.Global.HausdorffInverseChartLocalFrozenUpper

/-!
# Local frozen-metric Lipschitz and Hausdorff upper bounds

The sharp upper extended-distance estimate is repackaged here in Mathlib's
`LipschitzWith` interface.  The source ball is equipped with the metric
pulled back by the positive Gram-factor equivalence, exactly the same frozen
metric used by `frozenInverseChartPullbackHausdorffAreaFormulaAt`.

Mathlib's Hausdorff theorem then gives, on every subset of this local source
ball, the upper measure distortion factor `(sqrt (1 + ε)) ^ n`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Bundle Filter Matrix MeasureTheory Metric Set
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

/-- The frozen Gram-factor parametrization on an arbitrary subset of the
genuine inverse-chart target. -/
noncomputable def frozenInverseChartLinearParametrizationAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target)
    (U : Set (extChartAt I x₀).target) : U → E :=
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  fun z ↦ e (z.1 : E)

/-- The frozen Gram-factor parametrization is a topological embedding. -/
theorem frozenInverseChartLinearParametrizationAt_isEmbedding
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target)
    (U : Set (extChartAt I x₀).target) :
    Topology.IsEmbedding
      (frozenInverseChartLinearParametrizationAt g x₀ z₀ U) := by
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  have hU : Topology.IsEmbedding
      ((↑) : U → (extChartAt I x₀).target) :=
    Topology.IsEmbedding.subtypeVal
  have htarget : Topology.IsEmbedding
      ((↑) : (extChartAt I x₀).target → E) :=
    Topology.IsEmbedding.subtypeVal
  exact e.toHomeomorph.isEmbedding.comp (htarget.comp hU)

/-- The genuine inverse-chart parametrization on a subset of its target. -/
def inverseChartParametrizationOn
    (x₀ : M) (U : Set (extChartAt I x₀).target) : U → M :=
  fun z ↦ (extChartAt I x₀).symm (z.1 : E)

/-- On a sufficiently small target ball, the genuine inverse-chart map is
`sqrt (1 + ε)`-Lipschitz from the frozen Gram-factor metric to the actual
Riemannian metric.  Hence its image satisfies the corresponding Hausdorff
measure upper bound on every subset. -/
theorem exists_inverseChart_frozen_lipschitzWith_and_hausdorff_upper
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0,
      let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
      let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
      let hφ := frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
      let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
      let frozenEMetric : EMetricSpace U :=
        @MetricSpace.toEMetricSpace U frozenMetric
      let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
      let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
      letI : EMetricSpace U := frozenEMetric
      letI : PseudoEMetricSpace U := frozenEMetric.toPseudoEMetricSpace
      letI : MetricSpace M := g.toMetricSpace
      @LipschitzWith U M frozenEMetric.toPseudoEMetricSpace
          g.toEMetricSpace.toPseudoEMetricSpace L ψ ∧
        ∀ s : Set U,
          μH[(n : ℝ)] (ψ '' s) ≤
            (L : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] s := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChart_riemannianEDist_le_frozenEDist
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hupper⟩
  refine ⟨r, hr, ?_⟩
  let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
  let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
  let hφ := frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
  let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
  let frozenEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U frozenMetric
  let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
  let L : ℝ≥0 := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩
  have hcoef : ENNReal.ofReal (Real.sqrt (1 + ε)) = (L : ℝ≥0∞) := by
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
  have hlip : @LipschitzWith U M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace L ψ := by
    intro z w
    have hup := hupper z.1 w.1 z.2 w.2
    have htarget :
        edist (ψ z) (ψ w) =
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (z.1 : E))
            ((extChartAt I x₀).symm (w.1 : E)) := by
      exact GeodesicTransport.induced_edist_eq_riemannianEDist
        (g := g) (ψ z) (ψ w)
    calc
      edist (ψ z) (ψ w) =
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (z.1 : E))
            ((extChartAt I x₀).symm (w.1 : E)) := htarget
      _ ≤ ENNReal.ofReal (Real.sqrt (1 + ε)) *
          frozenInverseChartEDist g x₀ z₀ z.1 w.1 := hup
      _ = (L : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w := by
        rw [show frozenInverseChartEDist g x₀ z₀ z.1 w.1 =
            edist (φ w) (φ z) by
          simp only [frozenInverseChartEDist, φ,
            frozenInverseChartLinearParametrizationAt,
            edist_eq_enorm_sub, map_sub]]
        rw [edist_comm, hφiso.edist_eq]
        rw [hcoef]
  refine ⟨hlip, ?_⟩
  intro s
  exact hlip.hausdorffMeasure_image_le (by positivity) s

end Poincare
