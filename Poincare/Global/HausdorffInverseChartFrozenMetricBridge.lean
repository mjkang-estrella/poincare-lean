import Poincare.Global.HausdorffRiemannianShortPathConfinement
import Poincare.Global.AntilipschitzBall
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Frozen inverse-chart metric bridge

This file connects the quadratic form used in the local path-length
comparison to the positive square-root linear equivalence used in the exact
frozen Hausdorff area formula.

The first result identifies frozen speed exactly with the norm after applying
`positiveDefiniteGramLinearEquiv`.  Consequently, the frozen speed integral
of a `C¹` coordinate curve dominates the frozen linear distance between its
endpoints.  Combining that endpoint estimate with the genuine Riemannian
path-length comparison gives the sharp chart-confined lower bound needed for
the anti-Lipschitz half of a local metric comparison.

The final theorem packages Mathlib's two Hausdorff-measure estimates for a
map for which the Lipschitz and anti-Lipschitz halves have been established.
Short-path confinement is available from the imported module to promote the
chart-confined path estimate to unrestricted local distance once the
coordinate lift of an arbitrary confined manifold path is supplied.
-/

noncomputable section

open Bundle Filter Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

universe u v

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- At the freezing point, the inverse-chart Gram quadratic form is the
squared norm after applying the canonical positive-definite Gram factor. -/
theorem inverseChartPullbackQuadraticForm_eq_norm_sq_frozenLinearEquiv
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) (v : E) :
    let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
    let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
    let e := positiveDefiniteGramLinearEquiv G₀ hG₀
    inverseChartPullbackQuadraticForm g x₀ z₀ (fun i ↦ v i) =
      ‖e v‖ ^ 2 := by
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  let A := linearPullbackCoordinateMatrix e
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let a : Fin n → ℝ := fun i ↦ v i
  have heGram : linearPullbackGramMatrix e = G₀ :=
    linearPullbackGramMatrix_positiveDefiniteGramLinearEquiv G₀ hG₀
  have hrepr : b.repr v = a := by
    funext i
    rfl
  have hAv : A *ᵥ a = (fun i ↦ e v i) := by
    change
      LinearMap.toMatrix b b (e : E →ₗ[ℝ] E) *ᵥ a =
        (fun i ↦ e v i)
    rw [← hrepr, LinearMap.toMatrix_mulVec_repr]
    rfl
  have hdot :
      (fun i ↦ e v i) ⬝ᵥ (fun i ↦ e v i) = ‖e v‖ ^ 2 := by
    simpa only [star_trivial, real_inner_self_eq_norm_sq] using
      (EuclideanSpace.inner_eq_star_dotProduct (e v) (e v)).symm
  calc
    inverseChartPullbackQuadraticForm g x₀ z₀ (fun i ↦ v i) =
        a ⬝ᵥ (G₀ *ᵥ a) := by
      rfl
    _ = a ⬝ᵥ (linearPullbackGramMatrix e *ᵥ a) := by
      rw [heGram]
    _ = a ⬝ᵥ ((Matrix.transpose A * A) *ᵥ a) := by
      rw [linearPullbackGramMatrix_eq_transpose_mul]
    _ = a ⬝ᵥ (Matrix.transpose A *ᵥ (A *ᵥ a)) := by
      rw [Matrix.mulVec_mulVec]
    _ = (A *ᵥ a) ⬝ᵥ (A *ᵥ a) := by
      exact Matrix.dotProduct_transpose_mulVec A a (A *ᵥ a)
    _ = ‖e v‖ ^ 2 := by
      rw [hAv, hdot]

/-- Frozen quadratic speed is exactly the Euclidean norm after applying the
Gram factor used in the frozen Hausdorff area formula. -/
theorem sqrt_inverseChartPullbackQuadraticForm_eq_norm_frozenLinearEquiv
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) (v : E) :
    let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
    let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
    let e := positiveDefiniteGramLinearEquiv G₀ hG₀
    Real.sqrt
        (inverseChartPullbackQuadraticForm g x₀ z₀ (fun i ↦ v i)) =
      ‖e v‖ := by
  rw [inverseChartPullbackQuadraticForm_eq_norm_sq_frozenLinearEquiv]
  exact Real.sqrt_sq (norm_nonneg _)

/-- The extended distance in the frozen linear pullback model, written
without installing a second metric instance on the chart target. -/
noncomputable def frozenInverseChartEDist
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ z w : (extChartAt I x₀).target) : ℝ≥0∞ :=
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  ‖e ((w : E) - (z : E))‖ₑ

/-- The frozen speed integral of a `C¹` coordinate curve dominates the
frozen linear distance between its endpoints. -/
theorem frozenInverseChartEDist_le_frozenSpeedIntegral
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target)
    (z : ℝ → (extChartAt I x₀).target) (v : ℝ → E)
    {a b : ℝ} (hab : a ≤ b)
    (hzcont : ContDiffOn ℝ 1 (fun t : ℝ ↦ (z t : E)) (Icc a b))
    (hzder : ∀ t ∈ Ioo a b,
      HasDerivAt (fun s : ℝ ↦ (z s : E)) (v t) t) :
    frozenInverseChartEDist g x₀ z₀ (z a) (z b) ≤
      frozenInverseChartSpeedIntegral g x₀ z₀ v a b := by
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  let f : ℝ → E := fun t ↦ e (z t : E)
  have hfcont : ContDiffOn ℝ 1 f (Icc a b) :=
    e.contDiff.comp_contDiffOn hzcont
  have hendpoint :=
    enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hfcont hab
  calc
    frozenInverseChartEDist g x₀ z₀ (z a) (z b) =
        ‖f b - f a‖ₑ := by
      simp only [frozenInverseChartEDist, f, G₀, hG₀, e, map_sub]
    _ ≤ ∫⁻ t in Icc a b, ‖derivWithin f (Icc a b) t‖ₑ := hendpoint
    _ = ∫⁻ t in Ioo a b,
        ENNReal.ofReal
          (Real.sqrt
            (inverseChartPullbackQuadraticForm g x₀ z₀
              (fun i ↦ v t i))) := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      change ‖derivWithin f (Icc a b) t‖ₑ =
        ENNReal.ofReal
          (Real.sqrt
            (inverseChartPullbackQuadraticForm g x₀ z₀
              (fun i ↦ v t i)))
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      have hfder : HasDerivAt f (e (v t)) t := by
        exact e.hasFDerivAt.comp_hasDerivAt t (hzder t ht)
      rw [hfder.deriv]
      rw [sqrt_inverseChartPullbackQuadraticForm_eq_norm_frozenLinearEquiv]
      exact (ofReal_norm_eq_enorm (e (v t))).symm
    _ = frozenInverseChartSpeedIntegral g x₀ z₀ v a b := by
      rfl

/-- A chart-confined inverse-chart curve has genuine Riemannian length at
least `sqrt (1 - ε)` times the frozen linear distance of its endpoints. -/
theorem exists_inverseChartCurve_pathELength_ge_frozenEndpoint
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0, ∀ (z : ℝ → (extChartAt I x₀).target) (v : ℝ → E)
      {a b : ℝ},
      a ≤ b →
      (∀ t ∈ Ioo a b, dist (z t) z₀ < r) →
      ContDiffOn ℝ 1 (fun t : ℝ ↦ (z t : E)) (Icc a b) →
      (∀ t ∈ Ioo a b,
        HasDerivAt (fun s : ℝ ↦ (z s : E)) (v t) t) →
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ENNReal.ofReal (Real.sqrt (1 - ε)) *
          frozenInverseChartEDist g x₀ z₀ (z a) (z b) ≤
        Manifold.pathELength I
          (fun t : ℝ ↦ (extChartAt I x₀).symm (z t : E)) a b := by
  rcases exists_inverseChartCurve_pathELength_relative_bounds
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hcompare⟩
  refine ⟨r, hr, ?_⟩
  intro z v a b hab hstay hzcont hzder
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  have hendpoint := frozenInverseChartEDist_le_frozenSpeedIntegral
    g x₀ z₀ z v hab hzcont hzder
  have hlower := (hcompare z v a b hstay hzder).1
  exact (mul_le_mul_left' hendpoint _).trans hlower

/-- The standard Hausdorff-measure sandwich supplied by Mathlib for a
bi-Lipschitz map.  This is the exact measure-level API consumed once the
local inverse chart has been given its frozen source metric and the two local
distance bounds have been proved. -/
theorem hausdorffMeasure_image_bilipschitz_bounds
    {X : Type u} {Y : Type v}
    [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y]
    {K L : ℝ≥0} {f : X → Y} {d : ℝ}
    (hanti : AntilipschitzWith K f) (hlip : LipschitzWith L f)
    (hd : 0 ≤ d) (s : Set X) :
    μH[d] s ≤ (K : ℝ≥0∞) ^ d * μH[d] (f '' s) ∧
      μH[d] (f '' s) ≤ (L : ℝ≥0∞) ^ d * μH[d] s := by
  exact ⟨hanti.le_hausdorffMeasure_image hd s,
    hlip.hausdorffMeasure_image_le hd s⟩

end Poincare
