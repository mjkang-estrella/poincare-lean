import Poincare.Global.GeodesicDistance
import Poincare.Global.GeodesicLength

/-!
# Local lower distance estimates

This module records verified lower-bound pieces for the local distance
realization thread.  The main unconditional result here is an exit estimate:
after fixing any positive chart radius around an anchor, every `C¹` path from
the anchor to a point outside the inverse image of that chart ball has
uniformly positive `pathELength`.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology ENNReal NNReal RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Pointwise integrand lower comparison for an inverse-chart curve.  Once a
chart-metric lower eigenvalue estimate has supplied the real inequality in
`hbound`, this turns it into the exact `pathELength` integrand comparison.
-/
theorem inverseChartCurve_enorm_mfderiv_ge_of_chartMetric_sqrt_lower
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ℝ → E} {u : E} {s lam : ℝ}
    (hz : z s ∈ (extChartAt I x₀).target)
    (hzder : HasDerivAt z u s)
    (hbound :
      lam * ‖u‖ ≤
        Real.sqrt (CovariantDerivative.chartMetric g.inner x₀ (z s) u u)) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ENNReal.ofReal (lam * ‖u‖) ≤
      ‖mfderiv 𝓘(ℝ) I
          (fun r : ℝ => (extChartAt I x₀).symm (z r)) s 1‖ₑ := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [inverseChartCurve_enorm_mfderiv_eq_chartMetric
    (g := g) (x₀ := x₀) hz hzder]
  exact ENNReal.ofReal_le_ofReal hbound

variable [T2Space M] [CompactSpace M]

/--
For any positive chart radius, there is a positive length threshold below
which no `C¹` path starting at the anchor can end outside the inverse-chart
image of that ball.
-/
theorem chart_ball_exit_pathELength_lower_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {r : ℝ} (hr : 0 < r) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ {γ : ℝ → M} {a b : ℝ} {y : M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b) →
        γ a = x₀ →
        γ b = y →
        a ≤ b →
        y ∉ (extChartAt I x₀).symm ''
          Metric.ball ((extChartAt I x₀) x₀) r →
        (c : ℝ≥0∞) ≤ Manifold.pathELength I γ a b := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  let s : Set M :=
    (extChartAt I x₀).symm '' Metric.ball ((extChartAt I x₀) x₀) r
  have hs : s ∈ 𝓝 x₀ := by
    have hpre :
        (extChartAt I x₀) ⁻¹'
            Metric.ball ((extChartAt I x₀) x₀) r ∈ 𝓝 x₀ :=
      (continuousAt_extChartAt x₀).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr)
    have hsource : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
      extChartAt_source_mem_nhds x₀
    filter_upwards [hpre, hsource] with y hy hys
    exact ⟨(extChartAt I x₀) y, hy, (extChartAt I x₀).left_inv hys⟩
  rcases setOf_riemannianEDist_lt_subset_nhds I hs with
    ⟨c, hc_pos, hc_subset⟩
  refine ⟨c, hc_pos, ?_⟩
  intro γ a b y hγ hγa hγb hab hy_out
  have hriem_le_len :
      Manifold.riemannianEDist I x₀ y ≤
        Manifold.pathELength I γ a b :=
    Manifold.riemannianEDist_le_pathELength hγ hγa hγb hab
  have hc_le_riem : (c : ℝ≥0∞) ≤ Manifold.riemannianEDist I x₀ y := by
    by_contra hnot
    have hlt : Manifold.riemannianEDist I x₀ y < (c : ℝ≥0∞) :=
      lt_of_not_ge hnot
    exact hy_out (hc_subset hlt)
  exact hc_le_riem.trans hriem_le_len

/--
Existential form of `chart_ball_exit_pathELength_lower_bound`, matching the
"small chart ball has a positive exit cost" shape.
-/
theorem exists_chart_ball_exit_pathELength_lower_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r : ℝ, 0 < r ∧ ∃ c : ℝ≥0, 0 < c ∧
      ∀ {γ : ℝ → M} {a b : ℝ} {y : M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b) →
        γ a = x₀ →
        γ b = y →
        a ≤ b →
        y ∉ (extChartAt I x₀).symm ''
          Metric.ball ((extChartAt I x₀) x₀) r →
        (c : ℝ≥0∞) ≤ Manifold.pathELength I γ a b := by
  refine ⟨1, zero_lt_one, ?_⟩
  exact chart_ball_exit_pathELength_lower_bound (g := g) (x₀ := x₀) zero_lt_one

end GeodesicTransport
end Poincare
