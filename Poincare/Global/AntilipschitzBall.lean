import Poincare.Global.GeodesicDistanceLower
import Poincare.Global.NormalizedFlow

/-!
# Local anti-Lipschitz ball assembly

This module contains the verified path-infimum assembly for the local
anti-Lipschitz chart-ball problem.  The remaining analytic input is a uniform
lower bound for every `C¹` path between two points in a sufficiently small
chart ball; once supplied, `antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower`
turns it into the exact `AntilipschitzWith` statement used by
`LocalChartAntilipschitzLowerBound`.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology ENNReal NNReal RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/--
Path-infimum lower-bound assembly for Mathlib's Riemannian extended distance:
if every `C¹` path from `x` to `y` has `pathELength` at least `L`, then the
Riemannian infimum distance is at least `L`.
-/
theorem ofReal_le_riemannianEDist_of_forall_pathELength_lower
    (g : ClosedSmoothRiemannianMetric n M) {x y : M} {L : ℝ}
    (hpaths :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ∀ {γ : ℝ → M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
        γ 0 = x →
        γ 1 = y →
        ENNReal.ofReal L ≤ Manifold.pathELength I γ 0 1) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ENNReal.ofReal L ≤ Manifold.riemannianEDist I x y := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  by_contra hnot
  have hlt : Manifold.riemannianEDist I x y < ENNReal.ofReal L :=
    lt_of_not_ge hnot
  rcases Manifold.exists_lt_of_riemannianEDist_lt hlt with
    ⟨γ, hγ0, hγ1, hγsmooth, hγlt⟩
  exact not_lt_of_ge (hpaths hγsmooth hγ0 hγ1) hγlt

omit [MeasurableSpace M] [BorelSpace M] in
/--
Real-distance form of
`ofReal_le_riemannianEDist_of_forall_pathELength_lower`, after installing the
metric induced by `g`.
-/
theorem le_induced_dist_of_forall_pathELength_lower
    (g : ClosedSmoothRiemannianMetric n M) {x y : M} {L : ℝ}
    (hpaths :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ∀ {γ : ℝ → M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
        γ 0 = x →
        γ 1 = y →
        ENNReal.ofReal L ≤ Manifold.pathELength I γ 0 1) :
    letI : MetricSpace M := g.toMetricSpace
    L ≤ dist x y := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  have hriem :
      ENNReal.ofReal L ≤ Manifold.riemannianEDist I x y :=
    ofReal_le_riemannianEDist_of_forall_pathELength_lower
      (g := g) (x := x) (y := y) hpaths
  have hed : ENNReal.ofReal L ≤ edist x y := by
    rw [induced_edist_eq_riemannianEDist (g := g) x y]
    exact hriem
  rw [edist_dist] at hed
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hed

omit [MeasurableSpace M] [BorelSpace M] in
/--
The exact anti-Lipschitz ball assembly: a uniform path-length lower bound for
every pair of chart points in the ball implies the inverse chart is
`AntilipschitzWith K` on that ball.
-/
theorem antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {r : ℝ} {K : ℝ≥0}
    (hK : 0 < K)
    (hpaths :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      ∀ (u v :
          {y : E // y ∈ Metric.ball ((extChartAt I x₀) x₀) r})
        {γ : ℝ → M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
        γ 0 = (extChartAt I x₀).symm (u : E) →
        γ 1 = (extChartAt I x₀).symm (v : E) →
        ENNReal.ofReal (((K : ℝ)⁻¹) * dist (u : E) (v : E)) ≤
          Manifold.pathELength I γ 0 1) :
    letI : MetricSpace M := g.toMetricSpace
    AntilipschitzWith K
      (fun y :
          {y : E // y ∈ Metric.ball ((extChartAt I x₀) x₀) r} =>
        (extChartAt I x₀).symm (y : E)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  have hKℝ : (0 : ℝ) < K := by exact_mod_cast hK
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro u v
  have hlower :
      ((K : ℝ)⁻¹) * dist (u : E) (v : E) ≤
        dist ((extChartAt I x₀).symm (u : E))
          ((extChartAt I x₀).symm (v : E)) :=
    le_induced_dist_of_forall_pathELength_lower
      (g := g)
      (x := (extChartAt I x₀).symm (u : E))
      (y := (extChartAt I x₀).symm (v : E))
      (by
        intro γ hγ hγ0 hγ1
        exact hpaths u v hγ hγ0 hγ1)
  calc
    dist u v = dist (u : E) (v : E) := by
      rw [Subtype.dist_eq]
    _ = (K : ℝ) * (((K : ℝ)⁻¹) * dist (u : E) (v : E)) := by
      field_simp [ne_of_gt hKℝ]
    _ ≤ (K : ℝ) *
        dist ((extChartAt I x₀).symm (u : E))
          ((extChartAt I x₀).symm (v : E)) := by
      exact mul_le_mul_of_nonneg_left hlower (by positivity)

end GeodesicTransport
end Poincare
