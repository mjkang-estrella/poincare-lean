import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.GeodesicLengthFinal

/-!
# Cartan domain shrink

This module records the honest radius intersection available downstream of the
current exponential-local-homeomorphism and cutoff-one PL-flow packages.

It deliberately stops before the Cartan block instantiation: the exported
cutoff-one flow package controls small initial velocities `v₀`, while the
unit-speed endpoint-at-`‖v‖` Cartan blocks require the normalized nonzero
direction `‖v‖⁻¹ • v`.  Shrinking a ball around `0` controls `v`, not the
norm-one direction.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanDomainShrink

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
There is a positive normal-coordinate ball contained in the exponential chart
source and small enough for the cutoff-one PL-flow package; on this same ball
the endpoint time `‖v‖` lies in the PL interval.

The final conjunct is the concrete conversion supplied by the current public
API: for `‖v‖ < ρ`, the PL-flow law applies to the unnormalised small velocity
`v` at time `‖v‖`.
-/
theorem exists_shrunk_expAt_source_cutoff_one_ball
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball (0 : E) ρ ⊆
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
      ∃ τ : ℝ, 0 < τ ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ a : NNReal,
        ∃ α : E × E → ℝ → E × E,
          ρ ≤ δ ∧ ρ ≤ τ ∧
          (∀ v₀ : E, ‖v₀‖ < δ →
            α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
              (∀ s ∈ Icc (-τ) τ,
                HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                  (geodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                    (α (extChartAt I x₀ x₀, v₀) s))
                  (Icc (-τ) τ) s) ∧
              (∀ s ∈ Icc (-τ) τ,
                α (extChartAt I x₀ x₀, v₀) s ∈
                  Metric.closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
              (∀ s ∈ Icc (-τ) τ,
                (α (extChartAt I x₀ x₀, v₀) s).1 ∈
                  (extChartAt I x₀).target) ∧
              (∀ s ∈ Icc (-τ) τ,
                GeodesicTransport.cutoff (n := 3) x₀
                  (α (extChartAt I x₀ x₀, v₀) s).1 = 1) ∧
              ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (-τ) τ,
                α (extChartAt I x₀ x₀, r • v₀) s =
                  ((α (extChartAt I x₀ x₀, v₀) (r * s)).1,
                    r • (α (extChartAt I x₀ x₀, v₀) (r * s)).2)) ∧
          (∀ v : E, ‖v‖ < ρ →
            v ∈
                (GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₀).source ∧
              ‖v‖ < δ ∧
              ‖v‖ ∈ Icc (0 : ℝ) τ ∧
              GeodesicTransport.expAt g x₀ (‖v‖ • v) =
                (extChartAt I x₀).symm
                  (α (extChartAt I x₀ x₀, v) ‖v‖).1) := by
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0 : (0 : E) ∈ e.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0) with
    ⟨r, hr_pos, hr_source⟩
  rcases GeodesicTransport.expAt_uniform_pl_flow_cutoff_one_eq_on_Icc
      (g := g) (x₀ := x₀) with
    ⟨τ, hτ_pos, δ, hδ_pos, a, α, hα, hexp⟩
  let ρ : ℝ := min r (min δ τ) / 2
  have hmin_pos : 0 < min r (min δ τ) :=
    lt_min hr_pos (lt_min hδ_pos hτ_pos)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρ_le_min : ρ ≤ min r (min δ τ) := by
    dsimp [ρ]
    linarith
  have hρ_le_r : ρ ≤ r :=
    hρ_le_min.trans (min_le_left r (min δ τ))
  have hρ_le_delta : ρ ≤ δ :=
    hρ_le_min.trans ((min_le_right r (min δ τ)).trans (min_le_left δ τ))
  have hρ_le_tau : ρ ≤ τ :=
    hρ_le_min.trans ((min_le_right r (min δ τ)).trans (min_le_right δ τ))
  refine ⟨ρ, hρ_pos, ?_, τ, hτ_pos, δ, hδ_pos, a, α,
    hρ_le_delta, hρ_le_tau, hα, ?_⟩
  · intro v hv
    apply hr_source
    have hvdist : dist v (0 : E) < r :=
      (Metric.mem_ball.mp hv).trans_le hρ_le_r
    exact Metric.mem_ball.mpr hvdist
  · intro v hv
    have hvsrc : v ∈ e.source := by
      apply hr_source
      have hvdist : dist v (0 : E) < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hv.trans_le hρ_le_r
      exact Metric.mem_ball.mpr hvdist
    have hvδ : ‖v‖ < δ := hv.trans_le hρ_le_delta
    have hvτ : ‖v‖ ≤ τ := hv.le.trans hρ_le_tau
    have ht : ‖v‖ ∈ Icc (0 : ℝ) τ := ⟨norm_nonneg v, hvτ⟩
    exact ⟨hvsrc, hvδ, ht, hexp v hvδ ‖v‖ ht⟩

end CartanDomainShrink
end Poincare
