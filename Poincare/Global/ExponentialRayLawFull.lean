import Poincare.Global.ExponentialRayLaw

/-!
# Closed-interval ray-law boundary

The fixed-time package now exposes the full closed-interval PL-flow law for
the chosen `expAt` witness.  The remaining step to the requested
`geodesicGermAt` ray law is an interval identification between that PL flow and
the independently chosen `geodesicGermChartSolution`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

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
The selected `expAt` witness has a uniform closed-interval ray law with the
PL chart flow used in its construction.
-/
theorem expAt_closed_interval_eq_uniform_pl_flow
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) t))
                (Icc (-ε) ε) t) ∧
            (∀ t ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) t ∈
                Metric.closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
            (∀ t ∈ Icc (-ε) ε,
              (α (extChartAt I x₀ x₀, v₀) t).1 ∈
                (extChartAt I x₀).target) ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, s • v₀) σ =
                ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
                  s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2)) ∧
        ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
          expAt g x₀ (t • v) =
            (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v) t).1 :=
  expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀)

/--
The requested full ray law follows formally from the exported PL-flow law plus
position-coordinate identification of that PL flow with the chosen geodesic
germ on the same closed interval.
-/
theorem expAt_eq_geodesicGermAt_on_Icc_of_pl_flow_position_eq_germ
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {τ δ : ℝ} {α : E × E → ℝ → E × E}
    (hpl :
      ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
        expAt g x₀ (t • v) =
          (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v) t).1)
    (hgerm :
      ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
        (α (extChartAt I x₀ x₀, v) t).1 =
          (geodesicGermChartSolution g x₀ v t).1) :
    ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
      expAt g x₀ (t • v) = geodesicGermAt g x₀ v t := by
  intro v hv t ht
  rw [hpl v hv t ht]
  simpa [geodesicGermAt] using
    congrArg (fun z : E => (extChartAt I x₀).symm z)
      (hgerm v hv t ht)

end GeodesicTransport
end Poincare
