import Poincare.Global.TheSelector

/-!
# Two connector work surface

This module records the verified part of the two-connector boundary: the
second-variation `Ξ` local-family selector obtained directly from the
chart-Christoffel second-variation Picard-Lindelöf package.

The remaining Ω-to-CLM bridge is not asserted here: the public Ω selector is
local in the perturbation, while the current endpoint-CLM constructor requires
global all-perturbation PL and closed-ball hypotheses.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace TwoConnectors

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
The `Ξ` connector available from the existing second-variation PL package.

For every continuous augmented base curve `ζ`, this selects a local family of
solutions to the second-variation linear ODE.  The family is valid on the PL
closed ball around the zero perturbation and exports the exact data needed to
form the hosted doubly-augmented curve
`τ ↦ (β y.1 τ, Ξ y.2 τ)` whenever the selected initial perturbation lies in
that ball.
-/
theorem exists_xiSelectorPackage_on_pl_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → A} (hζ : Continuous ζ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ a r : ℝ≥0, 0 < r ∧
      ∃ Ξ : A → ℝ → A,
        ∀ η : A, η ∈ closedBall (0 : A) r →
          Ξ η 0 = η ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (Ξ η)
                (secondVariationFlowFieldAlong
                  (GeodesicTransport.chartChristoffelField g x₀)
                  ζ t (Ξ η t))
                (Icc (-ε) ε) t) ∧
            ∀ t ∈ Icc (-ε) ε, Ξ η t ∈ closedBall (0 : A) a := by
  rcases
      GeodesicTransport.exists_isPicardLindelof_chartChristoffel_secondVariation_linearODE
        (g := g) (x₀ := x₀) (ζ := ζ) hζ (0 : A) with
    ⟨ε, hε, a, r, L, K, hr, hpl⟩
  rcases hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall with
    ⟨Ξ, hΞ⟩
  exact ⟨ε, hε, a, r, hr, Ξ, hΞ⟩

end TwoConnectors
end Poincare
