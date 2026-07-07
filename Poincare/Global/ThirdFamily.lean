import Poincare.Global.ExponentialMap
import Poincare.Global.ThirdVariation

/-!
# Hosted third-variation family export

This module exposes the Picard-Lindelöf fixed-point family for the
third-variation linear ODE along a hosted doubly-augmented curve.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
Concrete hosted third-variation solutions on a Picard-Lindelöf closed ball.

For a continuous hosted doubly-augmented base curve `ζ`, the existing
chart-Christoffel third-variation PL package supplies local PL data at the
zero variation.  This theorem chooses the corresponding fixed-point family
`Ω` and exports its exact initial value, linearized ODE, and closed-ball
invariance on the common interval.
-/
theorem exists_hosted_thirdVariation_solution_family_on_pl_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → A × A} (hζ : Continuous ζ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ a r : ℝ≥0, 0 < r ∧
      ∃ Ω : A × A → ℝ → A × A,
        ∀ h : A × A, h ∈ closedBall (0 : A × A) r →
          Ω h 0 = h ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (Ω h)
                (fderiv ℝ
                  (fun y : A × A =>
                    let F : A → A :=
                      augmentedGeodesicFlowField (chartChristoffelField g x₀)
                    (F y.1, (fderiv ℝ F y.1) y.2))
                  (ζ t) (Ω h t))
                (Icc (-ε) ε) t) ∧
            ∀ t ∈ Icc (-ε) ε, Ω h t ∈ closedBall (0 : A × A) a := by
  rcases
      exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE
        (g := g) (x₀ := x₀) (ζ := ζ) hζ (0 : A × A) with
    ⟨ε, hε, a, r, _L, _K, hr, hpl⟩
  rcases hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall with
    ⟨Ω, hΩ⟩
  exact ⟨ε, hε, a, r, hr, Ω, hΩ⟩

end GeodesicTransport
end Poincare
