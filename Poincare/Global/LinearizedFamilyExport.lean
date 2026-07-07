import Poincare.Global.CartanIsometryClose
import Poincare.Global.ExponentialMap

/-!
# Hosted linearized-family export

This module exposes the Picard-Lindelöf fixed-point family for the linearized
chart-geodesic equation at hosted data.  The family is still local in the PL
closed ball: the remaining global endpoint-linearity step must rescale this
local family before it can feed `linearizedEndpointCLM` for all directions.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace LinearizedFamilyExport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Concrete hosted linearized solutions on a Picard-Lindelöf closed ball.

Given PL data for the linearized geodesic equation along a hosted base curve
`γ`, this chooses one flow of linearized states and reindexes it by endpoint
directions `w` through the strict-derivative initial datum `(0, T⁻¹ • w)`.
For every direction whose initial state lies in the PL radius, the exported
family has the exact initial value, solves the linearized equation on the
common interval, and remains in the PL closed ball.
-/
theorem exists_hosted_linearized_solution_family_on_pl_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {ε T : ℝ} (hε : 0 < ε)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E), (0 : E)) a r L K) :
    ∃ Ψ : E → ℝ → E × E,
      ∀ w : E, ((0 : E), T⁻¹ • w) ∈ closedBall ((0 : E), (0 : E)) r →
        Ψ w 0 = ((0 : E), T⁻¹ • w) ∧
          (∀ t ∈ Icc (-ε) ε,
            HasDerivWithinAt (Ψ w)
              (linearizedGeodesicFlowFieldAlong
                (GeodesicTransport.chartChristoffelField g x₀)
                γ t (Ψ w t))
              (Icc (-ε) ε) t) ∧
          ∀ t ∈ Icc (-ε) ε, Ψ w t ∈ closedBall ((0 : E), (0 : E)) a := by
  rcases hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨Φ, hΦ⟩
  refine ⟨fun w => Φ ((0 : E), T⁻¹ • w), ?_⟩
  intro w hw
  rcases hΦ ((0 : E), T⁻¹ • w) hw with ⟨h0, hder, hmem⟩
  exact ⟨h0, hder, hmem⟩

end LinearizedFamilyExport
end Poincare

