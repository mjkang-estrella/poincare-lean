import Poincare.Global.ChristoffelTransition
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Koszul naturality sign pin

This strict-partial module pins the sign convention needed by the chart-change
producer for `ChristoffelTransition.lean`.

For the local Euclidean coordinate change `σ z = z + z^2`, the ordinary
second-derivative correction at `0` in the unit direction is `+2`.  With this
repo's geodesic convention `γ'' = -Γ(γ)(γ', γ')`, the target Christoffel
value on the transported unit velocity is therefore `-2`, i.e. the transition
law is `Γ¹(Dσ v, Dσ v) = Dσ(Γ⁰(v,v)) - B`, not the plus-sign variant.
-/

noncomputable section

namespace Poincare
namespace GeodesicTransport

/--
Numeric sign pin for the Christoffel transition under the convention
`geodesicFlowField Γ p = (p.2, -Γ p.1 p.2 p.2)`.

Here `σ z = z + z^2`, `v = 1`, the source Euclidean Christoffel value is `0`,
and the ordinary chain-rule correction is
`B = d/ds (Dσ(s) v)|₀ = 2`.  Thus the compatible target value is `-2`, which
is exactly `Dσ₀ * 0 - B`; the plus-sign identity would give `+2`.
-/
theorem quadratic_euclidean_transition_sign_pin :
    let σ : ℝ → ℝ := fun z => z + z ^ 2
    let v : ℝ := 1
    let sourceΓvv : ℝ := 0
    let targetΓww : ℝ := -2
    let Dσ₀ : ℝ := deriv σ 0
    let B : ℝ := deriv (fun s : ℝ => deriv σ s * v) 0
    Dσ₀ = 1 ∧ B = 2 ∧
      targetΓww = Dσ₀ * sourceΓvv - B ∧
      targetΓww ≠ Dσ₀ * sourceΓvv + B := by
  norm_num [deriv_add, deriv_pow]

end GeodesicTransport
end Poincare
