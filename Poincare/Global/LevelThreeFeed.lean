import Poincare.Global.TowerCloses

/-!
# Level-three feed bridge

This module isolates the noncomputable-selection bridge for the produced
exponential-chart derivative fields.  Once the canonical `fderiv` fields are
known to be `C1`, the neighborhood `HasFDerivAt` facts exported by
`FieldProducer` identify the selected fields with those canonical fields near
the base points, so the selected fields inherit `C1` regularity.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace LevelThreeFeed

local notation "E3" => ClosedSmoothModel 3

/--
The `FieldProducer` derivative-field selections inherit `C1` regularity from
the canonical `q ↦ fderiv ℝ e q` fields.

This is the exact congruence step needed after a level-three residual theorem
has proved `C1` regularity of the canonical derivative field: the selected
`sourceD` and `targetD` values agree locally with the canonical Frechet
derivatives by uniqueness of `HasFDerivAt`.
-/
theorem selected_expChart_derivative_fields_contDiffAt_one_of_fderiv_contDiffAt_one
    {eM eS : E3 → E3} {sourceD targetD : E3 → E3 →L[ℝ] E3}
    {v w : E3}
    (hsource_deriv :
      ∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q)
    (hsource_fderiv_c1 :
      ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v)
    (htarget_deriv :
      ∃ U ∈ 𝓝 w, ∀ q ∈ U, HasFDerivAt eS (targetD q) q)
    (htarget_fderiv_c1 :
      ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) w) :
    ContDiffAt ℝ 1 sourceD v ∧ ContDiffAt ℝ 1 targetD w := by
  rcases hsource_deriv with ⟨U, hU, hUderiv⟩
  have hsource_event :
      sourceD =ᶠ[𝓝 v] fun q : E3 => fderiv ℝ eM q := by
    filter_upwards [hU] with q hq
    exact (hUderiv q hq).fderiv.symm
  rcases htarget_deriv with ⟨U, hU, hUderiv⟩
  have htarget_event :
      targetD =ᶠ[𝓝 w] fun q : E3 => fderiv ℝ eS q := by
    filter_upwards [hU] with q hq
    exact (hUderiv q hq).fderiv.symm
  exact
    ⟨hsource_fderiv_c1.congr_of_eventuallyEq hsource_event,
      htarget_fderiv_c1.congr_of_eventuallyEq htarget_event⟩

end LevelThreeFeed
end Poincare
