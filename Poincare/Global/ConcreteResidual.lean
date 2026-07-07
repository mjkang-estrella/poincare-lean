import Poincare.Global.DFrechetUpgrade

/-!
# Concrete residual bridge for the Cartan derivative field

This module isolates the final norm conversion for the Cartan differential
field in local inverse coordinates.  Direction-uniform augmented endpoint
remainders give pointwise bounds after applying the residual operator to an
arbitrary direction; `opNorm_le_bound` turns those into the operator-norm
residual required by `DFrechetUpgrade`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Poincare
namespace GeodesicTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Upgrade direction-uniform concrete residual bounds for the chart-indexed
Cartan differential field to Frechet differentiability of that field.

The hypothesis is the endpoint-remainder shape produced by the augmented
second-variation comparison after evaluating the operator residual on an
arbitrary direction `u`.  The proof converts it to the operator-norm residual
bound and feeds `clmField_hasFDerivAt_of_residual_norm_le`.
-/
theorem chartField_hasFDerivAt_of_directional_residual_norm_le
    (eM_symm : E → E) (DF : E → E →L[ℝ] E) (q : E)
    (CLM : E →L[ℝ] E →L[ℝ] E)
    (hdir : ∀ c > (0 : ℝ), ∀ᶠ δ in 𝓝 (0 : E), ∀ u : E,
      ‖(DF (eM_symm (q + δ)) - DF (eM_symm q) - CLM δ) u‖ ≤
        (c * ‖δ‖) * ‖u‖) :
    HasFDerivAt (fun q' : E => DF (eM_symm q')) CLM q := by
  apply clmField_hasFDerivAt_of_residual_norm_le
  intro c hc
  filter_upwards [hdir c hc] with δ hδ
  exact
    ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg hc.le (norm_nonneg δ))
      (fun u => by
        simpa only [mul_assoc] using hδ u)

end GeodesicTransport
end Poincare
