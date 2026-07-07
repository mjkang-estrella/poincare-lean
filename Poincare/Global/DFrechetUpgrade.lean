import Poincare.Global.SecondFrechet

/-!
# Residual upgrade for CLM-valued derivative fields

This module isolates the final calculus step needed after the order-two
residual comparison has been proved for a concrete derivative field: a
direction-uniform endpoint residual bound against a continuous-linear candidate
is exactly the Frechet differentiability statement for that field.
-/

noncomputable section

open Asymptotics Filter
open scoped Topology

namespace Poincare
namespace GeodesicTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Upgrade a direction-uniform order-two endpoint residual bound to Frechet
differentiability of a CLM-valued field.

The hypothesis is the residual spelling produced by the Gronwall comparison:
for every tolerance, uniformly for all sufficiently small perturbations `δ`,
the difference `D (q + δ) - D q - CLM δ` is bounded by that tolerance times
`‖δ‖`.
-/
theorem clmField_hasFDerivAt_of_residual_norm_le
    (D : E → E →L[ℝ] E) (q : E)
    (CLM : E →L[ℝ] E →L[ℝ] E)
    (hres : ∀ c > (0 : ℝ), ∀ᶠ δ in 𝓝 (0 : E),
      ‖D (q + δ) - D q - CLM δ‖ ≤ c * ‖δ‖) :
    HasFDerivAt D CLM q := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  filter_upwards [hres c hc] with δ hδ
  exact hδ

end GeodesicTransport
end Poincare
