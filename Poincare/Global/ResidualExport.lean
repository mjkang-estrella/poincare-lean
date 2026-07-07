import Poincare.Global.DerivativeUnique

/-!
# Residual export for canonical `fderiv` fields

This module records the final calculus export used after a genuine Frechet
derivative of `q ↦ fderiv ℝ F q` has been produced: it yields the
direction-uniform residual bound consumed by `DerivativeUnique`, and the
second-derivative symmetry demanded by `FTransition`.
-/

noncomputable section

open Asymptotics Filter
open scoped Topology

namespace Poincare
namespace ResidualExport

/--
Export a Frechet derivative of the canonical derivative field as the residual
bound required by the Cartan derivative bridge, together with the usual
symmetry of the second derivative.

The residual conclusion is the exact `fderiv`-based direction-uniform shape
consumed by
`DerivativeUnique.exists_cartanChartField_hasFDerivAt_of_fderiv_directional_residual_on_punctured_ball`.
The symmetry conclusion rewrites `ContDiffAt.isSymmSndFDerivAt` through the
given derivative of `q ↦ fderiv ℝ F q`.
-/
theorem fderiv_directional_residual_and_symm_of_hasFDerivAt_fderiv
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) {q : E} {CLM : E →L[ℝ] E →L[ℝ] G}
    (hfderiv : HasFDerivAt (fun q' : E => fderiv ℝ F q') CLM q)
    (hC2 : ContDiffAt ℝ 2 F q) :
    (∀ c > (0 : ℝ), ∀ᶠ δ in 𝓝 (0 : E), ∀ w : E,
      ‖(fderiv ℝ F (q + δ) - fderiv ℝ F q - CLM δ) w‖ ≤
        (c * ‖δ‖) * ‖w‖) ∧
      ∀ a b : E, (CLM a) b = (CLM b) a := by
  constructor
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hfderiv
    intro c hc
    filter_upwards [hfderiv hc] with δ hδ
    intro w
    calc
      ‖(fderiv ℝ F (q + δ) - fderiv ℝ F q - CLM δ) w‖
          ≤ ‖fderiv ℝ F (q + δ) - fderiv ℝ F q - CLM δ‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ w
      _ ≤ (c * ‖δ‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hδ (norm_nonneg w)
  · intro a b
    have hfderiv_eq :
        fderiv ℝ (fun q' : E => fderiv ℝ F q') q = CLM :=
      hfderiv.fderiv
    have hsymm := hC2.isSymmSndFDerivAt (by simp)
    have h := hsymm.eq a b
    simpa [hfderiv_eq] using h

end ResidualExport
end Poincare
