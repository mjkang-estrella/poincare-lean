import Poincare.Global.ResidualExport

/-!
# Congruence step for endpoint derivative fields

This module records the open-neighborhood congruence step: if the endpoint
derivative family agrees with the canonical `q ↦ fderiv ℝ F q` field on an
open set around `q`, then its derivative at `q` transfers to the canonical
field and can be consumed by `ResidualExport`.
-/

noncomputable section

open Filter
open scoped Topology

namespace Poincare
namespace CongruenceStep

/--
Transfer a Frechet derivative from an endpoint derivative family to the
canonical derivative field on an open agreement neighborhood, then export the
direction-uniform residual and second-derivative symmetry facts.
-/
theorem fderiv_directional_residual_and_symm_of_endpoint_hasFDerivAt_on_open
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) {q : E} {endpoint : E → E →L[ℝ] G}
    {CLM : E →L[ℝ] E →L[ℝ] G} {U : Set E}
    (hU : IsOpen U) (hq : q ∈ U)
    (hEq : Set.EqOn (fun q' : E => fderiv ℝ F q') endpoint U)
    (hendpoint : HasFDerivAt endpoint CLM q)
    (hC2 : ContDiffAt ℝ 2 F q) :
    (∀ c > (0 : ℝ), ∀ᶠ δ in 𝓝 (0 : E), ∀ w : E,
      ‖(fderiv ℝ F (q + δ) - fderiv ℝ F q - CLM δ) w‖ ≤
        (c * ‖δ‖) * ‖w‖) ∧
      ∀ a b : E, (CLM a) b = (CLM b) a := by
  have hevent :
      (fun q' : E => fderiv ℝ F q') =ᶠ[𝓝 q] endpoint :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hq) hEq
  have hfderiv :
      HasFDerivAt (fun q' : E => fderiv ℝ F q') CLM q :=
    hevent.hasFDerivAt_iff.mpr hendpoint
  exact
    ResidualExport.fderiv_directional_residual_and_symm_of_hasFDerivAt_fderiv
      F hfderiv hC2

end CongruenceStep
end Poincare
