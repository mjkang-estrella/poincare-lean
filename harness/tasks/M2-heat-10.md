Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-10: the Laplacian under the integral — THE CAUCHY THEOREM

Context: `harness/reports/M2-heat-9_blocked.md` (READ FIRST). Everything else is discharged: both pointwise dominations, both integrable envelopes, the TIME interchange (dominated differentiation proven), and the conditional package now waits on ONE hypothesis: the spatial Laplacian of the parameter integral = the integral of the Laplacian integrands (`HeatCauchyFinal.lean` — read the exact remaining hypothesis shape). Route: `Δ` on a finite-dim inner-product space = sum over an orthonormal basis of second directional derivatives (`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`, used in `HeatKernelPDEn.lean`); each second directional derivative moves under the integral by TWO applications of dominated `hasDerivAt_integral_of_dominated_loc_of_deriv_le`-style differentiation (first derivative needs its own envelope — the first-spatial-derivative Gaussian bound; derive it in the same family as the proven `heatKernelLaplacianEnvelope` — the integrability layer accepts any polynomial degree); then sum finitely.

Deliverables, in a NEW file `Poincare/Global/HeatCauchyTheorem.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. FIRST-SPATIAL-DERIVATIVE envelope + domination (the missing intermediate).
2. THE LAPLACIAN INTERCHANGE (two-step dominated differentiation + orthonormal-basis sum).
3. 🎯 THE UNCONDITIONAL MODEL CAUCHY THEOREM: `heatSolution` solves `∂ₜu = Δu` for `t > 0` with `u → f` as `t → 0⁺` — packaged as one named theorem (via the conditional package).
4. Report `harness/reports/M2-heat-10_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatCauchyTheorem` and report the actual result. Commit your work.
