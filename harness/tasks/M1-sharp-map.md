Read harness/worker_contract.md first and obey it strictly.

# Task M1-sharp-map: the smooth musical isomorphism (sharp map) bridge

Read `harness/reports/M1-hessian-symmetry_blocked.md` — it isolates this bridge and proposes two routes. Context on main: `g.gradientAt` (Global/Laplacian.lean) raises df via fiberwise nondegeneracy; `hessianAt_symm` is proven modulo `MDifferentiableAt (T% (g.gradient f)) x`; the canonical connection is smooth (`leviCivita_contMDiff`); metric smoothness is `g.contMDiff_inner` / `ContMDiffRiemannianMetric.contMDiff`; the model space has `RicciFlow.differentiableAt_coordGradient` (ModelLaplacian.lean) and the chart-transport layer can move statements (Global/LeviCivitaTransport.lean, LeviCivitaRegularity.lean patterns — the hom-bundle smoothness technique from the goal-1 chain is directly relevant: the sharp map is ALSO a hom-bundle section, `T*M → TM`, i.e. `fun y => (sharp_y : (TM y →L[ℝ] ℝ) →L[ℝ] TM y)`).

Deliverable (Global/Laplacian.lean extension or new Global/SharpMap.lean + root import), choose the route that the API supports best:

Route 2 (preferred per report): a reusable smoothness statement for the sharp map — e.g. `theorem contMDiffAt_sharp`/`mdifferentiableAt_gradient`: for f `ContMDiffAt 2` at x, `MDifferentiableAt (T% (g.gradient f)) x`. Implementation guidance: in the chart at x₀, the gradient's model representative is `(chart metric matrix)⁻¹ • (model df)`; inverse of a smooth invertible CLM-valued map is smooth (Mathlib: `ContDiffAt.clm_inverse` / `inverse` analyticity on units — find the current lemma; the repo also has `hasFDerivAt_inverse_raise`/`fderiv_inverse_raise_apply` machinery in ModelLaplacian for the derivative of the raise, and `chartMetric` smoothness in ChartTransport). Compose through the chart like `chartTransportedLeviCivitaHom_contMDiffAt` did for the connection hom.

Route 1 fallback: the local-frame coefficient lemma from the report.

Then the payoff corollaries (each its own commit):
1. `hessianAt_symm'` — symmetry from `f ContMDiffAt 2` alone (discharge the hypothesis via the new bridge).
2. If quick: `laplacianAt` well-behavedness upgrades that were waiting on gradient regularity.

Blocked → greens + refined report. No sorry/axiom. `lake build`, report names.
