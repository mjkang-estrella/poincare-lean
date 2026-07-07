Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-7: the two interchange lemmas — the Cauchy problem closes

Context: `harness/reports/M2-heat-6_blocked.md` (READ FIRST). `Poincare/Global/HeatCauchy.lean` has the CONDITIONAL Cauchy package + shifted integrability + one domination lemma. TWO facts remain: (1) time differentiation under the convolution integral (dominated: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the Gaussian time-derivative domination on a compact time window `[t/2, 2t]` — the explicit `deriv_heatKernel_time` gives the integrand; dominate by a fixed Gaussian at the window edges times polynomial — derive the bound honestly); (2) the spatial Laplacian interchange (`Δ` of the convolution = convolution with `Δ` kernel — via second-derivative differentiation under the integral, same domination discipline, or Mathlib convolution-derivative lemmas `HasFDerivAt.convolution`-family if they reach second order).

Deliverables, in a NEW file `Poincare/Global/HeatCauchyClose.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1-2. The two interchange facts (exact conditional-hypothesis spellings from `HeatCauchy.lean`; adaptations documented).
3. THE UNCONDITIONAL CAUCHY THEOREM via the conditional package: `heatSolution` solves the heat equation for `t > 0` with initial-data recovery — the model linear Cauchy problem, packaged.
4. Report `harness/reports/M2-heat-7_{done|blocked}.md`; if blocked, ONE domination estimate isolated.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatCauchyClose` and report the actual result. Commit your work.
