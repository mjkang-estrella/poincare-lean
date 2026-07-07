Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-9: pointwise-to-envelope — the Cauchy problem's final feeds

Context: `harness/reports/M2-heat-8_blocked.md` (READ FIRST). Proven: the envelope INTEGRABILITY layer (`HeatEnvelopes.lean`, incl. the classical `(1+‖y‖²)·heatKernel s (x−y)` shape and `heatKernelTimeWindowEnvelope`) and the pointwise window bound (`HeatCauchyClose.lean`). MISSING: (a) the pointwise DOMINATION `‖deriv (heatKernel · (x−y)) τ · f y‖ ≤ heatKernelTimeWindowEnvelope t A x y` for `τ` in the window and bounded `f` (massage the existing window bound into the envelope's exact shape — constants/Gaussian-widening arithmetic; the report states the exact statement); (b) the spatial analogue: pointwise bound on the second-derivative/Laplacian terms of `z ↦ heatKernel t (z−y)` by a (possibly new, same-family) integrable envelope — the derivative formulas are in `HeatKernelPDEn.lean` helpers; the Gaussian-polynomial integrability layer accepts any polynomial degree.

Deliverables, in a NEW file `Poincare/Global/HeatCauchyFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1-2. The two pointwise dominations (exact shapes per the reports).
3. THE INTERCHANGES + THE UNCONDITIONAL CAUCHY THEOREM via `HeatCauchy.lean`'s conditional package (dominated differentiation under the integral — `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for time; the second-derivative parametric argument for space).
4. Report `harness/reports/M2-heat-9_{done|blocked}.md`; if blocked, ONE estimate.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatCauchyFinal` and report the actual result. Commit your work.
