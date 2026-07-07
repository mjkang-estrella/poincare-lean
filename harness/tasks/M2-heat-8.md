Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-8: the integrable envelopes — the Cauchy problem's last analysis

Context: `harness/reports/M2-heat-7_blocked.md` (READ FIRST). Proven: the pointwise time-derivative window domination (`heatKernel_time_deriv_window_sub_left_mul_le_abs_majorant`, `HeatCauchyClose.lean`) + the conditional Cauchy package (`HeatCauchy.lean`). MISSING: (a) ONE fixed integrable envelope dominating `|∂ₜ heatKernel τ (x−y)| · |f y|` for all `τ` in the compact window `[t/2, 2t]` — the classical envelope: `C(t,x) · (1 + ‖y‖²) · heatKernel (2t·θ) (x−y)`-shaped (a slightly-widened Gaussian times polynomial; its integrability = Gaussian moments, which Mathlib has via `integral_gaussian`-family / `GaussianFourier` moment lemmas — assess and derive); prove the pointwise estimate feeds it (the window estimate already exists — massage constants); (b) the second-spatial-derivative analogue for the Laplacian interchange (same envelope discipline on `iteratedFDeriv 2` of the Gaussian — the derivative formulas are in `HeatKernelPDEn.lean` helpers).

Deliverables, in a NEW file `Poincare/Global/HeatEnvelopes.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE TWO ENVELOPES with integrability proofs.
2. THE INTERCHANGE FACTS discharged (the conditional hypotheses of `HeatCauchy.lean`'s package) and THE UNCONDITIONAL CAUCHY THEOREM.
3. Report `harness/reports/M2-heat-8_{done|blocked}.md`; if blocked, ONE moment/integrability estimate isolated.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatEnvelopes` and report the actual result. Commit your work.
