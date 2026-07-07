Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-5: the cpow/rpow bridge — the approximate identity closes

Context: `harness/reports/M2-heat-4_blocked.md` (READ FIRST). Proven in `Poincare/Global/HeatKernelIntegral.lean`: `integral_heatKernel_eq_one`, `heatSolution` convolution + existence + continuity, and a Fourier-normalized complex approximate-identity seed after the heat-time scale change. ONE bridge remains: identify the complex expression `((4π²t)⁻¹)^(finrank/2) * Complex.exp(−π²(4π²t)⁻¹‖x−y‖²)`-shaped (`Complex.cpow` normalization from the Fourier route) with the real `heatKernel t (x−y)` (`Real.rpow`/`^` normalization) — a coercion/normalization computation (`Complex.ofReal_cpow`, `Complex.cpow_natCast`/`cpow_ofReal`, `Complex.exp_ofReal`, `abs`/positivity side conditions; the exponent is `finrank/2` — handle the half-integer via `Real.rpow` or squared forms as the seed's exact shape demands).

Deliverables, in a NEW file `Poincare/Global/HeatApproxIdentity.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE NORMALIZATION IDENTIFICATION (the isolated statement; adaptations documented).
2. THE APPROXIMATE IDENTITY: `Tendsto (fun t ↦ heatSolution t f x) (𝓝[>] 0) (𝓝 (f x))` for integrable `f` continuous at `x` (or the exact class the seed supports — state honestly).
3. Report `harness/reports/M2-heat-5_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatApproxIdentity` and report the actual result. Commit your work.
