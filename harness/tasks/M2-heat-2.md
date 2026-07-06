Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-2: the heat equation identity

Context: `Poincare/Global/HeatKernel.lean` (report `harness/reports/M2-heat-1_assets.md`, READ ITS ROADMAP) defines `heatKernel` with positivity + spatial smoothness. Next slice: the PDE identity.

Deliverables, in a NEW file `Poincare/Global/HeatKernelPDE.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. TIME REGULARITY: differentiability of `t ↦ heatKernel t x` on `t > 0` with the explicit derivative.
2. THE 1-DIMENSIONAL HEAT EQUATION unconditionally: for `E = ℝ` (or the 1-dim inner-product space), `∂ₜ K = ∂ₓ² K` for `t > 0` — explicit `deriv`/`iteratedDeriv` computation on the Gaussian.
3. THE n-DIMENSIONAL IDENTITY if it closes: `∂ₜ K = Δ K` with the Laplacian as the trace of the second Fréchet derivative (`iteratedFDeriv` 2 contracted over an orthonormal basis) — if the contraction plumbing is heavy, isolate the exact statement and deliver 1-2.
4. Report `harness/reports/M2-heat-2_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatKernelPDE` and report the actual result. Commit your work.
