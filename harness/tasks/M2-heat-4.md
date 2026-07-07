Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-4: the fundamental-solution properties — integral one and smoothing

Context: the Gaussian heat kernel solves `∂ₜK = ΔK` in every dimension (`Poincare/Global/HeatKernelPDEn.lean`; kernel/positivity/smoothness in `HeatKernel.lean`, 1D + time derivative in `HeatKernelPDE.lean`; asset inventory `harness/reports/M2-heat-1_assets.md`). Next roadmap slices: the properties making it a FUNDAMENTAL solution.

Deliverables, in a NEW file `Poincare/Global/HeatKernelIntegral.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. INTEGRAL ONE: `∫ x, heatKernel t x = 1` for `t > 0` (Mathlib's `integral_gaussian` / `GaussianFourier` machinery + change of variables; on `EuclideanSpace ℝ (Fin n)` or the general finite-dim inner-product space with its canonical measure — pick what the Gaussian-integral API supports and document; the finrank exponent in `heatKernel` was chosen to make this exact).
2. CONVOLUTION DEFINITION + FIRST PROPERTIES: `heatSolution t f := (heatKernel t) ⋆ f` via `MeasureTheory.convolution` for bounded continuous `f` (or the integrability class the API prefers): well-definedness/integrability of the convolution for `t > 0`.
3. APPROXIMATE IDENTITY (the initial-data recovery seed): `heatSolution t f x → f x` as `t → 0⁺` for bounded continuous `f` — IF Mathlib's approximate-identity/`tendsto` convolution lemmas reach it (there is machinery around `ContDiffBump`/mollifiers — assess and adapt; strict-partial with the isolated missing convergence lemma is valid).
4. Report `harness/reports/M2-heat-4_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatKernelIntegral` and report the actual result. Commit your work.
