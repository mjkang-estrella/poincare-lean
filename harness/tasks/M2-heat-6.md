Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-6: heatSolution solves the heat equation — the model Cauchy problem

Context: the kernel is a certified fundamental solution (`HeatKernel*.lean`: PDE in all dimensions, integral one, convolution `heatSolution` with existence/continuity, approximate identity `tendsto_heatSolution_nhdsGT_zero`). The remaining piece of the model linear Cauchy problem: for `t > 0`, `heatSolution t f` SOLVES the heat equation — `∂ₜ (heatSolution t f) x = Δ (heatSolution t f ·) x` — by differentiation under the convolution integral (Mathlib: `MeasureTheory.convolution` differentiation lemmas — `HasFDerivAt.convolution`-adjacent / `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the time derivative with Gaussian domination; the kernel's explicit time derivative `deriv_heatKernel_time` and spatial derivatives from `HeatKernelPDEn.lean` supply the integrands and dominating functions).

Deliverables, in a NEW file `Poincare/Global/HeatCauchy.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. TIME DERIVATIVE UNDER THE INTEGRAL: `deriv (fun τ ↦ heatSolution τ f x) t = ∫ y, deriv (fun τ ↦ heatKernel τ (x−y)) t * f y` for `t > 0` and bounded integrable/continuous `f` (dominated differentiation; the Gaussian dominations on compact time-intervals are the work — state honestly the data class that closes).
2. SPATIAL LAPLACIAN UNDER THE INTEGRAL: similarly for `Δ` (or the second Fréchet derivative form; the `HeatKernelPDEn.lean` helpers are the integrands).
3. THE CAUCHY THEOREM: combining 1-2 with `heatKernel_heatEquation_laplacian`: `heatSolution` solves the heat equation for `t > 0` (+ recovery at `t → 0⁺` already proven) — the MODEL LINEAR CAUCHY PROBLEM SOLVED, stated as one packaged theorem.
4. Report `harness/reports/M2-heat-6_{done|blocked}.md`; strict-partial with ONE isolated domination lemma valid.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatCauchy` and report the actual result. Commit your work.
