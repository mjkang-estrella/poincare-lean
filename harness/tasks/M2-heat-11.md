Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-11: directional second derivatives under the integral — the Cauchy theorem via coordinates

Context: `harness/reports/M2-heat-10_blocked.md` (READ FIRST). ORCHESTRATOR SIMPLIFICATION: the blocker asked for a Fréchet-Hessian-under-integral theorem, but the LAPLACIAN needs only DIRECTIONAL second derivatives along an orthonormal basis (`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`, as used in `HeatKernelPDEn.lean`). Route: for each basis direction `e`, the scalar function `r ↦ heatSolution t f (x + r • e)` is differentiated under the integral TWICE by the SAME dominated `hasDerivAt_integral_of_dominated_loc_of_deriv_le` discipline already used for time (`HeatCauchyFinal.lean`): first derivative uses the proven first-spatial envelope/domination (`HeatCauchyTheorem.lean`), second uses the proven Laplacian/second-derivative envelope (`HeatCauchyFinal.lean`'s `heatKernelLaplacianEnvelope` — restate directionally if needed; the derivative formulas are explicit Gaussians). Then the finite orthonormal sum + the kernel's own PDE (`heatKernel_heatEquation_laplacian`) + the time interchange (proven) close the Cauchy theorem.

Deliverables, in a NEW file `Poincare/Global/HeatCauchyDirectional.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. DIRECTIONAL FIRST + SECOND derivative-under-integral for `heatSolution` along a fixed direction (two dominated applications; envelopes exist).
2. THE LAPLACIAN IDENTIFICATION: `Δ (heatSolution t f) x = ∫ y, Δ-kernel(x−y) f y` via the orthonormal sum (mind: the Laplacian-eq-basis-sum lemma needs the function's second differentiability — the directional theorems supply exactly the iterated data; check the lemma's precise hypotheses and adapt).
3. 🎯 THE UNCONDITIONAL MODEL CAUCHY THEOREM (the conditional package in `HeatCauchy.lean` + everything proven).
4. Report `harness/reports/M2-heat-11_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatCauchyDirectional` and report the actual result. Commit your work.
