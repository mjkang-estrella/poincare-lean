Read harness/worker_contract.md first and obey it strictly.

# Task M3-consequences-3: the three minimum-witness prerequisite lemmas + assembly

Read `harness/reports/M3-consequences-2_blocked.md` — execute its "Recommended next slice" exactly (each its own commit):

1. **Local flat second-derivative test** `fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt`: for f : E → ℝ with `ContDiffAt ℝ 2 f x₀` and `IsLocalMin f x₀`: `0 ≤ (fderiv ℝ (fderiv ℝ f) x₀ v) v` for all v. Route: the model's `hessian_nonneg_of_isLocalMin` (MaximumPrinciple.lean:397) with global ContDiff — localize its proof (it's a 1-D second-derivative test along lines through x₀: `secondDeriv_nonneg_of_isLocalMin` at MaximumPrinciple.lean:339 composed with the line map; ContDiffAt suffices since the test is local — mirror the proof with `ContDiffAt.comp` and local statements; alternatively use a smooth cutoff to reduce to the global lemma on a ball).
2. **Chart iterated-extDerivFun diagonal identity** (the report's displayed shape): `extDerivFun (fun y => extDerivFun f y (extend E v y)) x v = fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (chart x) v v` for f ContMDiffAt 2 at x. Tools: `extDerivFun`'s chart definition, the extend-section anchor properties (extends are chart-constant near their anchor — `mlieBracket_extend_extend_eventually_eq_zero`'s proof has the chart-representation machinery), ChartIdentification.lean's scalar patterns.
3. **Dual/CLM trace bridge**: identify `hessianDualAt`'s `TM x →ₗ Module.Dual` trace with the continuous-bilinear trace the model's `trace_dual_comp_nonneg` expects (finite-dim: `LinearMap.toContinuousLinearMap` is an equivalence; the trace is basis-sum either way — a `Finset.sum_congr` bridge).
4. **Assembly**: `laplacianAt_nonneg_of_isLocalMin` (1+2+3: at a local min, df=0 kills the first-order corrections in the identity from step 2 — the `extDerivFun_extDerivFun_extend_eq_hessianAt_add` correction terms carry a df factor, check and exploit) → `exists_scalarAt_isMinOn` (CompactSpace + continuity) → `hamilton_finite_time_singularity'` (witness discharged) + the packaged R_min statement. Done-report.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`, report names.
