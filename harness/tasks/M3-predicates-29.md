Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-29: the summed divergence trace, directly (the true keystone shape)

Read `harness/reports/M3-predicates-27_blocked.md` AND `M3-predicates-28_blocked.md`: two pointwise intermediates were REFUTED on the flat torus. The lesson (mirroring the model's history exactly): the identity holds ONLY under the full double trace. The true target is the SUMMED statement — read the frozen `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` / `DeltaGammaDivergenceTraceHessianAssemblyAt` (Global/ScalarVariation.lean) and FIRST sanity-check the summed statement on the torus pattern (h₁₁ = cos y): the double sum should make LHS = RHS (the model's proven keystone guarantees the summed identity is true — its single-chart form is `deltaGammaDivergenceTrace = div div h − ½Δ(tr h)`, ModelLaplacian, proven). Record the sanity check in the report.

Then prove the summed statement directly (each step its own commit):
1. Expand the full double-sum LHS via `covDeltaGamma_koszul` (on main): Σᵢ over the koszul expansion gives ΣᵢΣ[3 covTensor2SecondDerivExpansionAt patterns] − corrections. This mirrors the model's `deltaGammaDivergenceTrace_sndDeriv` (= ½ΣΣ(T1+T2−T3), commit 8b44000b in the model's history — where the corrections cancelled exactly via `ring` after the Koszul substitution; expect the same).
2. Evaluate the three double-trace groups (the model's sub-identities): (T1+T2) → `tensorDoubleDivergenceAt h` [model: `sum_sum...eq tensorDoubleDivergence`]; (T3) → `laplacianAt (traceMetricVariationAt h)` [model: `sum_sum_covTensor2SndDeriv_eq_curvedLap` via the trace-commute — the closed first-order trace-commute is DISCHARGED (`traceMetricVariationDerivAt...`); its once-differentiated/summed form is the piece to build here, using the C² classes + the closed Schwarz lemmas].
3. Assemble → the summed divergence assembly discharged → with the contraction side (closed) → `hDeltaGammaTrace` → `scalarVariation_lichnerowicz` from honest classes + the algebraic predicates only.
4. Notes with final list.

This is the true summit of the analytic work — partial groups + exact goals = success. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
