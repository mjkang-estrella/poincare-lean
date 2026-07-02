Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-30: the trace block (T3) = Hessian trace of tr h — sub-identity (b)

Read `harness/reports/M3-predicates-29_blocked.md`. On main: `deltaGammaDivergenceTrace_sndDerivAt_blocks` splits the summed keystone into a positive block (→ div div h, separate task) and the TRACE BLOCK. This task: prove
`deltaGammaDivergenceTraceSecondDerivTraceBlockAt (gt t₀) (timeDerivAt gt t₀) x = Σⱼ g.hessianAt (traceMetricVariationAt g H) x (bⱼ) (♯bⱼ)` (the frozen RHS shape from the report — the Hessian trace of tr h).

This is the closed analogue of the model's `sum_sum_covTensor2SndDeriv_eq_curvedLap` (sub-identity (b), whose model proof route is in the repo memory: the 2nd-order trace-commute `sum_covTensor2SndDeriv_Hslot_trace` + Hessian-symmetry raise-swap). Closed route:
1. The trace block's summands are `covTensor2SecondDerivExpansionAt` terms whose H-SLOTS are contracted (the T3 pattern) — identify the inner contraction with the FIRST-ORDER trace-commute, already DISCHARGED: `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt` says the contracted ∇h trace = derivative of tr h. Apply it INSIDE the outer derivative (the C² classes give the regularity; the trace block = outer derivative of the inner contracted trace − corrections).
2. The outer derivative of [derivative of tr h] = second derivative of tr h; identify with `g.hessianAt (tr h)` via `extDerivFun_extDerivFun_extend_eq_hessianAt_add` (on main from predicates-18) + the closed Schwarz lemmas + `hessianAt_symm'` for any slot swap.
3. Sum over j → the frozen RHS. Sanity-check on the torus pattern BEFORE proving (standing rule).
4. If it closes, chain: trace block done; the assembly then waits only on the positive block (note it in the report).

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
