Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-31: the positive block = tensorDoubleDivergenceAt — sub-identity (a), the FINAL analytic block

Read `harness/reports/M3-predicates-30_done.md` and `M3-predicates-29_blocked.md`. On main: the trace block (b) is PROVEN; `deltaGammaDivergenceTraceHessianAssemblyAt_of_positiveBlock` waits on ONE identity:
`deltaGammaDivergenceTraceSecondDerivPositiveBlockAt (gt t₀) (timeDerivAt gt t₀) x = tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x`

Model analogue: sub-identity (a) — ½ΣΣ(T1+T2) = div div h (the model memory's decomposition: T1 contracts (♯bʲ,bⱼ) in the derivative/H-slots giving div, T2 the transposed pattern; both → ∇(div h) traced → div div h; T1↔T2 agree by Schwarz under the trace).

Closed route (each step its own commit):
1. Read the positive block's exact definition (the T1+T2 `covTensor2SecondDerivExpansionAt` patterns) and `tensorDoubleDivergenceAt`'s definition (trace of the covariant divergence of the raised variation — via `tensorDivergenceOneFormAt`/`covTensor2DerivAt`, predicates-13-era).
2. Inner contraction first: each T1/T2 summand's inner trace is a first-derivative divergence-form object — identify with `tensorDivergenceOneFormAt` values via the DISCHARGED first-order machinery (the entry bridges + `traceMetricVariationDerivAt` analogues for the divergence form — if a `divergenceFormDerivAt` first-order lemma is missing, prove it via the same Gram route; it's the div-analogue of the trace-commute).
3. Outer contraction: the outer trace of the ∇(div-form) = `tensorDoubleDivergenceAt` by its definition (+ Levi-Civita corrections cancelling via the slot machinery).
4. T1 = T2 under the double trace (Schwarz + `sum_metricDualVectorAt_contraction_swap`), absorbing the ½.
5. Sanity-check on the torus pattern FIRST (standing rule; the model guarantees the summed identity). Then: positive block proven → `DeltaGammaDivergenceTraceHessianAssemblyAt` DISCHARGED → BOTH assemblies closed → consolidated `scalarVariation_lichnerowicz` + Hamilton wrappers from honest classes + algebraic predicates only. Notes with the final remaining list (should be: ClosedContractedBianchiAt + 3 substitution predicates).

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
