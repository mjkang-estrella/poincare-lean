Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-32: the three substitution predicates (algebraic tail)

The analytic chain is complete on main. Remaining for the Hamilton theorem: 4 predicates; this task takes the THREE substitution ones (ClosedContractedBianchiAt is separate):
- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt` — under the flow, `tensorDoubleDivergenceAt (timeDerivAt) = tensorDoubleDivergenceAt (−2·ricci)` -shape (read exact statements in Global/ScalarVariation.lean / ScalarEvolution.lean).
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt` — the Laplacian-of-trace substitution: `laplacianAt (tr timeDerivAt) = laplacianAt (−2·R)`-shape.
- `TensorDoubleDivergenceNegTwoRicciLinearityAt` — pull the −2 scalar out of the double divergence.

Route:
1. The pointwise h = −2Ric identification exists (`isClosedRicciFlowSolutionAt_timeDerivAt` + the variation-9 bridge — find `timeDerivAt ... = −2 * ricciAt`-form lemmas on main). The substitution predicates need this equality as FIELDS near x (the divergence/Laplacian differentiate in y) — the flow hypothesis `IsClosedRicciFlowSolutionAt` is pointwise-at-x; take the honest `∀ᶠ y in 𝓝 x`-form hypothesis (solution near x — the natural flow hypothesis; the `hNear` patterns in the file show the shape) and derive the field equality on the neighborhood.
2. Linearity/scaling: `tensorDoubleDivergenceAt`/`laplacianAt`/`traceMetricVariationAt` in h — scalar-multiple lemmas (the definitions are traces of derivative compositions; `smul` commutes through under the differentiability side conditions; several `_smul`/`_add` lemmas exist — extend where missing, honest hypotheses fine).
3. `traceMetricVariationAt (−2·ricci) = −2·scalarAt` (trace of Ricci = scalar — `scalarAt_eq_trace_ricciEndoAt`/RicciNorm machinery; mind the raised/lowered conventions).
4. Discharge all three; consolidated Hamilton wrapper (remaining: regularity + ClosedContractedBianchiAt only); notes.

Standing sanity-check rule applies (static/torus). Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
