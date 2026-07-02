Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-15: the divergence assembly predicates

With `TraceMetricVariationDerivAt` discharged (traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt, on main), the Lichnerowicz chain's remaining named obligations are the two divergence assemblies consumed by `scalarVariation_lichnerowicz` (Global/ScalarVariation.lean; read their exact statements first):
- `DeltaGammaDivergenceTraceAssemblyAt` — the divergence of the inner-trace one-form = `tensorDoubleDivergenceAt h − ½·laplacianAt(traceMetricVariationAt h)`.
- `DeltaGammaContractionTraceAssemblyAt` — the second δΓ contraction trace = the other `½·laplacianAt(traceMetricVariationAt h)`.

Both are SECOND-derivative analogues of what just closed: the divergence of an inner-trace built from δΓ + h. The technology that won the 14-task siege applies directly:
1. **First**: restate/propagate — with TraceMetricVariationDerivAt discharged, restate `deltaGamma_innerTrace_eq` unconditional-modulo-classes (the task chain left `deltaGamma_innerTrace_eq_of_covTensor2Regular_traceProduct` etc. — wire the new discharge through; commit).
2. **Contraction assembly** (likely easier): `deltaGammaContractionDerivAt`'s trace — expand its definition; the contraction is `Σ` of δΓ-inner-trace-shaped terms whose trace was just computed; connect to `laplacianAt`'s definition (trace of the Hessian, whose gradient/Hessian machinery is on main with `hessianAt_symm'`). Use the Gram route for any new trace derivative: the same `traceMetricVariationAt_eq_sum_gram_inv` pattern applies to the tr-h scalar field.
3. **Divergence assembly**: `deltaGammaDivergenceAt`'s trace = divergence of the inner-trace field (proven = div h − ½d(tr h) pointwise) — differentiate the field identity in the Gram/extend frame (the SAME product rule + cancellation, one derivative higher: the pieces `gram_h_extDerivFun_contraction_...`, `covTensor2DerivAt` calculus, and the second-derivative machinery from the goal-1/Hessian files are all on main). Named-honest-hypothesis fallback per sub-identity if a genuinely new second-order fact blocks (state exactly, use directly).
4. If both discharge: `scalarVariation_lichnerowicz` unconditional-modulo-classes; update `HamiltonScalarEvolutionPredicatesAt` consumers; notes.

Exact-goal-state rule on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
