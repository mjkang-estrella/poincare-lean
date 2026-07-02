Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-3: basis-invariant trace bridge → TraceMetricVariationDerivAt

Read `harness/reports/M3-predicates-2_blocked.md` in full — it contains the exact 4-step plan this task executes. On main: `metricDualVectorAt_eq_metricRaiseContinuousAt` (the algebraic raise = continuous raise). The gap: `traceMetricVariationAt` is a per-fiber `Module.finBasis` trace; differentiating it requires computing it in a SMOOTH frame.

Execute the plan (each step its own commit):

1. **Basis invariance**: define the trace of a bilinear form h_y over an ARBITRARY basis of TM y (paired with its g-raised dual coframe: `Σᵢ h(eᵢ, ♯e^i)`-shape) and prove it is basis-independent = `traceMetricVariationAt` for the finBasis (standard linear algebra: the g-trace of the g-raised endomorphism is basis-free — go through `LinearMap.trace` if cleanest: `traceMetricVariationAt h = LinearMap.trace (raise ∘ h♭)`, which the RicciNorm.lean machinery already models with `scalarAt_eq_trace_ricciEndoAt`).
2. **Smooth-frame specialization**: specialize to the chart/trivialization frame (`trivializationAt` or the fixed chart frame from `mdifferentiableAt_gradient`'s proof) — the trace becomes a finite sum of smooth-in-y terms.
3. **Coframe differentiability**: raised dual coframe differentiable via `metricDualVectorAt_eq_metricRaiseContinuousAt` + the inverse-raise smoothness (goal-1/`mdifferentiableAt_gradient` technique).
4. **Discharge `TraceMetricVariationDerivAt`**: differentiate the smooth-frame sum; metric compatibility (`leviCivita_metricCompatibleAt`) cancels the frame-derivative corrections (model: `fderiv_tensorMetricTrace_eq`); conclude the covariant-trace commutation with honest h-regularity hypotheses + a satisfiability witness. Then restate downstream consumers (deltaGamma_innerTrace unconditional-modulo-classes).

This is the known-hard step of the predicate backlog — partial verified progress per step + refined report is success. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
