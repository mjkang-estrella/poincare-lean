Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-4: TraceMetricVariationDerivAt via the trace-linearity route (frame-free)

Read `harness/reports/M3-predicates-3_blocked.md`. Steps 1-3 of the frame plan are on main (basis-invariant trace, chart-frame specialization, coframe rewrite). Step 4 stalled on differentiable-frame-FIELD machinery. ORCHESTRATOR ROUTE SUGGESTION — try this FIRST (frame-free):

**Route A (trace linearity).** `traceMetricVariationAt h y = LinearMap.trace ℝ (TM y) (endo_y)` where `endo_y = (raise_y) ∘ (h♭_y)` (the basis-invariant bridge from predicates-3 should make this available or nearly so). The trace of an endomorphism of the FIXED model-space fiber: in the closed context all fibers TM y are definitionally E (single ChartedSpace model), so `y ↦ endo_y : E →L[ℝ] E` is a map into ONE fixed space — no bundle transport needed for its differentiability. Then:
1. `d/dy tr(endo_y) = tr(d/dy endo_y)` — trace is a continuous linear functional on E →L E (finite-dim); `HasFDerivAt.comp` with `LinearMap.trace`-as-CLM (Mathlib: `ContinuousLinearMap.trace`? or build via `LinearMap.trace` + finite-dim continuity — `LinearMap.toContinuousLinearMap`).
2. `d/dy endo_y` by product rule: `(d raise_y) ∘ h♭ + raise ∘ (d h♭_y)` — the raise derivative is the spatial `−♯(∂g)♯` (the `metricDualVectorAt_eq_metricRaiseContinuousAt` + inverse-derivative tools; ModelChristoffel/ModelLaplacian `hasFDerivAt_inverse_raise` patterns).
3. Convert flat derivative → covariant (`covTensor2DerivAt` contraction): the Christoffel corrections from ∇h's definition pair off against the raise-derivative term by metric compatibility (∇g = 0, `leviCivita_metricCompatibleAt`) — the trace kills the mismatch exactly as in the model's `fderiv_tensorMetricTrace_eq`.
4. Discharge `TraceMetricVariationDerivAt`; restate `deltaGamma_innerTrace_eq` modulo classes only; add the flow-family satisfiability witness if reachable.

**Route B fallback**: continue the frame-field plan from the blocked report if Route A hits a genuine wall (e.g. the fibers are NOT definitionally identified in the current encoding — check early; if TangentSpace I y reduces to E definitionally, Route A stands).

Check the fiber-identification question FIRST and record the answer in the notes. No sorry/axiom; partials + refined report = success. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
