Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-2: the spatial raised-basis derivative bridge → TraceMetricVariationDerivAt

Read `harness/reports/M3-predicates-1_blocked.md`. On main: `CovTensor2DerivTraceSwapAt` discharged; `TraceMetricVariationDerivAt` (∇ commutes with metric trace of the variation h) blocked on ONE bridge: the spatial derivative of the raised basis field `y ↦ metricDualVectorAt g y ((finBasis).coord i)` and its metric-compatibility cancellation. Time analogue already proven: `metricRaiseDerivAt = −♯∘h♭∘♯` (variation-6). Model template: `fderiv_tensorMetricTrace_eq` (ModelLaplacian.lean ~10787) — inverse-raise derivative + Christoffel cancellation via ∇g=0. The goal-1 chain also built exactly this kind of spatial smoothness through charts: `mdifferentiableAt_gradient`'s proof (Global/Laplacian.lean) differentiates a raised field — inspect and reuse its technique/lemmas.

Deliverables (each its own commit):

1. **Spatial raise-derivative lemma**: for the closed metric g, the field `y ↦ ♯_y φ(y)` (raise of a differentiable covector field, or specialize to the coord/basis case actually needed by `traceMetricVariationAt`'s definition) is spatially differentiable with derivative = raise of the covector derivative MINUS the metric-derivative correction `♯(∂g)♯`-form — the spatial analogue of `metricRaiseDerivAt`. Use the chart route from `mdifferentiableAt_gradient` for existence and the Koszul/metric-compatibility identities for the formula.
2. **Christoffel cancellation**: combine with `leviCivita_metricCompatibleAt` — the raise-derivative correction cancels the connection correction terms in the covariant derivative of the trace (∇g = 0), yielding: directional derivative of `traceMetricVariationAt h` = contracted `covTensor2DerivAt` of h. This IS `TraceMetricVariationDerivAt` — discharge it (with honest spatial-differentiability hypotheses on h, plus a satisfiability witness for h = timeDerivAt of a regular flow OR the static case if the flow case stalls).
3. **Propagate**: restate `deltaGamma_innerTrace_eq` fully unconditional (modulo regularity classes only) and update the divergence-assembly predicates' inputs if they simplify.

No sorry/axiom; blocked → greens + refined report. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
