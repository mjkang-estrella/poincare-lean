Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-1: discharge TraceMetricVariationDerivAt + covTensor2DerivAt slot-linearity

First predicate-discharge task for `HamiltonScalarEvolutionPredicatesAt` (Global/ScalarEvolution.lean; see also harness/reports/M3-scalar-variation_notes.md latest status). Both targets are first-order metric-compatibility facts with proven model analogues.

1. **covTensor2DerivAt slot-linearity** (feeds the hTraceSwap adapter `CovTensor2DerivTraceSwapAt`): prove additivity/homogeneity of `covTensor2DerivAt` in its tensor-slot arguments from spatial differentiability hypotheses on the variation h (the definition composes extDerivFun + connection corrections — each is linear in the slots given the differentiability side conditions; the notes name this as "analytic regularity work"). Then discharge `CovTensor2DerivTraceSwapAt` where it is consumed.

2. **TraceMetricVariationDerivAt** (∇ commutes with the metric trace): the derivative of `traceMetricVariationAt h` along a direction equals the contracted covariant derivative of h. Model analogue: `fderiv_tensorMetricTrace_eq` (ModelLaplacian.lean ~10787-10835 per the frontier memory — the varying raised index handled via the inverse-raise derivative + Christoffel-correction cancellation by ∇g=0). Closed-manifold route: differentiate the finite basis-sum defining the trace; the ∂(raise) term = −♯h♭♯-analogue (already proven as `metricRaiseDerivAt` machinery in variation-6 — check reusability); metric compatibility (`leviCivita_metricCompatibleAt`) cancels the Christoffel corrections. Honest spatial-regularity hypotheses (h differentiable fields etc.) are fine — but they must be SATISFIABLE; add a satisfiability witness (e.g. for h = timeDerivAt of a MetricFlowRegularAt family, or at minimum the zero/static case).

3. Propagate: restate whichever downstream theorems (deltaGamma_innerTrace_eq', the divergence assemblies' inputs) simplify with these discharged.

No sorry/axiom; blocked → greens + notes. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
