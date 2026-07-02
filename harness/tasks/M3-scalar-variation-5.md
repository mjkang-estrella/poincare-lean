Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation-5: the Lichnerowicz trace identity (roadmap subtask 5 core)

Read `harness/reports/M3-scalar-variation_notes.md`. On main: `deriv_scalarAt_eq_trace_deltaRicciAt_of_metricFlowRegularAt` gives dR/dt as a trace of `deltaRicciAt` (built from `deltaGammaAt` contractions: `deltaGammaDivergenceAt − deltaGammaContractionDerivAt` shapes); the RHS vocabulary `tensorDoubleDivergenceAt`, `traceMetricVariationAt`, `metricVariationRicciPairingAt` exists. Model template: the ENTIRE keystone journey is documented in the repo memory and completed in ModelLaplacian.lean — study `deltaGammaDivergenceTrace_sndDeriv`, `sum_sum_covTensor2SndDeriv_eq_curvedLap`, `deltaGamma_innerTrace_eq`, `g_christoffelDeriv` (the Koszul 3-term form of g·δΓ), `ricciDeriv_raised_trace_eq_doubleDiv_sub_curvedLaplacian`.

Target (subtask 5): the algebraic bridge from the δΓ-trace to the Lichnerowicz shape:
`trace(deltaRicciAt-expression) = tensorDoubleDivergenceAt (gt t₀) h x − laplacianAt(trace h) − ⟨h, Ric⟩-term` where `h = timeDerivAt gt t₀ x` — matching `scalarVariation_lichnerowicz_shape` in the notes.

Key structural insight from the model (use it): the identity DECOMPOSES:
(i) the Koszul inner-trace: `Σᵢ g(δΓ(eᵢ, ♯eⁱ), w) = (div h)(w) − ½ d(tr h)(w)` — from differentiating the Koszul formula (`deltaGammaAt` values are determined by the metric variation via the differentiated Koszul formula: δΓ = ½ g⁻¹(∇h-terms); PROVE THIS FIRST — `deltaGamma_koszul`: the time-derivative of the Koszul characterization gives 2·g(δΓ(v,w),z) = ∇h 3-term form; this is the master identity everything else contracts from).
(ii) trace contractions of (i) in the two slot-orders give the divergence and Laplacian terms.
(iii) the ⟨h,Ric⟩ term arises from differentiating the metric inverse in the raised trace (already exposed in `ricciEndoHasDerivAt_of_ricciBilinearHasDerivAt`'s raise' term — check whether the pairing term is ALREADY separated there; if so subtask 5 may reduce to (i)+(ii)).

Work bottom-up, each lemma its own commit: (1) `deltaGamma_koszul` master identity; (2) its inner-trace contraction; (3) the divergence-order trace; (4) assembly. This is the hardest task issued so far — partial verified progress + a refined decomposition in the notes is a fully successful outcome. Do NOT force the final assembly with unproven intermediate hypotheses UNLESS each is stated as an honest named hypothesis with a comment marking it as an open obligation (the hCurv pattern — it worked).

No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
