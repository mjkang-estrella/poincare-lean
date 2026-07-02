Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation-8: hTraceSwap + hTraceDeriv + divergence assembly

Read `harness/reports/M3-scalar-variation_notes.md` (latest status). On main: `deltaGamma_innerTrace_eq` (inner δΓ trace = div h − ½ d(tr h)) proven modulo two first-order obligations, and `deltaRicciAt_raised_trace_eq_deltaGamma_contractions` (the hDeltaGammaTrace LHS as two δΓ contractions). Remaining chain to hDeltaGammaTrace: (1) the two obligations, (2) the divergence-of-inner-trace step.

Deliverables (each its own commit):

1. **hTraceSwap**: the contracted derivative/first-slot swap — `Σᵢ` of a bilinear-trace with raised/lowered slot exchange. Model analogue: `sum_raised_contraction_swap` (ModelLaplacian.lean, proof via basis expansion + inverse-metric symmetry — the coefficient identity Σⱼ M^{ja}Φ^c_j = Σ_k Φ^c_k M^{ka} for symmetric M). Port to the closed fiber: TM x is finite-dim with the symmetric nondegenerate g-form; the proof is pure linear algebra per-fiber (no manifold content) — consider proving it abstractly over any finite-dim inner-product-like pairing so it's reusable.
2. **hTraceDeriv**: contracted ∇h trace = derivative of tr_g h. Model analogue: `fderiv_tensorMetricTrace_eq` (the ∂(G⁻¹) term cancels Christoffel corrections by ∇g = 0). Closed-manifold content: differentiate `traceMetricVariationAt` (already defined) along a direction, commute the trace with the covariant derivative using metric compatibility of `g.leviCivita` (`leviCivita_metricCompatibleAt`) — the raised-index derivative correction cancels.
3. Restate `deltaGamma_innerTrace_eq'` unconditional (modulo only the honest regularity classes).
4. **Divergence assembly**: take the covariant divergence of the inner-trace identity: `Σⱼ ∇_{♯eʲ}[innerTrace](eⱼ) = tensorDoubleDivergenceAt h − ½·laplacianAt(tr h)`, combine with the second δΓ contraction (which gives the other ½·laplacianAt(tr h) — mirror the model's `ricciDeriv_raised_trace_eq_doubleDiv_sub_curvedLaplacian`) → **discharge hDeltaGammaTrace** → `scalarVariation_lichnerowicz` final. Named-honest-hypothesis fallback allowed per sub-identity if a step stalls (state exactly, use directly).

No sorry/axiom; blocked → greens + notes. `lake build Poincare.Global.ScalarVariation`, report names.
