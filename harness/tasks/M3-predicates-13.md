Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-13: the covariant cancellation — CLOSE TraceMetricVariationDerivAt

Read `harness/reports/M3-predicates-12_blocked.md` (exact reduced goal inside). On main, the Gram route is complete through differentiation: `traceMetricVariationAt_eq_sum_gram_inv` (trace = Σᵢⱼ Gram⁻¹ᵢⱼ·h(ext,ext)), `traceMetricVariationAt_extDerivFun_eq_gram_rhs` (its derivative in Gram product-rule form), plus ALL the cancellation ingredients from earlier tasks: `spatialMetricDerivAt_eq_leviCivita` (fixed-vector metric compatibility), `spatialMetricDualVectorDerivAt_inner_apply`, the swap machinery, `deltaGammaAt`/extend-section calculus.

ONE deliverable: the algebraic identification of the Gram RHS derivative with the contracted covariant derivative:
`extDerivFun (traceMetricVariationAt h) x w = Σᵢ covTensor2DerivAt h x w eᵢ ♯eⁱ` (the exact form `TraceMetricVariationDerivAt` states — match it literally).

The computation (classical, verify against the definitions):
- The Gram RHS derivative has three term groups: (a) ∂(Gram⁻¹)·h(ext,ext), (b) Gram⁻¹·∂h(ext,ext) — where ∂ of h-on-extend-sections relates to covTensor2DerivAt's flat term + Christoffel corrections via the extend-section derivative calculus (deltaGammaAt machinery differentiates extend sections; their y-derivative at x is the Christoffel action — find/prove the small lemma `extDerivFun (extend E p) = Γ`-shape if not present), and (c) at y=x, Gram(x) = metric matrix, ext = identity.
- ∂(Gram⁻¹) = −Gram⁻¹(∂Gram)Gram⁻¹; ∂Gram entries = ∂(g(ext,ext)) = metric-compatibility → Levi-Civita corrections (`spatialMetricDerivAt_eq_leviCivita`).
- Summing: group (a)'s Christoffel terms cancel group (b)'s Christoffel corrections EXACTLY (this is the ∇g=0 cancellation — the model's `fderiv_tensorMetricTrace_eq` algebra; the swap lemma reconciles slot orders), leaving precisely the covTensor2DerivAt contraction.

Work at y = x throughout (the predicate is pointwise at x; extend sections equal identity at x, Gram(x) = metric matrix — massive simplifications). Commit intermediate identities separately ((∂Gram = Γ-corrections), (extend derivative lemma), (the cancellation)). Then discharge `TraceMetricVariationDerivAt` + wire consumers + notes.

Exact-goal-state rule on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
