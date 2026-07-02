Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-39: prove ClosedRicciDerivativeExpansionAt (ONE atom)

SCOPE: one witness. Read `harness/reports/M3-predicates-38_done.md`. On main: `ClosedRicciDerivativeExpansionAt g y` (read its exact definition — the moving-point Ricci derivative expansion witness) with bridges (1)/(2) chained behind it; proving it near x (∀ᶠ form) discharges both.

Target: `theorem closedRicciDerivativeExpansionAt_of_[honest classes] : [g-smoothness/C³ classes] → ∀ᶠ y in 𝓝 x, ClosedRicciDerivativeExpansionAt g y`.

Content: the derivative of the closed Ricci entries in terms of the curvature covariant derivative — i.e. differentiate `ricciBilinearAt` (a g-contracted curvature trace) at moving points. The pattern is the discharged trace-derivative theorem one level up:
1. Express the Ricci entries near y via the anchored Gram formula (the Ricci is a trace of the curvature endomorphism — `ricciBilinearAt`'s definition + the Gram/dual-basis trace machinery; the `traceMetricVariationAt_eq_sum_gram_inv` pattern applied to curvature-slot entries).
2. Differentiate: entry derivatives of curvature values → `closedCurvatureCovDerivAt` + Christoffel corrections (the curvature-value entry bridge — the same product-rule shape as `DeltaGammaEntryDerivativeBridgeAt`'s proof, with curvature values in place of δΓ values; curvature values' differentiability from g C³ — the metric's ∞-smoothness gives all orders).
3. The Gram-inverse derivative terms cancel against the corrections (the `gram_inv_deriv_contraction_eq_leviCivita_corrections` pattern).
4. Conclude the witness in its exact frozen shape; the ∀ᶠ form via the neighborhood-uniform classes (the ContMDiffAt vocabulary).

Note: the metric g here is FIXED (one time slice) and ∞-smooth — no time-family subtleties; every regularity input derives from `g.contMDiff_inner`. This should be cleaner than the timeDerivAt campaigns.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
