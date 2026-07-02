Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-8: close TraceMetricVariationProductRuleAt (ONE obligation only)

SCOPE: exactly ONE theorem. Read `harness/reports/M3-predicates-7_blocked.md` item 1. On main: `TraceMetricVariationProductRuleAt` (a Prop-shaped obligation), `traceMetricVariationDerivAt_of_productRule_raiseCancellation` (consumes it), `VariationSpatiallyDifferentiableAt` (fixed-vector HasFDerivAt for h), and the raise-map machinery (`metricDualVectorAt_eq_metricRaiseContinuousAt`, `spatialMetricDualVectorDerivAt`).

Target: `theorem traceMetricVariationProductRuleAt_of_spatiallyDifferentiable : VariationSpatiallyDifferentiableAt h x → [g-smoothness/other honest side conditions] → TraceMetricVariationProductRuleAt g h x ...`

The content is a finite-sum product rule in the FIXED fiber E:
1. First prove `hasFDerivAt_metricDualVectorAt`: `y ↦ metricDualVectorAt g y φ` HasFDerivAt with the candidate `spatialMetricDualVectorDerivAt` — via the CLM-inverse derivative. The metric-CLM field's differentiability: mine how `mdifferentiableAt_gradient` (Global/Laplacian.lean) differentiates the metric/raise — its proof contains the needed `HasFDerivAt`/`ContMDiffAt` pieces for exactly this composite; also `hasFDerivAt_inverse_raise` (ModelLaplacian, flat) applies since fibers = E by rfl. If the candidate's formula mismatches the inverse-rule output, prove the algebraic identity separately (both are −♯(∂g)♯ shapes).
2. Then the sum: `traceMetricVariationAt h y = Σᵢ h y eᵢ (metricDualVectorAt g y (coord i))` — differentiate summand-wise: `HasFDerivAt.comp`/`.clm_apply`/bilinear product rule combining the fixed-vector h-derivative (from the class; for the varying second slot use h y eᵢ's linearity in that slot — if plain-function h lacks a CLM packaging, ADD the honest hypothesis field or use finite-dimensionality to build the CLM) with step 1. Sum via `HasFDerivAt.sum`.
3. Conclude the obligation exactly as stated (match its statement literally — do not modify it).

Every prior task around this predicate produced verified partials — this one should CLOSE this obligation. If you genuinely cannot, the report must contain the exact failing Lean goal (copy-paste the goal state), not a prose description. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
