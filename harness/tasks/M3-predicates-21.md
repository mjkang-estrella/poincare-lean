Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-21: the moving-frame identity via the anchored Gram reformulation

Read `harness/reports/M3-predicates-20_blocked.md`. ONE theorem remains for the contraction-side assembly: `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x` — the derivative of the moving fiberwise trace field `y ↦ deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y)` equals the fixed-base contraction `deltaGammaContractionDerivAt gt t₀ x u w`-shape.

KEY STEER — do NOT fight the per-fiber `Module.finBasis` directly. Reformulate the FIELD by the anchored Gram identity, the exact move that closed the first-order siege:
1. **Anchored field identity**: prove `deltaGammaFirstSlotTraceFieldAt gt t₀ y v = [anchored Gram expression in (x-anchored extend frame, gramMatrix g x y)⁻¹, scalar entries at y]` for y in the invertibility neighborhood of x — the field-level analogue of `traceMetricVariationAt_eq_sum_gram_inv` (whose proof pattern is on main; the field is a δΓ trace, and the basis-invariance lemma applies per fiber, so the per-fiber finBasis can be swapped for the anchored gramFrameBasis at each y — `gramFrameBasis` machinery from predicates-12).
2. **Differentiate the anchored expression** at x: products/inverses of scalar entries, all C² by the discharged trace-C²/entry-ContMDiff classes (on main from predicates-20) — product rule + `gramMatrix_inv_extDerivFun_eq_neg_sum` + the Levi-Civita cancellation lemmas.
3. **Identify with `deltaGammaContractionDerivAt`**: at x the anchored frame is the finBasis and extensions are identity; match the resulting expression with the fixed-base contraction's definition (the trace-cyclicity step the report mentions — the closed `sum_metricDualVectorAt_contraction_swap` + the Schwarz lemmas handle the reorderings).
4. **Chain**: the discharged identity + trace-C² (done) → `deltaGammaFirstSlotTraceFieldHessianAt_of_trace_extSecond` fires → `DeltaGammaContractionTraceHessianDerivativeAt` discharged → CONTRACTION ASSEMBLY CLOSES. Restate Hamilton wrappers; notes.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
