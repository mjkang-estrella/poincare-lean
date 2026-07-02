Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-9: ONE lemma — differentiability of the raise field

SCOPE: exactly one lemma (plus its immediate consumers if it lands quickly). Across three prior tasks the recurring missing atom is:

`lemma mdifferentiableAt_metricDualVectorAt (g : ClosedSmoothRiemannianMetric n M) (φ : (E →L[ℝ] ℝ) or the coord-covector shape actually consumed) (x : M) : MDifferentiableAt I 𝓘(ℝ, E) (fun y => metricDualVectorAt g y φ) x`

(and/or its `extDerivFun`-value form with candidate `spatialMetricDualVectorDerivAt` — prove EXISTENCE first; the value identity second.)

MINING TARGET — this is 90% done in the repo already: `Poincare/Global/Laplacian.lean`'s `mdifferentiableAt_gradient` proves `MDifferentiableAt` for `y ↦ g.gradientAt y (df_y)` — the raise field applied to a VARYING covector. Read its full proof. Extract/refactor the sub-proof for the raise map with a FIXED covector (strictly easier: compose their argument with the constant covector field). If their proof factors through a reusable lemma already, just apply it. Use `metricDualVectorAt_eq_metricRaiseContinuousAt` to switch representations as needed.

Then, if the lemma lands with budget remaining:
1. Prove the `extDerivFun` VALUE equals `spatialMetricDualVectorDerivAt g x w φ` (the candidate whose g-pairing identity `spatialMetricDualVectorDerivAt_inner_apply` is already proven — nondegeneracy converts the pairing identity into the vector identity once differentiability is known).
2. Discharge `hSummand` of `traceMetricVariationProductRuleAt_of_spatiallyDifferentiable` (product rule with the now-differentiable second factor) and `hFrame` (finite-sum extDerivFun linearity).
3. If ALL land: chain to discharge `TraceMetricVariationProductRuleAt` unconditionally-modulo-classes and update notes.

If even the single lemma fails: the report MUST contain the exact failing Lean goal state pasted verbatim. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
