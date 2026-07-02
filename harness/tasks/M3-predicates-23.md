Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-23: PROVE DeltaGammaEntryDerivativeBridgeAt (the triple product rule)

SCOPE: one theorem. On main: `DeltaGammaEntryDerivativeBridgeAt` (Global/ScalarVariation.lean — read its exact statement: the derivative of `y ↦ g.inner y (deltaGammaAt gt t₀ y (extend p) (extend w)) (extend q)` = `g(covDeltaGammaDerivAt, q)` + three Levi-Civita slot corrections) with static witness; everything downstream is proven and waiting (`...of_entryBridge` cascade).

Target: `theorem deltaGammaEntryDerivativeBridgeAt_of_[honest classes] : [C²/flow-regularity hypotheses] → DeltaGammaEntryDerivativeBridgeAt gt t₀ x`.

The computation — a triple product rule where every factor's derivative is already a merged lemma:
1. ∂[g_y(A_y, B_y)] = (∂g)(A,B) + g(∂A,B) + g(A,∂B): the ∂g-term is `spatialMetricDerivAt_eq_leviCivita` (on main); differentiability side conditions from the ContMDiff entry classes.
2. ∂[extend-sections]: the extend-derivative calculus (predicates-13's `covariant extension-slot derivative bridge`, commit 9cd80995 — find those lemma names in the file; they identify extend-section derivatives with Christoffel actions).
3. ∂[deltaGammaAt-values along y]: `covDeltaGammaDerivAt`'s definition = this flat derivative + Christoffel slot corrections — rearrange definitionally. The needed differentiability of `y ↦ deltaGammaAt gt t₀ y (extend p)(extend w)` values: derive from the C² time-space classes (deltaGammaAt is a time-derivative of connection values; its spatial regularity needs the joint class — `MetricFlowRegularAt`/`TimeVariationExtSecondDifferentiableAt` vocabulary on main; if a joint field is genuinely missing add it honestly + static witness).
4. Assemble; sign/slot bookkeeping against the frozen statement. Then confirm the cascade: `DeltaGammaContractionTraceHessianDerivativeAt` discharged via the `..._of_entryBridge_entries_contMDiffAt` wrapper (on main) — state the final composed theorem.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
