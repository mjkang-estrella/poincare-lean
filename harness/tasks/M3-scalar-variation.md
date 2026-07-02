Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation: time-derivative of scalar curvature along a metric family (exploration + first layer)

Goal-2 step (c). Context on main: `Global/MetricVariation.lean` (timeDerivAt vocabulary + Ricci-flow rewiring), `Global/Curvature.lean` (hypothesis-free `g.ricciAt`/`g.scalarAt` via the now-smooth canonical connection), `Global/ScalarEvolution.lean` (target `HamiltonScalarEvolutionProgram`). The port template: `ModelLaplacian.lean` proves the single-chart chain — study `hamilton_scalar_evolution_of_bianchi`, `ricciDeriv_*`, `lichnerowiczLaplacian_*`, and the keystone route summarized at the top of `RIEMANNIAN_FOUNDATION.md`/`harness/reports/manifold_assets.md` §frontier.

This is EXPLORATION + FOUNDATION (full formula is multi-session). Deliverables in priority order, NEW file `Poincare/Global/ScalarVariation.lean` (+ root import):

1. **Differentiability layer**: for a time-family `gt` with genuine smoothness-in-t hypotheses (state them honestly — e.g. t-differentiability of the inner products plus whatever the curvature layer needs), prove `DifferentiableAt ℝ (fun t => (gt t).scalarAt x) t₀` — or, if full generality stalls, prove it under stronger but honest hypotheses (e.g. an explicitly-differentiable family of connection values). This is the `HasDerivAt` prerequisite of `SatisfiesHamiltonScalarEvolutionAt`.
2. **Variation decomposition skeleton**: `scalarAt` is built from traces of `ricciBilinearAt` of the canonical connection. Prove the first decomposition step: the t-derivative of a trace = trace of the t-derivative (finite-dimensional fiber, `deriv`-through-finite-sum), reducing δR to the t-derivative of Ricci values. State (as a definition/`Prop`, proven or not — mark honestly) the target Lichnerowicz shape `δR = tensorDoubleDivergence-analogue − Δ(tr h) − ⟨h, Ric⟩` in the closed-manifold vocabulary, citing the model analogues by name in comments.
3. **The δΓ object**: define the connection-variation `deltaGammaAt gt t₀ x : TM x → TM x → TM x` (t-derivative of the canonical connection's values, with honest differentiability hypotheses) + tensoriality lemmas if reachable. The model file's `christoffelDeriv`/`covDeltaGammaDeriv` are the template.
4. Update `harness/reports/M3-scalar-variation_notes.md` with the decomposition of remaining work into ≤6 crisply-stated subtasks with exact Lean statements.

Commit each green piece. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
