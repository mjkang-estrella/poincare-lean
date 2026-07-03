Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-1: Ricci tensor evolution — statement layer + variation groundwork

GOAL 4 opener: toward Hamilton–Ivey pinching (M4), the next need is the EVOLUTION EQUATION FOR THE RICCI TENSOR under Ricci flow: ∂ₜ Ric = Δ_L Ric (Lichnerowicz Laplacian) + quadratic curvature terms. This is a statement-layer + groundwork task (the full proof is a campaign; do NOT attempt it).

On main (the toolkit): `deltaRicciAt` + `ricciVariation_eq_deltaGamma_contractions'` (the t-derivative of Ricci in δΓ form — ALREADY PROVEN under MetricFlowRegularAt), `deltaGamma_koszul`/`covDeltaGamma_koszul`, the full Gram machinery, `IsClosedRicciFlowSolutionAt`, `timeDerivAt = −2 Ric` under the flow.

Deliverables (each its own commit):
1. **Specialize δRic to the flow**: under `IsClosedRicciFlowSolutionAt`-near-x + regularity classes, substitute h = −2·Ric into `deltaGamma_koszul` → `deltaGammaAt` in ∇Ric 3-term form → `deltaRicciAt` = explicit second-derivative-of-Ric contractions (the "rough Laplacian of Ric + lower-order" shape). Land whatever honest identities this substitution gives directly (linearity in h is proven; this is mostly rewiring).
2. **Vocabulary**: `def lichnerowiczLaplacianAt` for symmetric 2-tensors (rough Laplacian + curvature action terms — mirror the model's `lichnerowiczLaplacian_*` definitions in ModelLaplacian; use the covTensor2SecondDeriv-style objects on main) and the curvature-quadratic `def ricciQuadraticAt` (Rm∗Ric contractions).
3. **The target statement**: `def SatisfiesRicciEvolutionAt (gt) (t₀) (x) : Prop` — HasDerivAt of `(gt t).ricciAt x u w` equal to `lichnerowiczLaplacianAt ... + ricciQuadraticAt ...` — the honest Prop-level target (like HamiltonScalarEvolutionProgram was), documented as unproven, with the trace-consistency SANITY CHECK: taking the metric trace of the target statement must recover the PROVEN scalar evolution shape (state this consistency as a lemma modulo the classes if tractable, else as an informal check in the report).
4. Notes with the decomposition of the remaining proof into ≤6 subtasks.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
