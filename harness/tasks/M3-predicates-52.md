Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-52: the raw cyclic bracket/output derivative block (last surviving group)

Read `harness/reports/M3-predicates-51_progress.md` — the correction block is expanded into the residue vocabulary with NO orientation mismatch; the survivors are the raw cyclic `extDerivFun` bracket/output DERIVATIVE terms.

Classical facts that kill this block (evaluate which applies to the actual surviving terms — paste them first):
1. **Anchored extend-brackets**: at the anchor point x, the canonical extend sections' brackets/derivative combinations simplify drastically — check `extend`'s definition: if `extDerivFun`-of-extend at the ANCHOR vanishes or equals the Christoffel action (the extend-calculus lemmas from variation-2/predicates-13 record exactly this), the bracket entries at x collapse. But NOTE the identity must hold at every y NEAR x (∀ᶠ) — the anchored simplification alone isn't enough UNLESS the final consumers only need the anchored value (check: `eventually_closed_cyclic_second_bianchi_of_inner_sum` needs ∀ᶠ y... BUT each y can use ITS OWN anchor — the cyclic identity is pointwise-tensorial in (u,v,w,z,q), so proving it AT each y with extend sections anchored AT y suffices if the statement's sections re-anchor; verify the quantifier structure and exploit it — this is likely the key simplification).
2. **Jacobi/Schwarz on brackets**: the cyclic sum of derivative-of-bracket terms is the Jacobi identity's derivative shadow — Mathlib's `VectorField.mlieBracket` has Leibniz/Jacobi lemmas (`mlieBracket_jacobi`?? — search); alternatively the bracket of extend sections reduces to flat derivative differences where flat Schwarz closes it.

Route: paste the exact surviving block → try the re-anchoring observation (1) first — it may collapse everything to already-proven anchored lemmas → else (2). Then: assemble → cyclic Bianchi → hMiddle → contracted Bianchi → **HAMILTON THEOREM** + historic done-report (the full chain from predicates-51's list).

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
