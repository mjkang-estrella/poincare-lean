Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-4: the traceless numerator bridges + evolution assembly

Read `harness/reports/M4-ivey-3_done.md` — its 5-item "remaining assembly" list is this task. On main: the FULL toolkit — rpow quotient calculus (ivey-3), the PROVEN eigenvalue improvement lemma (`TracelessPinchingEigenvalueImprovementLemma3_holds`, ivey-2), the traceless vocabulary + statement layer (ivey-1), and the entire goal-5 chain (|Ric|² parabolic inequality, scalar evolution, spectral machinery).

Deliverables (each its own commit; the report's items):
1. **Traceless numerator bridges**: `tracelessRicciNormSqAt = ricciNormSqAt − scalarAt²/3` derivative/Laplacian/gradient bridges (linear combination of PROVEN pieces: the |Ric|² parabolic machinery + the scalar-square parabolic form — pure linearity).
2. **The traceless parabolic inequality**: `d/dt |Ric°|² ≤ Δ|Ric°|² + [combined reaction/motion traces]` (subtract the two proven inequalities/equalities; mind that the R² one is an EQUALITY so subtraction preserves the ≤).
3. **Instantiate** the generic `quotient_rpow_spatial_expansion` with u = tracelessRicciNormSqAt, p = 2−δ (the report's item 3 with its listed regularity hypotheses).
4. **Vocabulary conversion** (item 4): the generic expansion → `tracelessPinchingGradientDrift3At` / `...DampingAt` / `...ReactionTermAt`.
5. **THE IMPROVED EVOLUTION INEQUALITY** (item 5): assemble with the eigenvalue reaction-sign lemma (spectral transport as in pinch-23 — the eigenbasis witness machinery is on main) → `satisfiesTracelessPinchingEvolutionAt_of_ricciFlow` under ε-pinching + admissible δ. Commit partials if the full chain exceeds budget; paste literal goals.

BUILD NOTE: be patient with builds; `lake env lean` per-file. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
