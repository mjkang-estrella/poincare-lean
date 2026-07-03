Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-17: RE-DERIVE the correct fold, coefficient-pinned by test metrics

Read `harness/reports/M4-prep-16_blocked.md` (the space-form refutation — LHS ≡ 0, proposed RHS ≠ 0) and `M4-prep-15_blocked.md` (where the false fold target came from). The definitions are validated; the M4-prep-15 ASSEMBLY DECOMPOSITION mis-derived the fold target. This task re-derives it correctly:

1. **Symbolic re-derivation**: recompute, from the definitions on main, what `Σᵢ CA(bᵢ,u,w,♯bⁱ) + Σᵢ CA(bᵢ,w,u,♯bⁱ)` actually equals in the vocabulary (`lichnerowiczCurvatureAt`, `ricciActionOnTensorAt`, `ricciQuadraticAt`, possibly additional Riemann-contraction terms the vocabulary lacks — if a genuinely new contraction shape appears, define it honestly). METHOD: expand CA's definition on the Ricci field; use the curvature symmetries + first Bianchi to reorganize; PIN THE COEFFICIENTS with TWO test patterns computed informally in the report: (a) the space form (LHS = 0 — the report's data), (b) a product/non-Einstein pattern if needed to separate the Lichnerowicz and Ric-action coefficients. The correct fold must reproduce both.
2. **Check the downstream shape**: with the corrected fold, verify (informally first) that the M4-prep-15 Hessian-cancelled assembly still lands on the FROZEN `RicciSecondDerivCurvatureCommutationAt` RHS (rough − 2·Lich + RicAction + quad). If the frozen RHS itself is inconsistent with the corrected algebra (i.e. `SatisfiesRicciEvolutionAt`'s RHS is wrong), that's a deeper definition correction — refute exactly with the test-metric data and STOP for orchestrator review (do not silently fix the frozen evolution statement).
3. If the corrected fold is consistent: prove it in Lean, complete the assembly, fire the chain → the Ricci evolution equation. Done-report.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
