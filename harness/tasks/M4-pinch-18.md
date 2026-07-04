Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-18: SANCTIONED correction — the honest quotient evolution (equality with explicit remainder)

Read `harness/reports/M4-pinch-17_blocked.md`. ORCHESTRATOR RULING: the frozen `SatisfiesHamiltonPinchingEvolutionInequality3At` damping decomposition is corrected (stated, never proven; its −(2/R)|Ric°|² pointwise damping is refuted by the (1,1,2) check). The correct classical structure (Hamilton 1982, §Lemma on |Ric|²/R²) separates GRADIENT damping from REACTION sign:

`∂ₜQ ≤ ΔQ + (2/R)⟨∇R, ∇Q⟩ − (2/R⁴)|R·∇Ric − ∇R⊗Ric|² + (2/R⁴)·P_reaction`, Q = |Ric|²/R², where `P_reaction = ½·R·[N-reaction/motion trace] − N·[R-reaction]/... ` — the EXACT algebraic combination the two proven parabolic forms supply (the worker's own (1,1,2) computation: quotient reaction = N_react/R² − 2N·R_react/R³; on (1,1,2) = −1/4 ✓, on space forms = 0 ✓). The SIGN of P_reaction under 3D + Ric ≥ 0 is roadmap STEP 5 — do NOT bundle it here.

Deliverables (each its own commit):
1. **Correct the target**: deprecate-with-comment the old predicate; state `SatisfiesPinchingQuotientEvolutionAt` as the EQUALITY/inequality with the explicit named remainder `pinchingReactionRemainderAt` (:= the exact reaction combination above, defined from the pinned vocabulary) and the gradient-square damping term named `pinchingGradientDampingAt` (define honestly; nonneg lemma by sum-of-squares). PIN the corrected shape on space form AND (1,1,2) AND one more diagonal pattern (e.g. (1,2,3)) in the report BEFORE proving.
2. **Quotient calculus lemmas**: d/dt and Δ of u/v at v = R² > 0 via the (u/v)·v product-rule trick (`laplacianAt_mul`, `gradientAt_mul` on main).
3. **The assembled theorem**: substitute the two proven parabolic forms → `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` (at points with scalarAt > 0, honest regularity classes). The gradient cross-terms must organize into the completed square − verify that algebra on the diagonal patterns first; if the completed-square shape itself mismatches, refute exactly and stop.
4. Done-report + step-5 outlook (the 3D reaction-sign lemma under Ric ≥ 0).

BUILD NOTE: ScalarVariation.lean elaborates ~10+ min/check; use `lake env lean` for iteration, be patient with the final build. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
