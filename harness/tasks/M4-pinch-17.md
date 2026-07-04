Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-17: roadmap step 4 — the pinching-quotient evolution (quotient rule)

Both inputs are PROVEN on main: (a) `deriv_ricciNormSqAt_le_laplacianAt_add_reactionMotionTrace3` (the parabolic |Ric|² inequality) and (b) the scalar-square parabolic form `d/dt R² = ΔR² − 2|∇R|² + 4R|Ric|²` (pinch-8, ScalarEvolution.lean) — plus `pinchingQuotientAt` (= |Ric|²/R², pinch-1 in RicciNorm.lean), `laplacianAt_mul`/the product-rule layer, `scalarGradNormSqAt`, and the scalar positivity machinery (R > 0 domain lemmas, `hamilton_scalar_lower_bound` chain).

Deliverable (roadmap step 4): the evolution inequality for the pinching quotient at a point where `scalarAt x > 0`:
`d/dt (|Ric|²/R²) ≤ Δ(|Ric|²/R²) + [gradient drift term] + [reaction remainder]/R²`-shape — the target statement `SatisfiesHamiltonPinchingEvolutionInequality3At` is ALREADY FROZEN on main (pinch-1, with `pinchingQuotientGradientDrift3At` + `pinchingTracelessDampingAt` vocabulary): FIRST validate that frozen shape against the two proven parabolic forms via the quotient-rule algebra INFORMALLY (the standing lesson: coefficient-pin on the space form — where Ric = λg makes the quotient constant ⟹ all terms must cancel — AND a non-Einstein pattern; if the frozen drift/damping decomposition mismatches, refute exactly and stop for review).

Then prove, as separate commits:
1. The quotient calculus lemmas: `d/dt (u/v) `, `Δ(u/v) = Δu/v − uΔv/v² − 2⟨∇(u/v), ∇v⟩/v`-shape at v = R² > 0 (from `laplacianAt_mul` applied to (u/v)·v — the standard trick avoiding a division-Laplacian theory; gradient form via `gradientAt_mul`).
2. Substitute the two parabolic forms → the assembled inequality (the |∇Ric|²-vs-|∇R|² cross terms organize into the drift + a nonpositive completed-square remainder — Hamilton's classical computation; keep the remainder explicit if the sign step needs 3D input, deferring it to step 5).
3. Land `satisfiesHamiltonPinchingEvolutionInequality3At_of_ricciFlow` (or the honest partial with the remainder named). Report names.

BUILD NOTE: ScalarVariation.lean elaborates slowly (~10+ min single-module); prefer `lake env lean` for iteration and be patient with the final `lake build` — silence is normal, do not kill it early. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`.
