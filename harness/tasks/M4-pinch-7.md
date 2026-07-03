Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-7: the Bochner inequality layer + scalar-square evolution (roadmap steps 3b + 4 prep)

On main: the |Ric|² evolution decomposition (`hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt` + the reaction-substituted 3D form with pinned trace/motion terms), `laplacianAt`/`hessianAt` (symmetric, hypothesis-free), the trace-commute machinery.

Deliverables (each its own commit):
1. **∇Ric norm vocabulary**: `def covRicciNormSqAt g x : ℝ` — |∇Ric|² as the double-contracted square of the covariant Ricci derivative (the `covTensor2DerivAt (ricciVariationField g)` values contracted; nonneg lemma by sum-of-squares — the Gram/trace machinery).
2. **The Bochner identity/inequality for |Ric|²**: `laplacianAt (fun y => ricciNormSqAt y) x = 2·⟨rough-Laplacian-of-Ric, Ric⟩ + 2·covRicciNormSqAt`-shape (the second-order trace-commute applied to the Ric-squared trace — the discharged machinery's pattern one more time), hence the INEQUALITY `2·⟨ΔRic, Ric⟩ ≤ Δ|Ric|²` (from covRicciNormSqAt ≥ 0). This converts the |Ric|² evolution into the parabolic form `d/dt |Ric|² ≤ Δ|Ric|² + [reaction traces + motion terms]` — state that corollary.
3. **Scalar-square evolution** (step-4 prep): from the PROVEN scalar evolution, `d/dt R² = 2R·(ΔR + 2|Ric|²)` and its parabolic form `d/dt R² = ΔR² − 2|∇R|² + 4R|Ric|²` (the scalar Bochner — gradient vocabulary exists; the |∇R|² term via `g.gradient`); the quotient-rule assembly (step 4 proper) uses exactly these two parabolic forms.

Test-pattern pin the Bochner coefficients. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
