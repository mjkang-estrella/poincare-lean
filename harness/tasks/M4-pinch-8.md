Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-8: the closed Laplacian product-rule layer → the two parabolic forms

Read `harness/reports/M4-pinch-7_blocked.md` — its "Next proof unit" is this task's plan (each item its own commit):

1. `gradientAt_mul`: `g.gradientAt (f₁·f₂) = f₁·grad f₂ + f₂·grad f₁` — from the extDerivFun product rule (Mathlib `extDerivFun_mul` or derive from `fderiv` product rule through the chart representative; the gradient is the raise of the differential — linear, so the product rule lifts directly).
2. The scalar-times-vector-field covariant derivative rule (`g.leviCivita (f·X) = df⊗X + f·∇X`-shape on the needed slots — the connection's Leibniz law, likely already a `CovariantDerivative` structure field or one rearrangement away).
3. `hessianAt_mul` and `laplacianAt_mul`: `Δ(f₁f₂) = f₁Δf₂ + f₂Δf₁ + 2⟨grad f₁, grad f₂⟩` — assemble from 1+2 (model template: `RicciFlow.modelLaplacian_mul`).
4. **The payoffs**: (a) scalar-square parabolic form: `d/dt R² = ΔR² − 2|∇R|² + 4R|Ric|²` (laplacianAt_mul at f₁=f₂=scalarAt + the proven scalar evolution; define `scalarGradNormSqAt` honestly); (b) the Ricci-norm Bochner expansion: `Δ|Ric|² = 2⟨rough-Lap Ric, Ric⟩ + 2·covRicciNormSqAt` (the second-order product rule on the Ric-squared trace via the same layer + the trace-commute machinery) — hence the parabolic inequality `d/dt |Ric|² ≤ Δ|Ric|² + [reaction+motion traces]` (covRicciNormSqAt ≥ 0, on main).

Test-pattern pin the Bochner coefficients. Standing protocols. No sorry/axiom. `lake build Poincare.Global.Laplacian Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
