Read harness/worker_contract.md first and obey it strictly.

# Task M3-consequences-2: the spatial-minimum witness — the first GLOBAL argument

On main: `hamilton_finite_time_singularity` takes the spatial-minimum Laplacian witness (`0 ≤ ΔR` at the tracked point) as a hypothesis. This task discharges it — the program's first genuinely GLOBAL (compactness-using) argument:

1. **Minimum attainment**: on a closed (compact) M, the continuous function `y ↦ g.scalarAt y` attains a global minimum (Mathlib: `IsCompact.exists_isMinOn`/`exists_forall_le` on `CompactSpace` + continuity of scalarAt from its ContMDiffAt-2 smoothness — the canonical instances give this). State `exists_scalarAt_isMinOn`.
2. **Laplacian sign at a minimum**: at an interior minimum (every point is interior — no boundary), `0 ≤ laplacianAt f x`. Route: `laplacianAt = Σ hessianAt(bᵢ, ♯bⁱ)` (on main) and the Hessian at a local min is positive-semidefinite. The MODEL has this: `hessian_nonneg_of_isLocalMin` (MaximumPrinciple.lean:397, for E → ℝ with ContDiff 2 — flat!). Closed route: at a local min of f on M, the chart representative has a local min at the chart point; its flat Hessian is PSD (the model lemma); identify the closed hessianAt with the chart-flat Hessian + first-order corrections that VANISH at a critical point (df = 0 at the min kills the Christoffel corrections — the standard fact; the `extDerivFun_extDerivFun_extend_eq_hessianAt_add` identity on main exposes exactly the correction shape). Prove `laplacianAt_nonneg_of_isLocalMin` — honest hypotheses (f ContMDiffAt 2 etc.).
3. **Corollary**: `hamilton_finite_time_singularity'` with the witness replaced by "x₀ is a global minimum of scalarAt at time t₀" (+ positivity R(x₀,t₀) > 0), via 1+2. And the packaged closed-manifold statement: a closed Ricci-flow solution with R_min(t₀) > 0 has T < n/(2·R_min).
4. Done-report.

This is the first task whose content is impossible in the single-chart model (needs CompactSpace). Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution`, report names.
