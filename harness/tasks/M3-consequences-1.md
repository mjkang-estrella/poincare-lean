Read harness/worker_contract.md first and obey it strictly.

# Task M3-consequences-1: clean Hamilton form + the scalar lower-bound/singularity chain

GOAL 3 opener. On main: `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` (the Hamilton theorem, contracted Bianchi discharged internally) and its `_hessian_variation` sibling; the two δΓ assembly predicates have PROVEN Hessian-trace discharge forms (`deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular`, the contraction-side canonical wrappers from predicates-23). Also on main: `Poincare/MaximumPrinciple.lean` — GENUINE scalar ODE machinery: `riccati_lower_bound`, `riccati_forces_finite_time`, `ode_comparison_*` (plain ℝ→ℝ analysis, immediately reusable).

Deliverables (each its own commit):
1. **Cleanest Hamilton form**: `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'` with hDiv/hCon replaced by their proven discharge forms (wire the Hessian-trace wrappers through; the result should need only: the flow near x, the regularity classes, and the scalar/Ricci differentiability data — all with witnesses). Verify the hypothesis list is minimal-honest; document each remaining hypothesis with its witness in a comment block.
2. **Pointwise Riccati step**: from `SatisfiesHamiltonScalarEvolutionAt` + the pinching `scalarAt_sq_le_nat_mul_ricciNormSqAt` (RicciNorm.lean, on main): `d/dt R ≥ ΔR + (2/n)·R²` — at a SPATIAL MINIMUM of R (where ΔR ≥ 0 — state the minimum hypothesis honestly; the model's `hamilton_scalar_lower_bound` shows the shape), `d/dt R_min ≥ (2/n)·R_min²`.
3. **Finite-time singularity**: chain with `riccati_forces_finite_time` (MaximumPrinciple.lean): a closed Ricci-flow solution with R(x₀,t₀) > 0 at a spatial minimum cannot extend smoothly past T = n/(2·R_min) — the closed-manifold `hamilton_finite_time_singularity` analogue (model template of the same name). State honestly with the time-domain hypotheses the ODE lemma needs.
4. Done-report with the theorem names.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution`, report names.
