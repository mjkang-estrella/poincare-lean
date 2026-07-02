Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-14: ONE displayed identity — the inverse-Gram cancellation

SCOPE: exactly the identity displayed in `harness/reports/M3-predicates-13_blocked.md` (read it first — the Lean goal is pasted there verbatim), then the ≤3-step chain that closes `TraceMetricVariationDerivAt` with it.

The identity, at the base point x (where `gramFrame x x i = bᵢ` and `gramMatrix g x x` = the metric matrix):
`Σᵢⱼ ∂_w[(gramMatrix g x ·)⁻¹ᵢⱼ] · h(bᵢ, bⱼ-frame) = −Σᵢ h(Γ_w(ext bᵢ), ♯bⁱ) − Σᵢ h(bᵢ, Γ_w(ext ♯bⁱ))`

Proof skeleton (finite-dim matrix algebra + already-proven pieces):
1. `∂(M⁻¹) = −M⁻¹(∂M)M⁻¹` entrywise for the Gram matrix (differentiable entries + eventual invertibility are on main: `gramMatrix_inv_entry_mdiffAt` machinery; if the derivative-of-inverse ENTRY identity isn't yet a lemma, prove it from `Matrix.inv_mul_cancel`-differentiation or Mathlib's `Matrix` calculus / `Ring.inverse` derivative — finite matrices over ℝ, standard).
2. `∂(Gram)ᵢⱼ = ∂_w[g(ext bᵢ, ext bⱼ)] = g(Γ_w(ext bᵢ), bⱼ) + g(bᵢ, Γ_w(ext bⱼ))` at x — this is `spatialMetricDerivAt_eq_leviCivita`/the Gram entry derivative identities from predicates-13 (on main — check exact names in the file around `gram_rhs_extDerivFun_eq_sum_product`).
3. Contract: Σᵢⱼ [−G⁻¹(∂G)G⁻¹]ᵢⱼ h(bᵢ, frameⱼ) — expand G⁻¹ against the h-slots via the raised-dual expansion (`metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv` on main; at x the raised duals are ♯bⁱ); each ∂G term from step 2 lands on one slot, producing exactly the two Γ sums with a minus sign. Pure `Finset.sum` reindexing + bilinearity — the swap machinery (`sum_metricDualVectorAt_contraction_swap`) handles the slot order.
4. Chain: plug into `gram_rhs_extDerivFun_eq_sum_product` + `extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections` (on main) → the Γ-corrections cancel → **`TraceMetricVariationDerivAt` discharged**. Wire the consumer (`traceMetricVariationDerivAt_of_productRule_raiseCancellation` or restate directly), update notes.

Exact-goal-state rule on failure — but this identity is self-contained linear algebra; expect it to close. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
