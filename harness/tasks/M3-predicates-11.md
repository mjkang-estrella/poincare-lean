Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-11: constant-vector section smoothness via tangentBundleCore.coordChange

Read `harness/reports/M3-predicates-10_blocked.md` — its exact failing goal is the differentiability of `fun b => (fderivWithin ℝ (extend-chart-x ∘ (extend-chart-b).symm) (range I) (chart b b)) p`, i.e. the tangent-coordinate change applied to a fixed vector. KEY IDENTIFICATION: this is `(tangentBundleCore I M).coordChange` (Mathlib, `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean`) — whose smoothness is a PROVEN field of the vector-bundle-core structure (`contMDiffOn_coordChange` / the core's `coordChange_smooth`-style field; read the actual file for exact names and the indexing convention).

Deliverables (each its own commit):

1. `mdifferentiableAt_const_tangent_field`: for p : E, the section `T% (fun y => (p : TM y))` is `MDifferentiableAt` at every x. Route: `mdifferentiableAt_section` reduces to the trivialization expression (the failing goal); identify that expression with `(tangentBundleCore I M).coordChange (achart E x') (achart E x) · p` (definitional or via the core's `coordChange` lemma equations); apply the core's smoothness field (restricted to the chart-source neighborhood; `ContMDiffOn` → `ContMDiffAt` → `MDifferentiableAt` at the base point, then `.clm_apply` with constant p if the smoothness is CLM-valued).
2. `mdifferentiableAt_metric_entry_raw`: `y ↦ g.inner y p q` MDifferentiableAt for FIXED p q : E — combine step 1's constant sections with `MDifferentiableAt.inner_bundle` (the same combination `metric_pairing_mdiffAt` uses for extend-sections).
3. **Unblock the scalar-entry route** (predicates-10's plan, now viable): metric CLM field via `mdifferentiableAt_clm_dual_of_apply` (on main) + step 2 → inverse differentiability (`ContinuousLinearMap.inverse` on units; ModelLaplacian `differentiableAt_inverse_raise` template) → `mdifferentiableAt_metricDualVectorAt` (fixed covector; use `metricDualVectorAt_eq_metricRaiseContinuousAt`). THE ATOM.
4. Cascade if budget: extDerivFun value identity, then hSummand/hFrame of the product-rule bridge.

Exact-goal-state rule on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
