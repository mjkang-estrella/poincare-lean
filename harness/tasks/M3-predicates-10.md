Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-10: raise-field differentiability via the SCALAR-ENTRY route (no mfderiv, no charts)

Read `harness/reports/M3-predicates-9_blocked.md` — the chart/`inTangentCoordinates` route hit a coordinate-representation mismatch. Do NOT use mfderiv of `extChartAt.symm`. Orchestrator route (scalar entries + dual basis; fully chart-free since every fiber TM y = E by rfl):

Target (same as before): `MDifferentiableAt I 𝓘(ℝ, E) (fun y => metricDualVectorAt g y φ) x` for fixed covector φ, plus the extDerivFun value = `spatialMetricDualVectorDerivAt` if reachable.

1. **Scalar entries are differentiable**: for FIXED p q : E, `y ↦ g.inner y p q` is MDifferentiableAt (from `ClosedSmoothRiemannianMetric.contMDiff_inner` / `MDifferentiableAt.inner_bundle` with constant sections — `metric_pairing_mdiffAt` in Global/LeviCivitaExistence.lean already does exactly this for extend-sections; constants are extend-sections of constants or easier).
2. **The metric CLM field is differentiable**: `y ↦ (metric-as-CLM at y) : M → (E →L[ℝ] (E →L[ℝ] ℝ))` via dual-basis reconstruction from finitely many scalar entries — the model file has the REUSABLE pattern `differentiableAt_clm_dual_of_apply` (ModelLaplacian, per frontier notes: a field into a CLM space is differentiable when each y ↦ f y w is, via f y = Σₖ (f y bₖ)•coord k). Port/adapt it to MDifferentiableAt over M (target is a fixed normed space, so MDifferentiable into E→L(E→Lℝ) reduces to the same dual-basis finite sum of scalar·constant).
3. **Inverse is differentiable**: `y ↦ (metric CLM y)⁻¹` — invertibility from nondegeneracy+finite-dim (`metric_nondegenerate`, the continuous raise `metricRaiseContinuousAt` IS this inverse — use `metricDualVectorAt_eq_metricRaiseContinuousAt`); differentiability via Mathlib's `ContinuousLinearMap.inverse` smoothness on units (`differentiableAt_inverse` — for maps INTO the unit group; compose with step 2 through `MDifferentiableAt` of a smooth-normed-space function: raising through 𝓘(ℝ, ·) targets is plain composition since the outer map is ContDiff on an open set — `ContDiff.comp_mdifferentiableAt`-style; ModelLaplacian's `hasFDerivAt_inverse_raise`/`differentiableAt_inverse_raise` chain is the template).
4. **Apply to φ**: `metricDualVectorAt g y φ = (inverse at y) φ` — `MDifferentiableAt.clm_apply` with the constant φ. DONE — the lemma.
5. **Value identity** (if budget): extDerivFun value = `spatialMetricDualVectorDerivAt` via `d(A⁻¹) = −A⁻¹(dA)A⁻¹` + the proven `spatialMetricDualVectorDerivAt_inner_apply` pairing + nondegeneracy.
6. **Cascade** (if budget): discharge hSummand/hFrame of `traceMetricVariationProductRuleAt_of_spatiallyDifferentiable`.

Exact-goal-state rule applies on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
