Read harness/worker_contract.md first and obey it strictly.

# Task M5-sphere-3: the locally-constant glue lemma → THE UNCONDITIONAL CONSTANT-CURVATURE THEOREM

Read `harness/reports/M5-sphere-2_blocked.md` — ONE lemma remains, with its recipe and ingredients named:

1. **`isLocallyConstant_of_extDerivFun_eq_zero`**: `(∀ x, MDifferentiableAt I 𝓘(ℝ) f x) → (∀ x w, extDerivFun f x w = 0) → IsLocallyConstant f`. Proof: through the chart — `extDerivFun_apply_chart`/`extDerivFun_apply_fixed_chart` (on main) identify extDerivFun with the chart representative's fderiv; on each chart ball the representative has fderiv ≡ 0 ⟹ locally constant (Mathlib: `isLocallyConstant_of_fderiv_eq_zero` or the convex-domain constancy lemma applied on the chart's preconnected target ball — mind that chart images may need shrinking to balls); glue chart-locally ⟹ `IsLocallyConstant f`.
2. **Global constancy**: + `PreconnectedSpace`/connectedness (ClosedSmoothRiemannianMetric's manifolds are connected in the Statement-layer context — check what's available; take `[ConnectedSpace M]` as a hypothesis if not bundled) via `IsLocallyConstant.apply_eq_of_preconnectedSpace` → `scalarAt_constant_of_extDerivFun_eq_zero_connected`.
3. **THE COMPOSITION**: `tracelessRicciNormSqAt ≡ 0 → HasConstantSectionalCurvature3 g (R₀/6)` — chain the merged pieces (Einstein criterion → Schur step → constancy → the conditional space-form bridge, all on main). This is goal-7 item-3 COMPLETE.
4. Done-report + the items-4/5 outlook (the `PositiveConstantCurvatureSpaceForm3` interface + the conditional sphere theorem, per the frontier survey).

Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
