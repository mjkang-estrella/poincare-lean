# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/augmented-system-regularity`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartAugmentedSystemRegularity.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/augmented-system-regularity_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never change the retained time `C.T` or the retained state ball).

# Task: full-time C¹ dependence of the augmented flow, hence C² of the patch endpoint map on the full ball

Read first: `harness/reports/patch-second-variation_blocked.md` (sections "One exact resisting statement" and
"Why step 1 still resists": the flow theorems return a possibly shorter time; the fix is continuation over the
full retained interval), then `Poincare/Global/FixedChartPatchSecondVariation.lean`
(`operatorAugmentedField`, `operatorAugmentedField_contDiff_one`, `chart_operatorAugmentedField_contDiff_two`,
`operatorAugmentedFlow_hasDerivWithinAt`, `patch_flow_hasFDerivAt_of_fundamentalSolution`,
`exists_patch_flow_contDiffOn_two_short_time`, `AugmentedSystemRegularity`, `target_of_augmentedSystemRegularity`),
`Poincare/Global/FixedChartUniformJacobiComparison.lean` (`exists_fundamentalSolution_on_Icc`: linear ODEs with
bounded continuous coefficients on ANY closed interval by finitely many Picard steps; `exists_patch_fundamentalSolution`:
the full-interval fundamental solution Φ of the base flow with joint continuity;
`flow_hasFDerivAt_of_fundamentalSolution`), and `Poincare/Global/GeodesicFlowJointDerivative.lean`
(`initialState_residual_isLittleO`, `flow_hasFDerivAt_initialState`, `continuousOn_fundamentalSolution`,
`exists_fundamentalSolution_lipschitzOn_initialState`: these are stated for a general C¹/C² field on a normed
space `X` with a compact trajectory tube — instantiate them with `X := (E × E) × ((E × E) →L[ℝ] (E × E))`).

Target (frozen): for every `{x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U)`,

```lean
theorem augmentedSystemRegularity (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    FixedChartPatchSecondVariation.AugmentedSystemRegularity C
```

with the definition used verbatim, and its consequence (via `target_of_augmentedSystemRegularity`)

```lean
theorem patch_endpoint_contDiffOn_two (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    ContDiffOn ℝ 2 (fun q => C.α q C.T) (ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
```

Route (commit each): (1) take Φ from `exists_patch_fundamentalSolution` (full interval, all initial states in the
ball) so the augmented flow `q ↦ (C.α q t, Φ q t)` exists on `Icc (-C.T) C.T` and satisfies the augmented ODE
(`operatorAugmentedFlow_hasDerivWithinAt`); (2) its trajectory tube over the closed ball-times-interval is
bounded (joint continuity of α and Φ on compact sets), so the augmented linearized coefficient
`t ↦ fderiv (operatorAugmentedField) (augmented state)` is bounded and continuous; build the augmented
fundamental solution on the FULL interval with `exists_fundamentalSolution_on_Icc`; (3) identify it with the
initial-state derivative of the augmented flow on the full interval with the general full-interval Grönwall
identification (`initialState_residual_isLittleO` / `flow_hasFDerivAt_initialState` on `X`, exactly as
`patch_flow_hasFDerivAt_of_fundamentalSolution` did for the base flow); (4) joint continuity of the augmented
fundamental solution in the initial state (`continuousOn_fundamentalSolution` on `X`) gives `ContDiffOn ℝ 1`
of the augmented endpoint on the full ball; assemble `augmentedSystemRegularity` and
`patch_endpoint_contDiffOn_two`. Do not shrink the time or the ball. If step (3) resists for the augmented
system, deliver the earlier steps and the exact resisting `def` with `target_of_<resisting>`.
