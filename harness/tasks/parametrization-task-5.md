# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/parametrization-task-5`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/parametrization-task-5_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/chain-parametrization-inventory.md` (the whole plan; your task is one of its
"First five bounded tasks" and is reproduced below verbatim), then the cited definitions. Tasks 1-4 have landed
on `main`: `CartanSuppliedSourceMap.lean`, `CartanSuppliedSourceGermTransfer.lean`, `FixedChartEndpointSlices.lean`,
`FixedChartUniformSourceNormal.lean` (namespace `Poincare.FixedChartUniformSourceNormal`: `Patch`, `exists_patch`,
`Patch.normal`, `Patch.rawLocalFamily`, anchor laws, `isOpen_normal_sourceLocus`, `continuousOn_normal_eval`);
import and use them.

# Task parametrization-task-5

### 5. `Poincare/Global/FixedChartUniformPreferredGermAgreement.lean`

Use the patch from task 4 with fixed position neighborhood inside the fixed chart's cutoff-one zone. For each **fixed** `x ∈ patch.anchors`, define

```lean
Jx := GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)
```

Target `normalized_endpoint_eventuallyEq_expAt`:

```lean
(fun v : E => (extChartAt I x₀).symm
  (FixedChartUniformNormalRadius.expChart patch.α patch.T
    (extChartAt I x₀ x) (patch.T⁻¹ • v)))
  =ᶠ[𝓝 (0 : E)]
(fun v : E => GeodesicTransport.expAt g x (Jx v))
```

Target `normal_eventuallyEq_generic_in_anchor_frame`:

```lean
(fun z : M => Jx (patch.normal x z))
  =ᶠ[𝓝 x]
(fun z : M => (CartanSourceExponential.genericFamily g).normal x z)
```

Prove invertibility of `Jx` on this fixed-chart overlap as part of the theorem, so the inverse comparison really applies. The target quantifier order is `∀x∈anchors, EventuallyEq ...`; it does **not** ask for one legacy comparison radius uniform over `x`. Use interval ODE uniqueness on a common cutoff-one neighborhood, geodesic chart-transition naturality, and the inverse laws. Gate: compile and probe these two comparison theorems plus the named frame-invertibility lemma. Evidence: `exists_normalizedSelectorTime_velocity_eventuallyEq_chart_expAt`, `fixedToAnchorVelocity` in [CartanSourceExponentialLocalFamilyTransitionAgreement.lean](../../Poincare/Global/CartanSourceExponentialLocalFamilyTransitionAgreement.lean), and `GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc`. The central-anchor comparison already checked in the repository is the starting argument, not the completed moving-anchor proof. Stop with the exact chart-transformed ODE equality or uniqueness type if it resists; do not assume the old joint `TransitionAgreementPackage`.

For **each** of the five files, acceptance additionally requires `rg -n '\b(sorry|admit|axiom)\b|native_decide' <new-file>` to have no matches, `git diff --check`, the task-specific `#check` scratch probes, and the worker module-wide axiom gate with only the project's permitted axiom footprint. No simultaneous full builds. The orchestrator records these targets with the shared instance binders before dispatch and independently reruns the gate. The list is an ordered implementation plan, not five already elaborated new theorem statements.

The exact next action is to freeze and dispatch task 1 against the recorded base, then use its checked kernel when freezing task 2. The eventual successor/data and joint-radius tasks remain explicit work after these foundations.

