# M5-glob-48 blocked: no pinned Mathlib smooth-dependence flow theorem

## Mathlib mining outcome

The pinned Mathlib checkout does not expose a ready-made `ContDiff` smooth
dependence theorem for Picard-Lindelöf/Grönwall ODE flows in initial
conditions.

Searched locations:

- `.lake/packages/mathlib/Mathlib/Analysis/ODE/`
- `.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean`
- broader `.lake/packages/mathlib/Mathlib` grep for flow/ODE/solution
  `ContDiff`, differentiability, smooth dependence, and variation terms

Relevant names found:

- `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
- `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`
- `ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt`
- `ContDiffAt.exists_eventually_eq_hasDerivAt`
- `Flow` in `Mathlib/Dynamics/Flow.lean`, which is a topological monoid-action
  API, not an ODE smooth-dependence API

Names/patterns searched but not found as usable smooth-dependence exports:

- `contDiff.*flow`, `flow.*contDiff`
- `ContDiff.*ODE`
- `smooth.*dependence`
- `IsPicardLindelof.contDiff`
- `ContDiffOn.*solution`
- `solution.*ContDiff`
- `fderiv.*flow`, `flow.*fderiv`

The only initial-data dependence export in the ODE file is Lipschitz/continuous
dependence, not `ContDiffAt`/`ContDiffOn` of the flow in initial conditions.

## Consumer check

`FTransitionDone` still needs a genuine derivative of the canonical endpoint
field, supplied downstream through `ContDiffAt ℝ 2 F`.  `ExpChartC2` derives
that `C2` input from:

```lean
ContDiffAt ℝ 1 sourceD v
ContDiffAt ℝ 1 targetD (L v)
```

So the symmetry-only fallback does not bypass the current consumer as written:
the field-C1 demand remains.

## Fallback started

I started the third-variation fallback in the required new file:

- `Poincare/Global/FlowSmoothness.lean`

The new isolated theorem is:

```lean
theorem Poincare.GeodesicTransport
  .exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
```

It proves the next regularity layer for the augmented geodesic/first-variation
field:

```lean
ContDiff ℝ 2
  (augmentedGeodesicFlowField (chartChristoffelField g x₀))
```

and packages the resulting compact-tube Lipschitz bound on every closed ball.
This is the concrete starter needed for a third-variation replay, beyond the
existing `AugmentedC1` `C1` export.

No existing Lean files were edited, including `Poincare.lean`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/FlowSmoothness.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/FlowSmoothness.lean
git diff --check -- Poincare/Global/FlowSmoothness.lean
lake build Poincare.Global.FlowSmoothness
```

Actual result:

```text
forbidden-token scan: no matches
top-level declaration scan:
43:theorem exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall

git diff --check -- Poincare/Global/FlowSmoothness.lean
exit status 0

lake build Poincare.Global.FlowSmoothness
✔ [2835/2835] Built Poincare.Global.FlowSmoothness (14s)
Build completed successfully (2835 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully and introduced no reported warning.
