# M5-glob-24 blocked report

## Status

Blocked on the fully non-hypothetical `RigidStepCompatibleWith` requested by
the task, with verified strict-partial progress in the required new Lean file:

- `Poincare/Global/TwoBridges.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.TwoBridges
  .rigidStepCompatibleWith_of_common_source_target_ray_and_chart_sources
```

It proves the chart-to-manifold bridge needed by
`RaysToBall.rigidStepCompatibleWith_of_common_source_expAt_ray_cover`:

```lean
expAt g x1
  ((expAtChartOpenPartialHomeomorph (g := g) x1).symm ((chartAt E x1) x)) = x
```

from the existing chart-coordinate identity in `RayCoverInputs.lean`, provided
the corresponding `expAt` endpoint lies in the `x1` chart source.  It then fires
the `RaysToBall` assembler and proves:

```lean
InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x1 L1
```

under the remaining pointwise target-ray identity and target chart-source
membership hypotheses.

## Blocking boundary

The current repository still does not export the two facts needed to make the
theorem non-hypothetical on the strict common source:

1. endpoint chart-source membership for the inverse `x1` exponential coordinate
   (the existing `expAt_mem_source_of_norm_lt` is only a small-norm theorem, and
   the `expAtChartOpenPartialHomeomorph` source is not exported as lying inside
   that small ball);
2. the old carried map target-ray identity

```lean
s.map x =
  expAt roundSphereMetric3 (s.map x1)
    (L1 ((expAtChartOpenPartialHomeomorph (g := g) x1).symm
      ((chartAt E x1) x)))
```

from the induced differential/re-anchored velocity construction.  `InducedAlignment`
constructs a metric-preserving alignment, and `ChainRuleInput` supplies the
one-dimensional re-anchor law, but there is still no exported consumer proving
that the old carried Cartan map sends every strict common-source `x1` normal ray
to the corresponding target normal ray.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/TwoBridges.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/TwoBridges.lean
git diff --check -- Poincare/Global/TwoBridges.lean
lake build Poincare.Global.TwoBridges
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
37:theorem rigidStepCompatibleWith_of_common_source_target_ray_and_chart_sources

git diff --check -- Poincare/Global/TwoBridges.lean
exit status 0

lake build Poincare.Global.TwoBridges
✔ [3246/3246] Built Poincare.Global.TwoBridges (12s)
Build completed successfully (3246 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
