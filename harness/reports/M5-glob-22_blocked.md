# M5-glob-22 blocked report

## Status

Blocked on deriving the full requested `RigidStepCompatibleWith` solely from
the current `NaturalityCascade` ray reanchoring and exponential partial
homeomorphism interfaces.

Verified strict-partial payload added in the required new file:

- `Poincare/Global/RaysToBall.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.RaysToBall
  .rigidStepCompatibleWith_of_common_source_expAt_ray_cover
```

It proves the actual pointwise assembly step:

1. for each point in the strict common source, the inverse `x1` normal
   coordinate really exponentiates back to that point;
2. the corresponding target ray endpoint is the old Cartan value at that
   point;
3. the target endpoint is readable by the target chart.

From those three ray-cover facts, the theorem proves:

```lean
InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x1 L1
```

This is the requested common-source `EqOn` shape, but still as a strict partial:
the ray-cover facts are explicit hypotheses rather than consequences of the
existing interfaces.

## Blocking boundary

The remaining missing bridge is the non-hypothetical upgrade from the current
available data to the three pointwise ray-cover inputs:

```lean
∀ x ∈ s.germ.source ∩
    (InducedAlignment.CompatibleStep.nextWithAlignment s x1 L1).germ.source,
  expAt g x1
      ((expAtChartOpenPartialHomeomorph (g := g) x1).symm
        ((chartAt E x1) x)) = x
```

and the matching target ray identity:

```lean
s.map x =
  expAt roundSphereMetric3 (s.map x1)
    (L1 ((expAtChartOpenPartialHomeomorph (g := g) x1).symm
      ((chartAt E x1) x)))
```

together with the target chart source membership for that endpoint.

The current local-homeomorphism source membership exposes enough data to write
the inverse coordinate, but the repo does not yet provide a theorem converting
membership in the composed Cartan common source into the source endpoint
identity above.  The current `NaturalityCascade` theorem is still an
eventual-germ statement along a supplied source/target ray, and no available
consumer identifies its reanchored target velocity with the explicitly supplied
`L1` action on the inverse `x1` normal coordinate for every common-source
point.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/RaysToBall.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/RaysToBall.lean
git diff --check -- Poincare/Global/RaysToBall.lean
lake build Poincare.Global.RaysToBall
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
41:theorem rigidStepCompatibleWith_of_common_source_expAt_ray_cover

git diff --check -- Poincare/Global/RaysToBall.lean
exit status 0

lake build Poincare.Global.RaysToBall
✔ [3243/3243] Built Poincare.Global.RaysToBall (2.1s)
Build completed successfully (3243 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
