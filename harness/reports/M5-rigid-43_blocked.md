# M5-rigid-43 blocked: rescaled hosted linearized family

## Status

Strict partial landed.  I added the new module
`Poincare/Global/LinearizedRescale.lean` with one isolated theorem and did not
edit existing Lean modules, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.LinearizedRescale.exists_hosted_rescaled_linearized_solution_family
```

Given the hosted Picard-Lindelöf data from
`LinearizedFamilyExport.exists_hosted_linearized_solution_family_on_pl_closedBall`
and a positive PL input radius `(0 : ℝ) < r`, it chooses the concrete PL-ball
family, normalizes each endpoint direction `w` into that ball by the scale

```lean
max 1 ((2 * ‖T⁻¹ • w‖) / (r : ℝ))
```

and scales the resulting local linearized solution back.  The theorem proves
the all-direction family satisfies the exact initial data

```lean
Ψ w 0 = ((0 : E), T⁻¹ • w)
```

and solves the hosted linearized geodesic ODE on `Icc (-ε) ε` for every
`w : E`.

This is not a vacuous wrapper: the proof uses the exported PL fixed-point
family, verifies the normalized initial state is in the PL closed ball, and
uses `linearizedGeodesicFlowFieldAlong_smul` to prove the scaled curve solves
the same linearized ODE with scaled initial data.

## Remaining blocker

The full CLM hypothesis discharge is still blocked at endpoint linearity:

```lean
∀ w w', (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1
∀ c w,  (Ψ (c • w) T).1 = c • (Ψ w T).1
```

The current exported PL family gives all-direction solutions after rescaling,
but the endpoint additivity/smul proof still needs the common-scale uniqueness
argument that compares different rescalings and keeps the summed/scaled
candidate curves inside the same PL uniqueness ball.  The existing
`LinearizedCLM.lean` endpoint lemmas are centered at the scaled initial datum,
while this hosted export is zero-centered, so the next step should either add
zero-centered uniqueness endpoint lemmas or prove the common-scale comparison
directly from `IsPicardLindelof.eqOn_Icc_of_mem_closedBall`.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/LinearizedRescale.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/LinearizedRescale.lean
```

Actual result:

```text
37:theorem exists_hosted_rescaled_linearized_solution_family
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/LinearizedRescale.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.LinearizedRescale
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
Built Poincare.Global.LinearizedRescale (12s)
Build completed successfully (3164 jobs).
```
