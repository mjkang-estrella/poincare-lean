# M5-rigid-51 done: covariant oscillator unpacked to coordinate acceleration

## Status

Done for the strict-partial acceleration identity.  I added the new module
`Poincare/Global/AccelerationIdentity.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.AccelerationIdentity.coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state
```

It applies the pointwise cutoff-one/unit/transverse covariant oscillator

```lean
coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
```

and then expands `coordinateCovariantJacobiSecond` to solve for the raw
coordinate acceleration.  The resulting identity keeps the honest Christoffel
correction terms, including the state bridge term
`K + Γ(z)(V,J)`.

This is the requested isolated coordinate unpacking; it does not assume or
erase the correction terms.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/AccelerationIdentity.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/AccelerationIdentity.lean
```

Actual result:

```text
37:theorem coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state
```

Direct Lean check:

```bash
lake env lean Poincare/Global/AccelerationIdentity.lean
```

Actual result: succeeded with no output.

Whitespace check:

```bash
git diff --check -- Poincare/Global/AccelerationIdentity.lean harness/reports/M5-rigid-51_done.md
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.AccelerationIdentity
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3135/3135] Built Poincare.Global.AccelerationIdentity (2.9s)
Build completed successfully (3135 jobs).
```
