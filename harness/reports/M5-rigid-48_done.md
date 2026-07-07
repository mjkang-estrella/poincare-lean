# M5-rigid-48 done: hosted endpoint equality by uniqueness

## Status

Added the new module `Poincare/Global/CartanEndpointUnique.lean`.
No existing Lean modules were edited, including `Poincare.lean`.

## Verified payload

The module exports exactly one theorem:

```lean
Poincare.CartanEndpointUnique.hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc
```

It proves the requested endpoint shape:

```lean
(Ψ w T).1 = (Φ w (speed * T)).1
```

from `linearODE_solution_uniqueOn_Icc`.  The theorem compares `Ψ w` with the
hosted time-rescaled harmonic state

```lean
fun t => ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2)
```

under explicit non-vacuous hypotheses that both solve the same hosted
linearized chart-geodesic ODE, stay in the same Picard-Lindelöf closed ball,
and have matching hosted initial data.  The initial-data match uses
`speed ≠ 0` and `T ≠ 0` to identify
`speed • ((speed * T)⁻¹ • w)` with `T⁻¹ • w`.

## Remaining instantiation boundary

This file deliberately contains only the endpoint-uniqueness statement.  To
feed the theorem into the full rigid-47 composition, the caller still has to
provide the geometric bridge hypotheses exported in this theorem's interface:
the time-rescaled harmonic state must be shown to solve the same hosted
`linearizedGeodesicFlowOperator` equation and remain in the corresponding PL
ball.  Those are the nontrivial oscillator-to-hosted-linearized ODE conversion
facts alluded to in the task.

## Verification

Forbidden-token and declaration scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b|^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanEndpointUnique.lean
```

Actual result:

```text
38:theorem hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanEndpointUnique.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanEndpointUnique
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3161/3161] Built Poincare.Global.CartanEndpointUnique (2.6s)
Build completed successfully (3161 jobs).
```
