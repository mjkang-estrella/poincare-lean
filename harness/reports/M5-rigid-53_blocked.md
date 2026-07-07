# M5-rigid-53 blocked: haccCollapse is false as stated

## Status

Blocked for the requested unconditional `haccCollapse`.  I added the new module
`Poincare/Global/ChristoffelCollapse.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.ChristoffelCollapse.sphereChristoffel_refutes_haccCollapse_at_unit_transverse_state
```

It pins the proposed collapse against the explicit stereographic round-sphere
Christoffel field `sphereChristoffel`.  The theorem chooses

```text
z = e0
V = (5 / 4) • e1
J = e2
K = 0
speed = 2
```

in `EuclideanSpace ℝ (Fin 3)`.  For the conformal round-sphere chart metric,
the theorem verifies the state is unit and transverse:

```lean
conformalChartMetricForm stereoInvFunAuxConformalFactor z V V = 1
conformalChartMetricForm stereoInvFunAuxConformalFactor z J V = 0
```

but also verifies that the proposed `haccCollapse` expression is not equal to
`(speed * speed) • (-J)`.

Concretely, in the `J` coordinate the left-hand Christoffel correction
expression evaluates to `-(5 / 8)`, while the requested right-hand side with
`speed = 2` evaluates to `-4`.  Thus the collapse is not a definitional
unfolding or symmetric-Christoffel cancellation; it is false under the
unit/transverse round-sphere model data.

## Blocker

The M5-rigid-52 `haccCollapse` statement attempts to identify raw coordinate
Jacobi acceleration with a time-rescaled harmonic acceleration.  The existing
constant-curvature theorem gives the covariant oscillator
`coordinateCovariantJacobiSecond = -J`; expanding it necessarily leaves
Christoffel correction terms.  Those terms do not vanish in stereographic
round-sphere coordinates, and they do not reorganize into the arbitrary
`speed^2` factor.

The next viable bridge should either:

1. carry the covariant corrected state `D = K + Γ(V,J)` through the hosted
   harmonic comparison, or
2. add the missing reparameterized/geometric hypotheses that make the raw
   coordinate acceleration equation true.

Assuming the displayed `haccCollapse` would hide a real false identity.

## Verification

Forbidden-token scan:

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|lemma|def|abbrev|structure|class|instance)\s" \
  Poincare/Global/ChristoffelCollapse.lean
```

Actual result:

```text
19:theorem sphereChristoffel_refutes_haccCollapse_at_unit_transverse_state
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/ChristoffelCollapse.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.ChristoffelCollapse
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully with no local warnings.

Final build lines:

```text
✔ [2926/2926] Built Poincare.Global.ChristoffelCollapse (2.5s)
Build completed successfully (2926 jobs).
```
