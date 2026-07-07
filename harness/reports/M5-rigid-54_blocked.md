# M5-rigid-54 blocked: radial sphere pin still refutes raw collapse

## Status

Blocked for the requested ray-restricted `haccCollapse`.  I added the new
module `Poincare/Global/CollapseOnRay.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.CollapseOnRay.sphereChristoffel_refutes_haccCollapse_at_unit_radial_harmonic_state
```

This is the requested sphere pin, specialized to a radial stereographic state:

```text
z = e0
V = (5 / 4) • e0
J = (4 / 5) • e1
K = (3 / 5) • e1
speed = 1
```

The theorem verifies that `V = (5 / 4) • z`, the state is unit and transverse
for the stereographic round-sphere conformal chart metric, and the proposed
raw Christoffel-correction collapse is not equal to the harmonic acceleration
`(speed * speed) • (-J)`.

Concretely, in the `e1` coordinate the raw collapse expression evaluates to
`1 / 10`, while the harmonic acceleration evaluates to `-4 / 5`.

## Blocker

The cutoff-one zone facts prove the covariant oscillator and the corrected norm
system.  They do not make the raw chart-coordinate acceleration harmonic, even
on the radial sphere ray with harmonic sine/cosine transverse values.  The
remaining Cartan composition therefore cannot be advanced by restating
`haccCollapse` as a cutoff-one/ray-only fact without adding a stronger,
nonexistent coordinate-normalization theorem.

## Verification

Direct Lean check:

```bash
lake env lean Poincare/Global/CollapseOnRay.lean
```

Actual result: succeeded with no output.

Required build:

```bash
lake build Poincare.Global.CollapseOnRay
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [2926/2926] Built Poincare.Global.CollapseOnRay (2.7s)
Build completed successfully (2926 jobs).
```
