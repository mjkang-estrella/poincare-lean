# M5-rigid-83 done: bounded PL package plus homogeneous extension

## Status

Added `Poincare/Global/BoundedPackage.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The module records the bounded resolution of the `UniformPL` obstruction:

- `Poincare.BoundedPackage.hosted_hplNorm_on_closedBall_of_center_norm_bound`
  instantiates the uniform linear PL lemma at the hosted quadratic center over
  a closed ball of endpoint directions, using an explicit finite center bound.
- `Poincare.BoundedPackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall`
  and the target analogue prove the transverse-transverse formulas from a
  ball-restricted norm-system PL package.  The PL package is used only at
  `w`, `w'`, and `w + w'`.
- `Poincare.BoundedPackage.source_transverseTransverse_extend_from_closedBall`
  and the target analogue extend those ball-restricted pairing formulas to
  all transverse directions using endpoint homogeneity and bilinearity.

Consumer check: `BundleDischarge` and `CorrectedRadial` consume the
transverse-transverse pairing formulas, not the norm-system PL package itself.
`PLNormFeed` is the old unrestricted-package bridge; the new module bypasses
that unrestricted `∀ w` requirement by producing the bounded formulas and the
homogeneous all-`w` formulas directly.

## Verification

- `lake env lean Poincare/Global/BoundedPackage.lean`
  - Result: success.
- Forbidden-token grep on `Poincare/Global/BoundedPackage.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/BoundedPackage.lean`
  - Result: success.
- `lake build Poincare.Global.BoundedPackage`
  - Result: success.
  - Final lines:

```text
✔ [3192/3192] Built Poincare.Global.BoundedPackage (5.5s)
Build completed successfully (3192 jobs).
```
