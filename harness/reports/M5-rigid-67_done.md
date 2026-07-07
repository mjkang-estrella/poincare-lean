# M5-rigid-67 done: speed-generic package layer

## Status

Done. Added `Poincare/Global/SpeedGeneric.lean` with additive speed-`s`
variants only; no existing Lean files were edited.

## Exact unit-speed consumer

The hard unit-speed demand is in
`Poincare/Global/CartanIsometryTheorem.lean`:

- `CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`

It reaches the `hunit` requirement through
`JacobiNormClose.chart_linearized_state_feeds_norm_system_at`, whose oscillator
input is
`coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`.
That theorem proves the frequency-1 Jacobi equation `J'' = -J`.

## What changed

`Poincare.Global.SpeedGeneric` proves the corresponding speed-`s` layer:

- curvature contraction with speed:
  `R(v, J)v = -(speed^2) • J` under orthogonality and
  `cG p v v = speed^2`;
- speed norm system:
  `A' = 2B`, `B' = C - speed^2 * A`, `C' = -2 * speed^2 * B`;
- pinned solution with
  `speedPinnedScale speed T = sin (speed*T)^2 / speed^2`;
- source and target endpoint package variants using the speed pinned solution;
- bridge lemmas from `SpeedPackage.lean` speed values to the needed
  `cG p v v = speed^2` hypotheses;
- a feed/local-isometry consumer theorem for the common-speed hosted package.

The resulting endpoint scale is the expected
`sin(speed*T)^2 / speed^2`; for inverse-time input vectors this gives the
hosted transverse scale `sin(speed*T)^2 / (speed*T)^2`, matching the existing
`CartanScaleGeneric` feed shape.

## Verification

Forbidden-token scan on `Poincare/Global/SpeedGeneric.lean`: no matches for
`sorry`, `admit`, `axiom`, or `native_decide`.

Whitespace check:

```text
git diff --check -- Poincare/Global/SpeedGeneric.lean
```

passed with no output.

Required build:

```text
lake build Poincare.Global.SpeedGeneric Poincare.Global.SourcePackage Poincare.Global.TargetPackage
```

completed successfully:

```text
Build completed successfully (3179 jobs).
```
