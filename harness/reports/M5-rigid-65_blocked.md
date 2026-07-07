# M5-rigid-65 blocked: hosted speed-value package added, unit-speed package still missing

## Status

Added `Poincare/Global/SpeedPackage.lean` and did not edit existing Lean
modules, including `SourcePackage.lean` and `TargetPackage.lean`.

The new module proves a non-vacuous speed package for the actual hosted base
curves.  The main exported facts are:

```lean
Poincare.SpeedPackage.sourceAnchorChartMetric_self_nonneg
Poincare.SpeedPackage.targetAnchorChartMetric_self_nonneg
Poincare.SpeedPackage.hostedSourceSpeed_sq
Poincare.SpeedPackage.hostedTargetSpeed_sq
Poincare.SpeedPackage.hostedTargetSpeed_sq_eq_hostedSourceSpeed_sq
Poincare.SpeedPackage.chartMetric_speed_eq_anchor_on_shrunk_Icc
Poincare.SpeedPackage.target_chartMetric_speed_eq_anchor_on_shrunk_Icc
Poincare.SpeedPackage.hosted_source_curve_speedValue_eq_anchor_on_shrunk_Icc
Poincare.SpeedPackage.hosted_target_curve_speedValue_eq_anchor_on_shrunk_Icc
Poincare.SpeedPackage.hosted_aligned_target_curve_speedValue_eq_source_anchor_on_shrunk_Icc
```

For source hosted data, the package proves the actual statement

```lean
CovariantDerivative.chartMetric g.inner x₀
    (α (extChartAt I x₀ x₀, T⁻¹ • v) t).1
    (α (extChartAt I x₀ x₀, T⁻¹ • v) t).2
    (α (extChartAt I x₀ x₀, T⁻¹ • v) t).2 =
  CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v)
```

on every closed interval strictly inside the exported PL interval, assuming the
existing PL geodesic-flow derivative and cutoff-one hypotheses.  The aligned
target version proves the corresponding round-sphere hosted speed value and
rewrites it through `TangentAlignment.map_app` to the source anchor metric.

## Remaining blocker

This discharges the available speed-value package, not the old unit-speed
field.  The existing endpoint package consumers still require the exact
frequency-one hypothesis:

```lean
(hunit : ∀ s ∈ Icc tmin tmax,
  CovariantDerivative.chartMetric g.inner x₀
    (γ s).1 (γ s).2 (γ s).2 = 1)
```

Applying that field to the actual hosted source curve
`αs (extChartAt I x₀ x₀, Ts⁻¹ • v)` would require

```lean
CartanMap.sourceAnchorChartMetric g x₀ (Ts⁻¹ • v) (Ts⁻¹ • v) = 1
```

which is not exported and is false for general hosted endpoint `v`.  The same
issue holds on the target side with `Tt⁻¹ • align v`.

The next non-vacuous route is therefore additive general-speed Jacobi pinning:
replace the frequency-one oscillator layer by a speed-squared system
`D²J = -speedSq • J`, yielding the scalar factor
`sin (speed * T)^2 / (speed * T)^2` after the existing inverse-time initial
data is unscaled.  That route needs new lower-level variants below the
`SourcePackage`/`TargetPackage` boundary; changing only the final package
wrappers would leave the same oscillator proof obligation.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/SpeedPackage.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/SpeedPackage.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.SpeedPackage
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module emitted no local errors.

Final build lines:

```text
✔ [3159/3159] Built Poincare.Global.SpeedPackage (12s)
Build completed successfully (3159 jobs).
```
