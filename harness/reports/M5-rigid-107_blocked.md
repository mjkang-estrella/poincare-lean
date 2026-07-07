# M5-rigid-107 blocked: radius tuple needs an unexported norm-system short-time bound

## Outcome

Added `Poincare/Global/RadiusTuple.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module does not restate the selector tuple as another assumption.  It
proves a necessary arithmetic condition for the bounded norm-system radius
tuple consumed by `TransverseExport`:

```lean
Poincare.RadiusTuple.norm_time_le_one_of_radius_tuple_bounds
Poincare.RadiusTuple.source_norm_time_le_one_of_selector_radius_tuple
Poincare.RadiusTuple.target_norm_time_le_one_of_selector_radius_tuple
```

These lemmas isolate the remaining selector-time obstruction.  From the
bounded-center side condition evaluated at `w = 0`, the tuple gives
`radius ≤ B`.  Combining that with

```lean
hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ)
hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)
```

forces the unexported condition

```lean
‖Aop‖ * T ≤ 1
```

for every positive `radius`.  To actually choose a positive radius from the
bounded-center constructor one needs the corresponding strict room, morally
`‖Aop‖ * T < 1`, because `B` itself must be at least `radius + qmax`.

## Remaining blocker

`TransverseExport.lean` now exposes the selector families, initial identities,
and continuations from bounded norm-system data.  `ScalarPin.lean` can build
the `hplNorm` package once the numeric tuple is supplied.  `UniformShrink.lean`
exports `T < εlin` for the linearized geodesic-flow PL package.

What is not exported is the analogous small-time bound for the scalar
norm-system coefficient operator at the selector time:

```lean
‖Aop‖ * T ≤ 1
```

or a strict version strong enough to select `radius`, `B`, and `LNorm` with

```lean
‖Aop‖ * B ≤ (LNorm : ℝ)
(LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)
∀ w ∈ closedBall (0 : E3) (R : ℝ),
  ‖(((0 : ℝ), (0 : ℝ), q w) : ℝ × ℝ × ℝ)‖ + (radius : ℝ) ≤ (B : ℝ)
```

where

```lean
q w =
  chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
    (T⁻¹ • w) (T⁻¹ • w)
```

and the target analogue.  Without this coefficient-time room, the radius tuple
is not constructible from the public selector data; feeding
`TransverseExport` into `BlockDiagonal` would require assuming exactly the
missing tuple again.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/RadiusTuple.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/RadiusTuple.lean`
  - Result: success.
- `lake build Poincare.Global.RadiusTuple`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3209/3209] Built Poincare.Global.RadiusTuple (2.5s)
Build completed successfully (3209 jobs).
```
