# M5-rigid-39 done: shifted Gronwall strict derivative

## Status

Done.  Added `Poincare/Global/ExponentialStrictClose.lean` only; no existing
Lean module or `Poincare.lean` was edited.

## Verified payload

The new module exports one isolated theorem:

```lean
Poincare.GeodesicTransport.expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
```

It proves the shifted endpoint two-variable Gronwall propagation and concludes

```lean
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := g) x₀)
  (linearizedEndpointCLM (Ψ := Ψ) τ hadd hsmul) v
```

for a shrunk-ball velocity `v` with `‖τ⁻¹ • v‖ < δ`, using the shifted
closed-ball Taylor estimate from `ExponentialStrictAtV`, the common PL flow
data, and a linearized endpoint family with initial data
`Ψ w 0 = (0, τ⁻¹ • w)`.

The statement is metric-generic for any `ClosedSmoothRiemannianMetric n M`, so
it specializes to both the general closed smooth metric and
`roundSphereMetric3` without adding a second wrapper theorem.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ExponentialStrictClose.lean
```

Actual result: no matches.

Exported declaration scan:

```bash
rg -n "^(theorem|def|axiom|abbrev|structure|class|instance)\b" Poincare/Global/ExponentialStrictClose.lean
```

Actual result:

```text
43:theorem expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
```

Required build:

```bash
lake build Poincare.Global.ExponentialStrictClose
```

Actual result: succeeded.

Final build lines:

```text
✔ [2984/2984] Built Poincare.Global.ExponentialStrictClose (7.8s)
Build completed successfully (2984 jobs).
```
