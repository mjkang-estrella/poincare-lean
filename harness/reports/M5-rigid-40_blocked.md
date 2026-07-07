# M5-rigid-40 blocked: side-condition discharge verified, isometry action gap remains

## Status

Blocked for the full requested local-isometry instantiation.  I added the new
module `Poincare/Global/CartanIsometryClose.lean` with one isolated, verified
statement discharging the shifted Gronwall side conditions from the exported
uniform PL-flow package on a shrunk source ball.

I did not edit existing Lean files, including `Poincare.lean`.

## Verified payload

The new module exports exactly one theorem:

```lean
Poincare.GeodesicTransport.exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
```

It chooses a positive radius `ρ` and fixed positive time `T` with `T ≤ ε`,
shrinks the exponential partial-homeomorphism source ball so that
`‖T⁻¹ • v‖ < δ`, extracts the closed-ball/target PL-flow side hypotheses from
`expAt_uniform_pl_flow_eq_on_Icc`, and applies

```lean
expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
```

The resulting strict derivative is the linearized endpoint CLM:

```lean
HasStrictFDerivAt
  (expAtChartOpenPartialHomeomorph (g := g) x₀)
  (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v
```

This is metric-generic in dimension 3, so it applies to both the source metric
`g` and `roundSphereMetric3` when the corresponding linearized family data are
available.

## Remaining blocker

The full theorem requested in the task would have to instantiate

```lean
CartanScaleGeneric.cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings
```

without assuming the hosted differential-action equations or the source
endpoint metric blocks.  The current exported API still does not provide:

1. a theorem constructing the required linearized family `Ψ` uniformly with
   endpoint additivity/smul and identifying its CLM action on the hosted
   radial/transverse decomposition;
2. the `hDu`/`hDu'` equations for
   `CartanLocalIsometry.cartanChartDifferential L A B`;
3. the source radial-radial, radial-transverse, and transverse-transverse
   endpoint metric blocks in the hosted scale.

Calling the hosted-scale bridge while keeping those assumptions would be a
vacuous wrapper, so I stopped at the verified side-condition discharge.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CartanIsometryClose.lean
```

Actual result: no matches.

Declaration scan:

```bash
rg -n "^(theorem|def|axiom|abbrev|structure|class|instance)\s" \
  Poincare/Global/CartanIsometryClose.lean
```

Actual result:

```text
45:theorem exists_shrunk_expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_linearized_family
```

Whitespace check:

```bash
git diff --check -- Poincare/Global/CartanIsometryClose.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanIsometryClose
```

Actual result: succeeded, with pre-existing upstream warnings replayed.

Final build lines:

```text
✔ [3162/3162] Built Poincare.Global.CartanIsometryClose (2.5s)
Build completed successfully (3162 jobs).
```
