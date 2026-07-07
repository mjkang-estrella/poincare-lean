# M5-rigid-78 blocked report

## Status

Added `Poincare/Global/HostedPayload.lean` as the requested new module and did
not edit existing Lean files, including `Poincare.lean`.

I did not state a hosted-package theorem or a `cartanMap_isLocalIsometry`
wrapper.  The current exports do not co-discharge the payload interval fields
needed by the transverse orthogonality theorem; assuming that field in the new
module would be a vacuous restatement of the missing package.

## First unfed field

The first field that cannot be supplied from the current exports is the
variation-flow payload required by
`OrthogonalityFeed.source_transverse_horth_on_Icc_of_payload`:

```lean
(hflow : ∀ τ ∈ Ioo a b,
  HasDerivAt
    (fun s : ℝ => α (extChartAt I3 x₀ x₀, v + s • w) τ) (Ψ τ) 0)
```

The target-side theorem has the analogous field:

```lean
(hflow : ∀ τ ∈ Ioo a b,
  HasDerivAt
    (fun s : ℝ => α (extChartAt I3 p₀ p₀, v + s • w) τ) (Ψ τ) 0)
```

## Why this blocks the common-time package

`OrthogonalityFeed.source_transverse_horth_on_Icc_of_payload` also requires

```lean
(h0 : (0 : ℝ) ∈ Ioo a b)
```

and the speed-generic transverse endpoint package requires a closed interval
with

```lean
(hzero : (0 : ℝ) ∈ Icc tmin tmax)
(hT : T ∈ Icc tmin tmax)
```

For the hosted positive time `T`, feeding the existing orthogonality theorem
therefore needs an open interval with left endpoint strictly below `0`, hence
the displayed `hflow` must be available for negative times as well as for the
path from `0` to `T`.

The only exported initial-velocity flow derivative I found is
`GeodesicTransport.chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`,
whose time hypothesis is one-sided:

```lean
(ht : t ∈ Icc (0 : ℝ) ε) :
  HasDerivAt
    (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
    (Ψ t) 0
```

`SmoothDependenceDischarge.chart_initialVelocity_fixedTime_payload_of_uniform_geodesicFlow`
preserves the same `t ∈ Icc 0 ε` restriction.  Thus the existing payload
exports do not feed the open-interval `hflow` required by `OrthogonalityFeed`.

Closing this boundary needs either:

- a negative-time/symmetric version of the initial-velocity derivative export,
  or
- a new one-sided integrated transverse Gauss payload compatible with the
  speed-generic `Icc 0 T` interval.

After that, the remaining scalar interval/norm package fields would still need
to be checked against the same common hosted datum.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/HostedPayload.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/HostedPayload.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.HostedPayload
```

Actual result: succeeded, with pre-existing imported-module warnings.  Final
build lines:

```text
✔ [3189/3189] Built Poincare.Global.HostedPayload (12s)
Build completed successfully (3189 jobs).
```
