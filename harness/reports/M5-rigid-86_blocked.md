# M5-rigid-86 blocked: common hosted datum still not exported

## Status

Added `Poincare/Global/IsometryAssembly.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

I did not state a curvature-only `cartanMap_isLocalIsometry` theorem.  The
`hplLinear` mismatch from rigid-84 is fixed by `SolutionsFeed`, but the public
exports still do not provide one common hosted package tying the endpoint-linear
`Psi` families from `CartanCascade` to the base-flow, cutoff, speed, and norm
fields consumed by `SolutionsFeed` and then `BundleDischarge`.

## First unfed field

After substituting `SolutionsFeed.source_transverseTransverse_of_solutions_feed`
for the old bounded feed, the first source-side field I cannot feed for the
same hosted curve used by the cascade solution family is:

```lean
(hγ : ∀ s ∈ Icc tmin tmax,
  HasDerivAt γ
    (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
```

For the cascade source curve

```lean
γ = αs (extChartAt I x₀ x₀, Ts⁻¹ • v)
```

`CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`
exports the endpoint-linear `Ψ` family and the strict derivative conditional,
but not this base-flow `HasDerivAt` field for `αs`.  It also does not export
the same curve's target-membership, cutoff-one, speed, or norm-membership
fields required later by `SolutionsFeed`.

The closest derivative adapter is
`IsometryInstantiate.hasDerivAt_on_Icc_of_hasDerivWithinAt_on_larger_Icc`, but
using it at the cascade endpoint would require a strict interior margin such as
`Ts < εs`.  The cascade theorem exports only:

```lean
Ts ≤ εs
```

and does not export the base `HasDerivWithinAt` hypothesis for `αs` either.
The cutoff-one speed/ray packages expose base-flow data for their own hosted
flow package, but the current public API does not identify that package with
the opaque cascade `αs`/`αt` used for endpoint linearity and strict
derivatives.

## Verification

- `lake build Poincare.Global.IsometryAssembly`
  - Result: success.
  - Final lines:

```text
✔ [3196/3196] Built Poincare.Global.IsometryAssembly (1.6s)
Build completed successfully (3196 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/IsometryAssembly.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/IsometryAssembly.lean`
  - Result: success.
