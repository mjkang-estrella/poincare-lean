# M5-rigid-87 done: enriched cascade exports the hosted base package

## Status

Added `Poincare/Global/EnrichedCascade.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves an enriched cascade export, not a vacuous wrapper.  It
replays the hosted PL-flow construction, shrinks the PL interval into the
cutoff-one locus, exports the half-time strict margin `T < ε`, and keeps the
same opaque hosted curve `α` attached to the linearized family.

## What landed

- `EnrichedCascade.BaseCurvePackage`
  records the base curve facts for
  `γ = α (extChartAt I x₀ x₀, T⁻¹ • v)`: initial value, full-interval
  `HasDerivWithinAt`, one-sided `HasDerivWithinAt`, upgraded
  `HasDerivAt` on `Icc 0 T`, target membership, cutoff-one germ membership,
  pointwise cutoff-one, constant chart-metric speed, and endpoint equality
  with `expAtChartOpenPartialHomeomorph`.
- `EnrichedCascade.LinearizedFamilyPackage`
  records the same-family linearized data: initial values, full and one-sided
  linearized ODE derivatives, upgraded `HasDerivAt` on `Icc 0 T`, the
  initial-velocity flow derivative, and the nearby-speed eventual equality
  used by one-sided payload consumers.
- `EnrichedCascade.exists_shrunk_cutoff_one_strictDeriv_package`
  constructs the one-sided enriched package for a single metric from the
  hosted PL flow and proves the strict derivative for the same `α`.
- `EnrichedCascade.exists_common_enriched_source_target_cascade`
  combines the source metric and the aligned round-sphere target over one
  small endpoint ball, exporting the enriched source and target packages plus
  strict margins on both sides.

## Scope note

I did not state a new curvature-only `cartanMap_isLocalIsometry` theorem in
this file.  The delivered module closes the rigid-86 base-curve identification
gap by exporting the `hγ`-shape derivative, cutoff/zone, and speed fields for
the same hosted datum used by the endpoint-linear family.

## Verification

- `lake build Poincare.Global.EnrichedCascade`
  - Result: success.
  - Final lines:

```text
✔ [3180/3180] Built Poincare.Global.EnrichedCascade (4.2s)
Build completed successfully (3180 jobs).
```

- Forbidden-token scan on `Poincare/Global/EnrichedCascade.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/EnrichedCascade.lean`
  - Result: success.
