# M5-glob-8 blocked report

## Delivered files

- `Poincare/Global/GeodesicPreservation.lean`
- `harness/reports/M5-glob-8_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`GeodesicPreservation.lean` imports `ExpNaturality` and adds one isolated theorem:

- `Poincare.GeodesicPreservation.cartanMap_target_chart_exp_naturality`

The theorem proves the strict-source target-chart identity for the anchor-based
Cartan partial homeomorphism:

```text
expChart_target (L (expChart_source.symm ((chartAt source_anchor) x)))
  = (chartAt target_anchor) (cartanMap source_anchor target_anchor L x)
```

This is the re-anchored Cartan map side of the charted exponential-naturality
identity.  The proof uses the strict source membership of
`CartanMap.openPartialHomeomorph` to extract the final target chart membership,
then applies the target chart right inverse.

## Blocking boundary

This does not yet prove the demanded `hnaturality` hypothesis consumed by
`ExpNaturality.lean`, because that hypothesis is about the old carried map
`s.map x`, not merely the newly re-anchored `CartanMap.cartanMap g x₁ (s.map x₁) L₁ x`.

The missing non-vacuous producer remains the classical geodesic-preservation
step: the old local isometry must transport source geodesics through `x₁` to
target geodesics through `s.map x₁`, or equivalently must provide the chart ODE
transport/Christoffel transformation law that identifies the old germ with the
re-anchored Cartan germ on the common strict source.  The current interfaces
still expose that as the unresolved chart-overlap acceleration/Christoffel
transport boundary.

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicPreservation
```

Actual final result:

```text
✔ [3231/3231] Built Poincare.Global.GeodesicPreservation (2.5s)
Build completed successfully (3231 jobs).
```

Additional contract checks:

```bash
rg -n "\\b(sorry|admit|axiom|native_decide)\\b" Poincare/Global/GeodesicPreservation.lean
git diff --check
```

Actual result: no matches from `rg`; `git diff --check` exited successfully.
