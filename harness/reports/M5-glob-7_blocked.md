# M5-glob-7 blocked report

## Delivered files

- `Poincare/Global/ExpNaturality.lean`
- `harness/reports/M5-glob-7_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`ExpNaturality.lean` imports `InducedAlignment` and adds one isolated theorem:

- `Poincare.ExpNaturality.rigidStepCompatibleWith_of_target_chart_exp_naturality`

The theorem proves the strict-partial assembly step:

```lean
InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁
```

from the normal-coordinate form of exponential naturality on the strict common
source of the old and re-anchored Cartan germs.  The consumed identity is the
charted version of

```text
Φ ∘ exp_{x₁} = exp_{Φ x₁} ∘ dΦ_{x₁}
```

namely that, for points in the common source, the target exponential chart at
`s.map x₁` applied to the explicitly supplied alignment `L₁` agrees with the
new target chart coordinate of the old value `s.map x`.  A separate chart-source
hypothesis records that those old target values stay in the `s.map x₁` chart.
The proof uses both hypotheses to apply the target chart inverse and then
unfolds the re-anchored Cartan map definition.

## Blocking boundary

The classical identity itself is still not available from the current
interfaces.  The repository already has same-anchor geodesic uniqueness in
`GeodesicGerm/GeodesicChart`, and `GeodesicReanchor.lean` exposes the right
consumer once a transported shifted state is known to solve the new anchor's
chart geodesic ODE.  However the required theorem that a local isometry sends
source geodesics to target geodesics still needs the Christoffel/acceleration
transformation law for the charted local isometry.

Concretely, the remaining non-vacuous input is a theorem producing the
`hnaturality` hypothesis consumed by `ExpNaturality.lean`, using either:

1. chart Christoffel transport plus geodesic uniqueness, or
2. a variational energy/length preservation argument plus uniqueness.

Without that theorem, the full old-germ-versus-reanchored-germ `EqOn` cannot be
proved from the metric pullback identity alone.

## Verification

Command run:

```bash
lake build Poincare.Global.ExpNaturality
```

Actual result:

```text
✔ [3230/3230] Built Poincare.Global.ExpNaturality (10s)
Build completed successfully (3230 jobs).
```

Additional contract checks:

```bash
rg -n "\\b(sorry|admit|axiom|native_decide)\\b" Poincare/Global/ExpNaturality.lean
git diff --check
```

Actual result: no matches from `rg`; `git diff --check` exited successfully.
