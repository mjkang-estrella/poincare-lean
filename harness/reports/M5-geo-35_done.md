# M5-geo-35: done

Task: reroute the anti-Lipschitz ball proof through Mathlib's Riemannian
lower-comparison topology lemma.

## Mathlib surface

Read `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`.

Public lemmas used:

```lean
eventually_enorm_mfderiv_extChartAt_lt
eventually_riemannianEDist_le_edist_extChartAt
eventually_riemannianEDist_lt
setOf_riemannianEDist_lt_subset_nhds
setOf_riemannianEDist_lt_subset_nhds'
```

`setOf_riemannianEDist_lt_subset_nhds` is the lower-comparison direction:
every neighborhood of `x` contains a small enough `riemannianEDist` ball.  Its
short-path/no-exit induction is inline in Mathlib, not exported as a pairwise
chart-ball lower-bound lemma.  The new file consumes the public neighborhood
inclusion as a positive exit cost and avoids reimplementing the previous
first-exit induction.

## Delivered

Added `Poincare/Global/AntilipschitzMathlib.lean` only.  Existing Lean source
files, including `Poincare.lean`, were not edited.

Public exports:

```lean
theorem exists_riemannianEDist_ball_subset_extChartAt_source_ball
theorem chart_source_ball_exit_pathELength_lower_bound_mathlib
theorem exists_chart_ball_pairwise_pathELength_lower_bound
```

These specialize Mathlib's lower-comparison lemma to chart source balls, turn it
into a path-length exit lower bound via `riemannianEDist_le_pathELength`, and
prove the requested geo-32 pairwise bound.

```lean
theorem exists_extChartAt_symm_antilipschitz_ball
theorem localChartAntilipschitzLowerBound_mathlib
theorem volumeMeasure_univ_ne_zero_mathlib
```

These provide the unconditional anti-Lipschitz chart ball and the
`NormalizedFlow.lean` consumer payoff.

```lean
theorem exists_expAt_dist_lower_bound_ball
```

This gives the requested local `dist x₀ (expAt g x₀ v) ≥ c * ‖v‖`-shaped
payoff, using the anti-Lipschitz chart ball and the already proven exponential
chart first-order estimate.

## Verification

Forbidden-token scan on the new file:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/AntilipschitzMathlib.lean
```

Result: no matches.

Requested build:

```text
lake build Poincare.Global.AntilipschitzMathlib
```

Result:

```text
✔ [3001/3001] Built Poincare.Global.AntilipschitzMathlib (4.0s)
Build completed successfully (3001 jobs).
```

The build emitted pre-existing dependency replay/linter warnings, but no errors.
