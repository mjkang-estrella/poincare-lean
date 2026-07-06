# M5-geo-13 blocked report

## Files changed

- `Poincare/Global/ExponentialFixedTime.lean`
- `Poincare/Global/ExponentialRayLawFull.lean`
- `harness/reports/M5-geo-13_blocked.md`

No other existing Lean source file was edited.  In particular, `Poincare.lean`
was not changed.

## Verified progress

### 1. Stronger chosen `expAt` package

`Poincare/Global/ExponentialFixedTime.lean` now adds a non-breaking fourth
conjunct to `exists_expAt_fixed_time_package`.  The `expAt` definition's type
is unchanged, and the existing exported names still compile:

- `expAt_zero`
- `expAt_eventually_eq_geodesicGermAt`
- `expAt_mem_source_of_norm_lt`

The new exported theorem is:

```lean
theorem Poincare.GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc
```

It exposes the uniform PL-flow witness used by the selected `expAt`, including:

- the common closed interval `Set.Icc (-epsilon) epsilon`,
- the common closed-ball control,
- chart-target membership,
- the PL homogeneity law,
- and the closed-interval endpoint law

```lean
expAt g x0 (t • v) =
  (extChartAt I x0).symm (alpha (extChartAt I x0 x0, v) t).1
```

for all `t in Set.Icc 0 tau` and `‖v‖ < delta`.

### 2. New boundary module

`Poincare/Global/ExponentialRayLawFull.lean` was added and builds.  It records:

```lean
theorem Poincare.GeodesicTransport.expAt_closed_interval_eq_uniform_pl_flow
```

as the closed-interval PL-flow ray law for `expAt`, and:

```lean
theorem Poincare.GeodesicTransport.expAt_eq_geodesicGermAt_on_Icc_of_pl_flow_position_eq_germ
```

which proves that the requested full `geodesicGermAt` ray law follows
formally once the PL-flow position component is identified with the chosen
`geodesicGermChartSolution` on the same closed interval.

## Remaining blocker

The unconditional requested theorem

```lean
expAt g x0 (t • v) = geodesicGermAt g x0 v t
```

for all `t in Set.Icc 0 tau` and uniformly small `‖v‖` is still not proved.

The remaining missing fact is not the fixed-time endpoint packaging anymore:
that now exports a full closed-interval PL-flow law for the selected `expAt`.
The missing fact is an interval identification between this exported uniform
PL flow and the independently chosen `geodesicGermChartSolution`.

The available germ API still gives only:

- derivative of `geodesicGermChartSolution g x0 v` on its own chosen
  `Ioo (-geodesicGermRadius g x0 v) (geodesicGermRadius g x0 v)`,
- positivity of each per-velocity chosen radius,
- eventual target/source facts near `0`.

It does not export a uniform lower bound for `geodesicGermRadius g x0 v` for
all small `v`, nor closed-ball membership for the chosen germ on the fixed
PL interval.  The available interval uniqueness theorem
`IsPicardLindelof.eqOn_Icc_of_mem_closedBall` requires both curves to stay in
the same PL closed ball, so the new PL-side closed-ball control is not enough
by itself.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/ExponentialFixedTime.lean \
  Poincare/Global/ExponentialRayLawFull.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.ExponentialFixedTime \
  Poincare.Global.ExponentialRayLaw \
  Poincare.Global.ExponentialRayLawFull
```

Actual result:

```text
Build completed successfully (2832 jobs).
```

The build emitted pre-existing linter warnings from imported modules.
