# M5-geo-12 blocked report

## New module

File: `Poincare/Global/ExponentialRayLaw.lean`

No existing Lean source file or root import was edited.  In particular,
`Poincare.lean` was not changed.

## Verified progress

The new module imports `Poincare.Global.ExponentialFixedTime` and proves two
downstream consequences of the currently exported fixed-time package.

### 1. Right-neighborhood ray law

```lean
theorem Poincare.GeodesicTransport.expAt_eventually_eq_geodesicGermAt_nhdsGE
```

This converts the existing
`𝓝[Set.Icc 0 τ] 0` eventual ray law into a genuine right-neighborhood
statement at `0`, using `Icc_mem_nhdsGE hτ`.

### 2. Right-derivative corollary

```lean
theorem Poincare.GeodesicTransport.expAt_chart_hasDerivWithinAt_of_norm_lt
```

Statement proved:

```lean
∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ),
  ∀ v : E, ‖v‖ < δ →
    HasDerivWithinAt
      (fun t : ℝ => extChartAt I x₀ (expAt g x₀ (t • v)))
      v (Set.Ici (0 : ℝ)) (0 : ℝ)
```

The proof uses the right-neighborhood ray law and
`geodesicGermAt_chart_hasDerivAt`.

## Remaining blocker

The requested full closed-interval identification and ray law were not proved:

```lean
expAt g x₀ (t • v) = geodesicGermAt g x₀ v t
```

for all `t ∈ Set.Icc 0 τ'` and uniformly small `‖v‖`.

The blocker is an export boundary in the existing API.  `expAt` is defined as a
`Classical.choose` from `exists_expAt_fixed_time_package`, and the exported
spec for that package contains only:

- `expAt_zero`,
- the eventual ray law at `0`,
- small endpoint chart-source membership.

The concrete endpoint map, PL flow, and the target-shrunk PL uniqueness witness
used inside the proof of `exists_expAt_fixed_time_package` are not available to
a downstream file.  Since this task forbids editing existing files, the new
module cannot strengthen the selected `expAt` witness to a full-interval law.

There is also no exported uniform lower bound for
`geodesicGermRadius g x₀ v` for all small `‖v‖`, nor exported closed-ball
membership of the chosen `geodesicGermChartSolution` on a common interval.
Those are exactly the facts needed to apply
`IsPicardLindelof.eqOn_Icc_of_mem_closedBall` on the intersection of the PL
interval and the germ interval.

## Needed next step

Strengthen an existing package theorem, likely in
`Poincare/Global/ExponentialFixedTime.lean` or an upstream construction, so
that the chosen `expAt` witness exports either:

1. the full-interval ray law directly, or
2. a reusable PL-flow/germ `EqOn` theorem on a uniform closed interval, with
   the common closed-ball membership needed by
   `IsPicardLindelof.eqOn_Icc_of_mem_closedBall`.

Smoothness of `expAt` in `v` is still a separate issue: the current local API
uses existence and interval uniqueness, but does not expose smooth dependence
of the ODE solution on initial data.  That likely needs a parametric ODE
smooth-flow theorem or a local wrapper exporting the same information.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ExponentialRayLaw.lean
```

Actual result: no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/ExponentialRayLaw.lean harness/reports/M5-geo-12_blocked.md
```

Actual result: no output.

Required build command:

```text
lake build Poincare.Global.ExponentialRayLaw
```

Actual result:

```text
Build completed successfully (2831 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialRayLaw.lean`.
