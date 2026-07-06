# M5-geo-6 blocked report

## New module

File: `Poincare/Global/ExponentialMap.lean`

No existing Lean source file or root import was edited.  In particular,
`Poincare.lean` was not changed.

## Verified strict-partial progress

### 1. PL flow with endpoint control

The new theorem

```lean
theorem IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
```

rebuilds Mathlib's Picard-Lindelöf fixed points through public
`ODE.FunSpace` internals and returns a common local flow `α` such that, for
every initial point in the PL initial closed ball:

- `α x t₀ = x`;
- `HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t` for every
  `t ∈ Icc tmin tmax`;
- `α x t ∈ closedBall x₀ a` for every `t ∈ Icc tmin tmax`.

The closed-ball invariant is exactly the information supplied by
`ODE.FunSpace.compProj_mem_closedBall`.

The geodesic specialization

```lean
theorem Poincare.GeodesicTransport.exists_uniform_local_geodesic_chart_flow_with_mem_closedBall
```

applies this to the autonomous geodesic flow field centered at
`(extChartAt I x₀ x₀, 0)`.  It returns common `δ`, `ε`, a PL ball radius, and
a flow for all chart velocities with `‖v₀‖ < δ`, with derivative and ball
control on `Icc (-ε) ε`.

### 2. Interval uniqueness

The new theorem

```lean
theorem IsPicardLindelof.eqOn_Icc_of_mem_closedBall
```

specializes Mathlib's Grönwall uniqueness theorem to a PL closed ball.  It
proves equality on the whole `Icc tmin tmax` for two `HasDerivWithinAt`
solutions with the same value at `t₀`, provided both curves stay in
`closedBall x₀ a` on the interval.

The proof splits at the possibly non-endpoint initial time `t₀` and applies
`ODE_solution_unique_of_mem_Icc_left` and
`ODE_solution_unique_of_mem_Icc_right`, converting `Icc` derivatives to the
needed one-sided derivatives using `Icc_mem_nhdsLE_of_mem` and
`Icc_mem_nhdsGE_of_mem`.

## Remaining blocker for `expAt`

The fixed-time exponential map was not defined in this strict-partial.  The
new uniqueness theorem is strong enough to compare interval solutions, but the
existing chosen germ API does not yet provide the hypotheses needed for that
comparison at a fixed endpoint:

1. `geodesicGermChartSolution g x₀ v` only exposes `HasDerivAt` on its own
   open interval `Ioo (-geodesicGermRadius ...) (geodesicGermRadius ...)`;
   it does not expose membership in the new common PL closed ball on a closed
   interval such as `Icc 0 t`.
2. `geodesicGermAt_smul_eventually` is still only an eventual equality near
   `0`.  It does not identify the existing chosen germ with the new PL flow at
   the fixed time `ε`.
3. A PL-defined endpoint map could be introduced in the new file, but proving
   the requested ray law against the existing `geodesicGermAt` requires an
   additional bridge theorem: the existing chosen germ solution, or a
   reparametrization of it, must be shown to stay in the same PL ball on the
   relevant closed interval so that `IsPicardLindelof.eqOn_Icc_of_mem_closedBall`
   applies.
4. Chart-source membership for the endpoint also needs a target-contained PL
   ball or an equivalent shrink of the PL radius into
   `(extChartAt I x₀).target`; the current geodesic specialization records the
   common PL product ball but does not yet shrink it against the chart target.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|axiom|native_decide)\b" Poincare/Global/ExponentialMap.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.ExponentialMap
```

Actual result:

```text
Build completed successfully (2828 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialMap.lean`.
