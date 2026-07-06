# M5-geo-7 blocked report

## New module

File: `Poincare/Global/ExponentialMapDef.lean`

No existing Lean source file or root import was edited.  In particular,
`Poincare.lean` was not changed.

## Verified strict-partial progress

### 1. Target-shrunk endpoint-controlled flow

The new theorem

```lean
theorem Poincare.GeodesicTransport.exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target
```

refines the M5-geo-6 endpoint-controlled PL flow.  It reruns the
Picard-Lindelöf construction, shrinks the PL radius against a closed ball
contained in `(extChartAt I x₀).target`, and returns common `δ`, `ε`, a
closed-ball radius, and a flow `α` such that for every `‖v₀‖ < δ`:

- `α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀)`;
- `α` solves the chart geodesic system on the whole `Icc (-ε) ε` as a
  `HasDerivWithinAt` solution;
- the first-order state remains in the common PL closed ball;
- the position component remains in `(extChartAt I x₀).target` on the whole
  `Icc (-ε) ε`.

The target membership comes from the product closed-ball control and the
sup-product metric: membership in the first-order closed ball implies the
position coordinate lies in the shrunk chart-target ball.

### 2. Germ identification near zero

The new theorem

```lean
theorem Poincare.GeodesicTransport.exists_uniform_local_geodesic_chart_flow_with_mem_target_eventuallyEq_germ
```

extends the target-shrunk flow package with

```lean
α (extChartAt I x₀ x₀, v₀) =ᶠ[𝓝 (0 : ℝ)]
  geodesicGermChartSolution g x₀ v₀
```

for every `‖v₀‖ < δ`.

This proves the requested local neighborhood identification in germ form.  The
proof converts the flow's `Icc` derivative control to `HasDerivAt` on a small
`Ioo` around `0` and applies the existing same-anchor chart-ODE uniqueness
theorem against the chosen `geodesicGermChartSolution`.

## Remaining blocker for `expAt`

The fixed-time exponential map was not introduced in this strict partial.
The remaining nontrivial gap is the endpoint ray law, not target membership or
germ identification.

To define `expAt` by a fixed positive time flow endpoint with rescaled
velocity and prove

```lean
expAt g x₀ (t • v) = geodesicGermAt g x₀ v t
```

on an honest interval, the new file still needs a flow-level homogeneity
theorem on a closed interval:

```lean
σ ↦ ((α (z₀, v) (s * σ)).1, s • (α (z₀, v) (s * σ)).2)
```

must be shown to solve the same chart geodesic ODE with initial velocity
`s • v`, stay in the common PL ball on the relevant `Icc`, and then be
identified with `α (z₀, s • v)` by `IsPicardLindelof.eqOn_Icc_of_mem_closedBall`.
That proof also needs the endpoint parameters arranged so `s * σ` remains in
the source interval and the scaled velocity component remains inside the same
closed ball.  This is the flow-level upgrade of the existing
`geodesicGermAt_smul_eventually` pattern.

Once this homogeneity lemma is available, the fixed-time `expAt` definition
can use the target-shrunk endpoint flow, and the chart-source membership of
`expAt g x₀ v` for small `v` follows directly from the target membership
proved here via `(extChartAt I x₀).map_target`.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ExponentialMapDef.lean
```

Actual result: no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/ExponentialMapDef.lean
```

Actual result: no output.

Required build command:

```text
lake build Poincare.Global.ExponentialMapDef
```

Actual result:

```text
Build completed successfully (2829 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialMapDef.lean`.
