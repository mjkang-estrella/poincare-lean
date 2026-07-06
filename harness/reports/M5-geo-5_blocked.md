# M5-geo-5 blocked report

## New module

File: `Poincare/Global/ExponentialDomain.lean`

No existing Lean file or root import was edited.  In particular,
`Poincare.lean` was not changed.

## Verified progress

Namespace: `Poincare.GeodesicTransport`

```lean
theorem exists_uniform_local_geodesic_chart_solution
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∃ γ : ℝ → E × E,
        γ 0 = (extChartAt I x₀ x₀, v₀) ∧
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt γ
            (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t
```

This proves the uniform local existence part from the pinned quantitative
Picard-Lindelöf API.  The proof centers the closed-ball PL theorem at
`(extChartAt I x₀ x₀, 0)` and uses `dist_prod_same_left` to include every
small velocity initial state `(extChartAt I x₀ x₀, v₀)` in that same initial
closed ball.

## Blocker

The fixed-time exponential map on a velocity ball was not defined, because the
available exported statements are not enough to prove the required non-vacuous
endpoint laws.

The missing boundary is not uniform existence itself; Mathlib has that.  The
gap is endpoint control for the common PL flow:

1. `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
   returns common `δ, ε` and solutions for every initial point in the closed
   ball, but it does not expose that the chosen solution remains in the larger
   PL closed ball on the full closed interval.
2. The internal `ODE.FunSpace.compProj_mem_closedBall` lemma has exactly this
   kind of path-bound information, but the exported existence theorem drops it.
3. `geodesicGermAt_smul_eventually` is only a germ-at-`0` homogeneity theorem.
   It cannot by itself justify evaluating a reparametrized solution at a fixed
   positive common time `ε`.

An honest `expAt` should be built from a common PL flow, e.g. by evaluating the
solution with initial velocity `ε⁻¹ • v` at time `ε`.  To prove
`expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` and chart-source membership,
the next lemma should expose both:

```lean
-- schematic target
theorem IsPicardLindelof.exists_flow_with_mem_closedBall :
  ∃ α : E → ℝ → E,
    ∀ x ∈ closedBall x₀ r,
      α x t₀ = x ∧
      (∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      (∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a)

theorem IsPicardLindelof.interval_unique_of_mem_closedBall :
  -- uniqueness among curves staying in the PL ball, or equivalently a
  -- fixed-point characterization strong enough to compare reparametrized
  -- geodesic chart solutions on the whole interval
  α =ᶠ[𝓝ˢ (Icc tmin tmax)] β
```

## Next decomposition

1. Export a strengthened PL flow theorem from `IsPicardLindelof` that returns
   closed-ball membership of trajectories on `Icc`, reusing
   `ODE.FunSpace.compProj_mem_closedBall`.
2. Prove interval uniqueness for two solutions staying inside the PL ball on
   the common interval, or expose a fixed-point uniqueness theorem usable for
   reparametrized geodesic chart solutions.
3. Define `expAt g x₀ v` on `‖v‖ < δ'` as the common-flow endpoint for
   initial velocity `ε⁻¹ • v`, with documented junk value outside the ball.
4. Prove `expAt g x₀ 0 = x₀`, ray compatibility with `geodesicGermAt` via
   interval homogeneity, and chart-source membership using the closed-ball
   trajectory bound chosen inside `(extChartAt I x₀).target`.
5. Then handle continuity/smoothness of `expAt` in `v`.  In the pinned Mathlib
   tree I found `exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`,
   i.e. continuous dependence on initial conditions, but no ODE smooth
   dependence-on-initial-conditions API under `Mathlib/Analysis/ODE` or
   `Mathlib/Geometry/Manifold/IntegralCurve`.
6. Later decomposition: derivative of `expAt` at `0`, Gauss lemma, and
   injectivity radius on compact manifolds.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|axiom|native_decide)\b" Poincare/Global/ExponentialDomain.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.ExponentialDomain
```

Actual result:

```text
Build completed successfully (2827 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialDomain.lean`.
