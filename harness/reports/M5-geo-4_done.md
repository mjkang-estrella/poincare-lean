# M5-geo-4 done report

## New module

File: `Poincare/Global/ExponentialGerm.lean`

No existing Lean file or root import was edited.  In particular,
`Poincare.lean` was not changed.

This module deliberately packages only the germ-level exponential ray.  It does
not define a global `exp : TM x -> M`; global domain control is future work.

## Final signatures

Namespace: `Poincare.GeodesicTransport`

```lean
theorem geodesicGermAt_zero_velocity_eventually_const
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∀ᶠ t in 𝓝 (0 : ℝ), geodesicGermAt g x₀ (0 : E) t = x₀

theorem geodesicGermAt_smul_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ (s • v₀) t =
        geodesicGermAt g x₀ v₀ (s * t)

def expRayAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → M

@[simp]
theorem expRayAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    expRayAt g x₀ v₀ 0 = x₀

theorem expRayAt_smul_eventually
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      expRayAt g x₀ (s • v₀) t = expRayAt g x₀ v₀ (s * t)
```

## Scope completed

- Proved the zero-velocity chart state is a constant solution of the
  geodesic flow and consumed same-anchor Gronwall uniqueness to obtain the
  constant manifold germ.
- Proved the reparametrized state
  `t ↦ ((γ (s * t)).1, s • (γ (s * t)).2)` solves the same chart ODE with
  initial state `(extChartAt I x₀ x₀, s • v₀)`.
- Used the chain rule for `t ↦ s * t`, component derivative lemmas for the
  geodesic flow, and bilinearity of the Christoffel continuous-linear-map
  slots to identify the scaled acceleration term.
- Consumed same-anchor uniqueness again to prove the germ homogeneity law.
- Added the honest germ-level exponential ray API `expRayAt` and restated
  zero and homogeneity through it.

## Next decomposition

1. Velocity-smoothness of the germ family `(v₀, t) ↦ geodesicGermAt g x₀ v₀ t`
   in the anchor chart, reusing smooth dependence of ODE solutions.
2. Chart derivative at the origin for the eventual
   `v ↦ expRayAt g x₀ v 1` analogue: prove identity after a local-domain
   package is available, using homogeneity plus the chart initial-velocity
   theorem.
3. Gauss lemma prerequisites: formalize radial variations, metric
   compatibility along geodesics, and the radial/orthogonal pairing identity.
4. Chart-overlap independence: show compatible anchor-chart choices produce
   the same manifold germ on common neighborhoods, then expose chart-free
   statements.

## Verification

Forbidden-token check:

```text
rg -n "\b(sorry|axiom|native_decide)\b" Poincare/Global/ExponentialGerm.lean
```

Actual result: no matches.

Required build command:

```text
lake build Poincare.Global.ExponentialGerm
```

Actual result:

```text
Build completed successfully (2826 jobs).
```

The build emitted only pre-existing warnings from imported modules; there were
no warnings reported for `Poincare/Global/ExponentialGerm.lean`.
