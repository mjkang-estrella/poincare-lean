# M5-glob-56 blocked: hosted third-variation PL family exported

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/ThirdFamily.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .exists_hosted_thirdVariation_solution_family_on_pl_closedBall
```

For any continuous hosted doubly-augmented base curve

```lean
ζ : ℝ → A × A
```

where `A = (E × E) × (E × E)`, the theorem uses the existing level-three PL
package

```lean
exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE
```

at the zero variation and exposes the chosen Picard-Lindelöf fixed-point
family

```lean
Ω : A × A → ℝ → A × A
```

on the PL closed ball.  For every initial variation in that ball, it exports:

```lean
Ω h 0 = h
```

the third-variation linear ODE

```lean
HasDerivWithinAt (Ω h)
  (fderiv ℝ
    (fun y : A × A =>
      let F : A → A :=
        augmentedGeodesicFlowField (chartChristoffelField g x₀)
      (F y.1, (fderiv ℝ F y.1) y.2))
    (ζ t) (Ω h t))
  (Icc (-ε) ε) t
```

and the PL closed-ball invariant.

## Blocking boundary

This does not yet discharge the full hosted third-variation continuity demand.
The remaining missing exports are still:

1. a rescaled/all-direction third-variation endpoint family represented by a
   continuous linear map at fixed time, usable as `hD` in `DoublyResidual`;
2. the hosted instantiation tying `ζ` to the produced
   `(β y.1 τ, Ξ y.1 y.2 τ)` datum from the uniform-flow/residual layer;
3. continuous dependence of the third-variation endpoint CLM in the base point,
   sufficient to obtain `ContDiffAt ℝ 1 (fun q => fderiv ℝ e q) q`.

Consequently `CanonicalC1` / `LevelThreeFeed` / `TowerCloses` are not yet
fired by this file, and the unconditional F-transition law is not closed here.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ThirdFamily.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ThirdFamily.lean
lake build Poincare.Global.ThirdFamily
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
39:theorem exists_hosted_thirdVariation_solution_family_on_pl_closedBall

lake build Poincare.Global.ThirdFamily
✔ [2837/2837] Built Poincare.Global.ThirdFamily (1.0s)
Build completed successfully (2837 jobs).
```

The build replayed pre-existing imported-module warnings; no warning was
emitted from `Poincare/Global/ThirdFamily.lean`.
