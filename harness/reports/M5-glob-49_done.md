# M5-glob-49 done: third-variation PL opener

## Result

Added the required new file:

- `Poincare/Global/ThirdVariation.lean`

No existing Lean files were edited, including `Poincare.lean`.

The new isolated theorem is:

```lean
theorem Poincare.GeodesicTransport
  .exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE
```

It proves the Picard-Lindelöf package for the linearized ODE of the
doubly-augmented chart-Christoffel field along any continuous hosted
doubly-augmented curve.  The proof builds the doubly-augmented vector field

```lean
(z, ξ) ↦ (F z, D F z ξ)
```

with

```lean
F = augmentedGeodesicFlowField (chartChristoffelField g x₀)
```

and uses the `ContDiff ℝ 2` augmented-field export from
`FlowSmoothness.lean` to prove that this doubly-augmented field is
`ContDiff ℝ 1`.  Its derivative composed with the continuous hosted curve is
then a continuous time-dependent linear coefficient, so the existing generic
linear-ODE PL package applies.

This is the stage-one third-variation replay: the doubly-augmented system and
the PL package for its linearization.  It does not yet discharge the
third-variation residual/Gronwall theorem or upgrade `FieldProducer`'s
`sourceD`/`targetD` fields to `ContDiffAt ℝ 1`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ThirdVariation.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ThirdVariation.lean
git diff --check -- Poincare/Global/ThirdVariation.lean
lake build Poincare.Global.ThirdVariation
```

Actual result:

```text
forbidden-token scan: no matches
top-level declaration scan:
40:theorem exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE

git diff --check -- Poincare/Global/ThirdVariation.lean
exit status 0

lake build Poincare.Global.ThirdVariation
✔ [2836/2836] Built Poincare.Global.ThirdVariation (2.5s)
Build completed successfully (2836 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully.
