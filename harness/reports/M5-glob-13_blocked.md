# M5-glob-13 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/TransitionLaw.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.chartTransitionDeriv_chartChristoffelField_minus_sndFDeriv_symm
```

## Proved strict partial

The theorem proves the torsion-free half of the LC-uniqueness route for the
minus-correction transported chart expression:

```text
Dσ(Γ⁰(z)(u,v)) - D²σ(z)(u,v)
  =
Dσ(Γ⁰(z)(v,u)) - D²σ(z)(v,u)
```

in the repo's actual API shape:

```text
chartTransitionDeriv x₀ y₀ z ((chartChristoffelField g x₀ z) u v)
  - fderiv (chartTransitionDeriv x₀ y₀) z u v
```

The proof uses:

- symmetry of the source `chartChristoffelField`, reduced to
  `CovariantDerivative.christoffelAt_symm` for the blended chart metric;
- symmetry of the ordinary second Frechet derivative from
  `ContDiffAt.isSymmSndFDerivAt`.

## Remaining blockers

The full abstract transition law is still not proved in this task.

1. The metric-compatibility half of the transported value operator was not
   packaged.  It still needs differentiated transport of
   `chartMetric_chartTransitionDeriv` into the exact
   `MetricCompatibleAt`/Koszul shape required by
   `Poincare/LeviCivitaUniqueness.lean`.

2. The strict partial proves symmetry in source velocity slots.  The final
   target-chart statement still needs the inverse-derivative packaging
   `Γ̃(y)(a,b)` with `a,b` in target coordinates, then the uniqueness
   invocation identifying it with `chartChristoffelField g y₀`.

3. The velocity-component chain-rule input consumed by
   `ChristoffelTransition.lean` is still not produced from the abstract law.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/TransitionLaw.lean
git diff --check -- Poincare/Global/TransitionLaw.lean
lake build Poincare.Global.TransitionLaw
```

Actual result:

```text
rg: no matches
git diff --check: no output
lake build Poincare.Global.TransitionLaw
✔ [2831/2831] Built Poincare.Global.TransitionLaw (10s)
Build completed successfully (2831 jobs).
```

The build replayed pre-existing imported-module warnings; the new module
itself built successfully and introduced no reported warning.
