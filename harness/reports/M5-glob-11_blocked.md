# M5-glob-11 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/ChristoffelTransition.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_signed_christoffel_transition
```

It proves the downstream re-anchor equality by assembling the velocity
component required by `ReanchorLawFinal` from two explicit chart-change inputs:

1. a derivative/chain-rule input for
   `chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2`, with a correction term `B t`;
2. the signed Christoffel transition identity
   `Γ¹(Dσ v,Dσ v) = Dσ(Γ⁰(v,v)) - B`.

The proof then feeds the resulting velocity-component hypothesis to
`shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_velocity_component`.

## Remaining blocker

The unconditional chart-change law is still not derivable from the currently
exported APIs.

The repo has the first-order metric transport identity
`chartMetric_chartTransitionDeriv` / `chartMetric_chartTransitionMFDeriv`, and
it has local value-level Levi-Civita uniqueness/transport machinery in
`LeviCivitaTransport.lean`.  I did not find an exported theorem that turns
those into either of the two inputs above:

```lean
HasDerivAt
  (fun s => chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2)
  (chartTransitionDeriv x₀ y₀ (γ t).1
      (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) + B t)
  t
```

and

```lean
(chartChristoffelField g y₀ (chartTransitionState x₀ y₀ γ t).1)
  (chartTransitionState x₀ y₀ γ t).2
  (chartTransitionState x₀ y₀ γ t).2 =
chartTransitionDeriv x₀ y₀ (γ t).1
  ((chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) - B t
```

There is also a sign issue in the task prose as written.  With this repo's
convention

```lean
geodesicFlowField Γ p = (p.2, -Γ p.1 p.2 p.2)
```

the usual chain rule for `η₂ = Dσ γ₂` gives

```text
η₂' = D²σ(v,v) - Dσ(Γ⁰(v,v)).
```

Therefore the target geodesic equation `η₂' = -Γ¹(Dσ v,Dσ v)` is compatible
with

```text
Γ¹(Dσ v,Dσ v) = Dσ(Γ⁰(v,v)) - D²σ(v,v),
```

not the plus-sign formula if `D²σ` denotes the ordinary second derivative.
The new theorem uses this signed form, with `B` representing the ordinary
second-derivative correction along the shifted geodesic.

## Verification

Commands run:

```bash
rg -n "\b(sorry|admit|axiom)\b|native_decide" Poincare/Global/ChristoffelTransition.lean
git diff --check -- Poincare/Global/ChristoffelTransition.lean
lake build Poincare.Global.ChristoffelTransition
```

Actual result:

```text
lake build Poincare.Global.ChristoffelTransition
✔ [2831/2831] Built Poincare.Global.ChristoffelTransition (2.2s)
Build completed successfully (2831 jobs).
```

The forbidden-token scan produced no matches, and `git diff --check` produced
no output.  The build replayed pre-existing imported-module warnings; the new
module itself did not introduce a warning in the final build.
