# M3-consequences-1 done report

## Theorem names

- `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'`
- `hamilton_scalar_reaction_bound_at`
- `hamilton_scalar_riccati_supersolution_at`
- `hamilton_scalar_minimum_riccati_step_at`
- `hamilton_finite_time_singularity`

## Summary

`Poincare/Global/ScalarEvolution.lean` now has a cleaned Hamilton wrapper whose
raw `DeltaGammaDivergenceTraceAssemblyAt` and
`DeltaGammaContractionTraceAssemblyAt` hypotheses are replaced by their proven
Hessian-trace discharge routes.  The remaining hypotheses are documented in the
file as concrete witnesses consumed by those discharge routes or by the scalar
variation / Bianchi / Ricci-divergence tail.

The pointwise Riccati chain is formalized in two steps: Hamilton scalar
evolution plus Ricci pinching gives
`dR/dt >= Delta R + (2/n) R^2`, and the spatial-minimum witness
`0 <= Delta R` gives the pointwise minimum inequality.

The finite-time obstruction is stated in shifted-time form: for
`tau in [0,T]`, geometric time is `t0 + tau`.  If Hamilton scalar evolution and
the spatial-minimum Laplacian witness hold along the track, and
`R(t0,x0) > 0`, then `T < n / (2 * R(t0,x0))`, by
`RicciFlow.riccati_forces_finite_time`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|axiom|native_decide)\b' Poincare/Global/ScalarEvolution.lean
lake env lean Poincare/Global/ScalarEvolution.lean
lake build Poincare.Global.ScalarEvolution
```

Results:

- no `sorry`, `axiom`, or `native_decide` matches in the edited Lean file;
- focused Lean check succeeds;
- `lake build Poincare.Global.ScalarEvolution` succeeds, with pre-existing
  dependency linter warnings.

## Commits

- `3b5e8f8a` Add clean Hamilton scalar evolution wrapper
- `64fb4bd7` Add pointwise scalar Riccati step
- `1c664be8` Add scalar finite-time Riccati obstruction
