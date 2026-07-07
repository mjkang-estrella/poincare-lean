# M5-glob-15 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/DifferentiatedCompat.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.chartGeodesicMetric_transportedChristoffel_pairing_eq_of_differentiated_pullback
```

## Proved strict partial

The theorem proves the algebraic compatibility step after the differentiated
metric pullback identity is available.

It shows that, on a cutoff-one chart overlap, the signed transported source
Christoffel field

```text
Dσ(Γ⁰(u,v)) - D²σ(u,v)
```

satisfies the target Koszul metric-compatibility pairing identity on
transported vectors:

```text
G¹(DσΓ⁰(u,v) - D²σ(u,v), Dσw)
  =
1/2 * (∂G¹[Dσv](Dσu,Dσw)
     + ∂G¹[Dσu](Dσv,Dσw)
     - ∂G¹[Dσw](Dσv,Dσu)).
```

The proof uses:

- the proven cutoff-one pullback law from
  `chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one`;
- the source compatibility identity
  `chartChristoffelField_pairing_eq_blendedChartMetric`;
- symmetry of `D²σ`, obtained from
  `ContDiffAt.isSymmSndFDerivAt`;
- target metric symmetry to cancel the remaining second-derivative terms.

The differentiated pullback identity itself is an explicit non-vacuous
hypothesis `hdiff` in the theorem. It is used in the three Koszul directions
`(v,u,w)`, `(u,v,w)`, and `(w,v,u)`.

## Remaining blocker

The full task is not closed because this module does not yet prove the
calculus producer for `hdiff` from the previously proved pointwise pullback
law/germ:

```text
d/dz [G¹(σ z)(Dσ a)(Dσ b)] e
  =
∂G¹[Dσe](Dσa,Dσb)
  + G¹(D²σ(e,a),Dσb)
  + G¹(Dσa,D²σ(e,b))
  =
∂G⁰[e](a,b).
```

That producer still needs the local smoothness/germ packaging around the
cutoff-one zone and the chart-transition chain rule.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/DifferentiatedCompat.lean
git diff --check -- Poincare/Global/DifferentiatedCompat.lean
lake build Poincare.Global.DifferentiatedCompat
```

Actual result:

```text
rg: no matches
git diff --check: no output
lake build Poincare.Global.DifferentiatedCompat
✔ [2833/2833] Built Poincare.Global.DifferentiatedCompat (4.3s)
Build completed successfully (2833 jobs).
```

The build replayed pre-existing imported-module warnings. The new module
itself built successfully and introduced no reported warning.
