# M5-glob-28 blocked: F-transition law reduced to the missing D-germ package

## Status

Blocked on the fully non-hypothetical Cartan F-transition law, with verified
strict-partial progress in the required new Lean file:

- `Poincare/Global/FTransition.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.FTransition
  .exists_cartanChartMap_christoffelAt_F_transition_law_on_punctured_ball
```

It consumes the M5-glob-27 field theorem
`DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball`.
For every nonzero `v` in the returned radius, it proves the signed
Christoffel transport law for the Cartan chart map after supplying the
remaining chart-indexed regularity/germ inputs:

- a chart-indexed derivative field `D : E3 -> E3 ->L[ℝ] E3`;
- the point-value bridge `D (eM v) = DF v` to the selected field;
- `HasFDerivAt D (fderiv ℝ D (eM v)) (eM v)`;
- symmetry of `(fderiv ℝ D (eM v))`;
- the eventual metric-pullback germ around `eM v`;
- first derivatives of the raw source and target chart metrics;
- nondegenerate bilinear representatives for the source and target metrics.

The proof differentiates the supplied eventual pullback germ via
`GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq`, uses the
M5-glob-27 field for invertibility and the pointwise pullback identity, and
then applies
`GeodesicTransport.christoffelAt_map_eq_signed_transport_of_differentiated_pullback`.

## Blocking boundary

The repository still does not export a non-hypothetical chart-indexed
Cartan derivative field near `z = exp_x(v)` with:

```lean
D (eM v) = DF v
HasFDerivAt D (fderiv ℝ D (eM v)) (eM v)
∀ a b, (fderiv ℝ D (eM v) a) b = (fderiv ℝ D (eM v) b) a
```

nor the corresponding eventual pullback germ:

```lean
(fun q => G₁ (F q) (D q a) (D q b)) =ᶠ[𝓝 (eM v)]
  (fun q => G₀ q a b)
```

The M5-glob-27 field is pointwise and selected by choice in normal
coordinates.  It proves invertibility, strict derivative of the Cartan chart
map at each endpoint, and the pointwise raw chart-metric pullback identity,
but it does not yet provide differentiability of the selected field or a
neighborhood-level pullback identity.  Discharging those inputs is the
remaining work needed to turn the strict partial into the full F-transition
law.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/FTransition.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/FTransition.lean
git diff --check -- Poincare/Global/FTransition.lean
lake build Poincare.Global.FTransition
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
42:theorem exists_cartanChartMap_christoffelAt_F_transition_law_on_punctured_ball

git diff --check -- Poincare/Global/FTransition.lean
exit status 0

lake build Poincare.Global.FTransition
Built Poincare.Global.FTransition
Build completed successfully (3218 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
