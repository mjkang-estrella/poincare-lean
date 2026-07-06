# M5-model-5 done report

## Convention notes

`Poincare/ModelChristoffel.lean` defines
`christoffelFunctional G x u v` by

`(1 / 2) * ((DG_x u)(v,w) + (DG_x v)(u,w) - (DG_x w)(u,v))`

after testing against `w`. `christoffelAt G x b hb u v` is the metric-dual
vector representing that functional against `b`.

`christoffelOneForm_apply` flips the two vector slots:

`christoffelOneForm G b hb x s v = christoffelAt G x (b x) (hb x) v s`.

So the one-form API takes section-value first and direction second, while the
classical bilinear formula is stated for `christoffelAt ... u v`.

## Added file

New file only: `Poincare/Global/ConformalChristoffel.lean`.

No existing Lean import/root file was edited.

## Final signatures

- `conformalFlatMetric (f : E → ℝ) : E → E →L[ℝ] E →L[ℝ] ℝ`
- `conformalFlatBilin (f : E → ℝ) (z : E) : LinearMap.BilinForm ℝ E`
- `conformalFlatBilin_nondegenerate (f : E → ℝ) (z : E) (hf : f z ≠ 0)`
- `conformalChristoffelFormula (f : E → ℝ) (z gradf u v : E) : E`
- `fderiv_conformalFlatMetric`
- `christoffelAt_conformalFlatMetric`
- `christoffelOneForm_conformalFlatMetric_apply`
- `stereoInvFunAuxConformalFactorFDeriv`
- `hasFDerivAt_stereoInvFunAuxConformalFactor`
- `fderiv_stereoInvFunAuxConformalFactor`

The proved conformal formula is:

`Γ(u,v) = (Df_z u / (2 * f z)) • v + (Df_z v / (2 * f z)) • u - (inner ℝ u v / (2 * f z)) • gradf`,

assuming `f z ≠ 0`, `DifferentiableAt ℝ f z`, and
`∀ w, inner ℝ gradf w = fderiv ℝ f z w`.

The one-form theorem restates this as `Γ(v,s)` for
`christoffelOneForm ... z s v`.

## Specialization hook

`stereoInvFunAuxConformalFactorFDeriv` is a verified raw chain-rule derivative
operator for `16 / (‖z‖ ^ 2 + 4) ^ 2`, with `HasFDerivAt` and `fderiv` lemmas.
Pointwise it should simplify to
`u ↦ -64 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 3 * inner ℝ z u`; that scalar simplification is
left as an algebra cleanup, not a curvature blocker.

## Remaining roadmap

1. Add a pointwise simplification lemma for `stereoInvFunAuxConformalFactorFDeriv`.
2. Instantiate `gradf` for the stereographic factor using the Euclidean
   gradient vector corresponding to the derivative hook.
3. Connect the conformal chart metric from `RoundSphereChartMetric` to
   `conformalFlatMetric` at the chart-model level.
4. Feed `christoffelOneForm_conformalFlatMetric_apply` into the chart curvature
   computation, respecting the one-form slot flip.

## Verification

Actual command run:

`lake build Poincare.Global.ConformalChristoffel`

Actual result: succeeded, `Build completed successfully (2924 jobs).`
