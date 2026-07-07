# M5-glob-36 blocked: derivative-uniqueness bridge landed

## Status

Blocked on the fully unconditional `FTransition` law, but the derivative
uniqueness bridge requested in this slice was added and verified in the
required new Lean file:

- `Poincare/Global/DerivativeUnique.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.DerivativeUnique
  .exists_cartanChartField_hasFDerivAt_of_fderiv_directional_residual_on_punctured_ball
```

At each nonzero point in the selected punctured normal ball, the theorem proves
the pointwise derivative-uniqueness identification

```lean
DF v = fderiv ℝ F (eM v)
```

for the Cartan chart map

```lean
F := CartanDifferential.cartanChartMap g x₀ p₀ L
```

It then uses that identification on a neighborhood, via the derivative germ
from `GermAndField`, to rewrite any direction-uniform residual estimate for
`fderiv ℝ F`

```lean
∀ c > 0, ∀ᶠ δ in 𝓝 0, ∀ u,
  ‖(fderiv ℝ F (eM v + δ) - fderiv ℝ F (eM v) - CLM δ) u‖ ≤
    (c * ‖δ‖) * ‖u‖
```

into the concrete selected-field conclusion

```lean
HasFDerivAt (fun q => DF (eM.symm q)) CLM (eM v)
```

by feeding `ConcreteResidual.chartField_hasFDerivAt_of_directional_residual_norm_le`.

## Blocking boundary

The remaining unconditional `FTransition` closure still needs an exported,
non-hypothetical theorem producing the exact `fderiv ℝ F` directional residual
above from the augmented second-variation endpoint data, plus the required
second-derivative symmetry data for the chart-indexed field.  The current
repository has the augmented flow derivative and the concrete residual upgrade,
but not the final API that instantiates this new theorem without the residual
hypothesis.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/DerivativeUnique.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/DerivativeUnique.lean
git diff --check -- Poincare/Global/DerivativeUnique.lean
lake build Poincare.Global.DerivativeUnique
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
38:theorem exists_cartanChartField_hasFDerivAt_of_fderiv_directional_residual_on_punctured_ball

git diff --check -- Poincare/Global/DerivativeUnique.lean
exit status 0

lake build Poincare.Global.DerivativeUnique
✔ [3226/3226] Built Poincare.Global.DerivativeUnique (2.7s)
Build completed successfully (3226 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully and introduced no reported warning.
