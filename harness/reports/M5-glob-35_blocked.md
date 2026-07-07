# M5-glob-35 blocked: directional residual-to-operator upgrade landed

## Status

Blocked on the fully non-hypothetical comparison identifying the selected
Cartan `DF` field with the augmented second-variation endpoint family near the
basepoint.  Verified strict-partial progress was added in the required new
Lean file:

- `Poincare/Global/ConcreteResidual.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .chartField_hasFDerivAt_of_directional_residual_norm_le
```

It proves the operator-norm bridge demanded by the concrete residual step.  For
a chart-inverse-coordinate field

```lean
fun q' => DF (eM_symm q')
```

and a candidate second derivative

```lean
CLM : E →L[ℝ] E →L[ℝ] E
```

the theorem consumes the direction-uniform residual estimate

```lean
∀ c > 0, ∀ᶠ δ in 𝓝 0, ∀ u,
  ‖(DF (eM_symm (q + δ)) - DF (eM_symm q) - CLM δ) u‖ ≤
    (c * ‖δ‖) * ‖u‖
```

uses `ContinuousLinearMap.opNorm_le_bound` to convert it into the CLM norm
bound, and feeds `clmField_hasFDerivAt_of_residual_norm_le` to obtain:

```lean
HasFDerivAt (fun q' => DF (eM_symm q')) CLM q
```

## Blocking boundary

This closes the direction-to-operator residual conversion and the Frechet
upgrade for the chart-indexed field once the augmented endpoint residuals are
available in that exact form.

The repository still does not export the non-hypothetical bridge that rewrites
the selected `DF (eM.symm (q + δ))` values from `DifferentialField` as the
linearized endpoint values controlled by `SecondFlowDerivative` and
`SecondDischarge`.  Without that equality/comparison theorem, the augmented
remainders cannot yet be instantiated as the `hdir` hypothesis above, and the
unconditional `FTransition` law cannot honestly be closed in this worktree.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ConcreteResidual.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ConcreteResidual.lean
git diff --check -- Poincare/Global/ConcreteResidual.lean
lake build Poincare.Global.ConcreteResidual
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
32:theorem chartField_hasFDerivAt_of_directional_residual_norm_le

git diff --check -- Poincare/Global/ConcreteResidual.lean
exit status 0

lake build Poincare.Global.ConcreteResidual
✔ [2841/2841] Built Poincare.Global.ConcreteResidual (2.1s)
Build completed successfully (2841 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully and introduced no reported warning.
