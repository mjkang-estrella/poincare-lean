# M5-glob-27 done: pointwise Cartan differential field assembled

## Status

Verified strict-partial progress in the required new Lean file:

- `Poincare/Global/DifferentialField.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.DifferentialField
  .exists_cartanChartDifferential_field_on_punctured_ball
```

From `RigidityComplete.cartanMap_isLocalIsometry`, it chooses the pointwise
endpoint equivalences `A_v` and `B_v` on the punctured shrunk normal ball and
assembles the field

```lean
DF v = CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)
```

For every `v` with `‖v‖ < ρ` and `v ≠ 0`, the theorem proves:

- `(DF v).IsInvertible`;
- `DF v` is the strict derivative of
  `CartanDifferential.cartanChartMap g x₀ p₀ L` at
  `expAtChartOpenPartialHomeomorph x₀ v`;
- the round-target/source metric pullback identity holds pointwise with `DF v`.

## Remaining boundary

This lands the pointwise differential field requested by the M5-glob-26
neighborhood-level demand.  It does not yet provide the neighborhood regularity
needed to instantiate `LCNaturality`: there is still no exported
`HasFDerivAt DF (fderiv ℝ DF z) z` / second-derivative symmetry package, nor the
eventual pullback germ differentiated through `PullbackDifferentiate`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/DifferentialField.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/DifferentialField.lean
git diff --check -- Poincare/Global/DifferentialField.lean
lake build Poincare.Global.DifferentialField
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
39:theorem exists_cartanChartDifferential_field_on_punctured_ball

git diff --check -- Poincare/Global/DifferentialField.lean
exit status 0

lake build Poincare.Global.DifferentialField
Built Poincare.Global.DifferentialField
Build completed successfully (3215 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
