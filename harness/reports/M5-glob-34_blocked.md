# M5-glob-34 blocked: residual-to-Frechet upgrade lemma landed

## Status

Blocked on the fully non-hypothetical residual comparison for the selected
Cartan `DF` field, with verified strict-partial progress in the required new
Lean file:

- `Poincare/Global/DFrechetUpgrade.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .clmField_hasFDerivAt_of_residual_norm_le
```

It proves the calculus upgrade needed after the order-two residual comparison
has been supplied.  For a CLM-valued field

```lean
D : E → E →L[ℝ] E
```

and a candidate second derivative

```lean
CLM : E →L[ℝ] E →L[ℝ] E
```

the theorem consumes the direction-uniform residual bound

```lean
∀ c > 0, ∀ᶠ δ in 𝓝 0,
  ‖D (q + δ) - D q - CLM δ‖ ≤ c * ‖δ‖
```

and returns:

```lean
HasFDerivAt D CLM q
```

This is the exact final `o(‖δ‖)` to `HasFDerivAt` step described in the task.

## Blocking boundary

The repository still lacks the non-hypothetical bridge producing the above
residual bound for the selected Cartan derivative field used by
`DifferentialField`, `GermAndField`, and `FTransition`.

The obstruction is unchanged but now isolated more sharply:

- `SecondFlowDerivative.lean` proves fixed-time differentiability for scalar
  perturbations of an abstract augmented flow.
- `SecondDischarge.lean` instantiates that theorem at split geodesic and
  first-variation data.
- `SecondFrechet.lean` packages a second-variation endpoint family as a CLM
  when such a family is supplied.
- `DifferentialField.lean` defines the Cartan `DF` by pointwise
  `Classical.choose`; no exported API currently identifies its neighborhood
  increments with the second-variation endpoint residual, nor proves the
  direction-uniform residual bound for
  `DF (eM.symm (q + δ)) - DF (eM.symm q) - CLM δ`.

Therefore the unconditional `FTransition` theorem cannot yet be closed without
one additional theorem producing the concrete residual comparison for the
selected `DF` field and its local inverse-coordinate parametrization.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/DFrechetUpgrade.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/DFrechetUpgrade.lean
git diff --check -- Poincare/Global/DFrechetUpgrade.lean
lake build Poincare.Global.DFrechetUpgrade
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
31:theorem clmField_hasFDerivAt_of_residual_norm_le

git diff --check -- Poincare/Global/DFrechetUpgrade.lean
exit status 0

lake build Poincare.Global.DFrechetUpgrade
✔ [2840/2840] Built Poincare.Global.DFrechetUpgrade (11s)
Build completed successfully (2840 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
