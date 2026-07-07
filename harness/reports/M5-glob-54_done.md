# M5-glob-54 done: doubly augmented residual instantiation

## Status

Verified Lean payload was added in the required new file:

- `Poincare/Global/DoublyResidual.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds the Frechet-parameter residual comparison:

```lean
theorem Poincare.flowEndpoint_hasFDerivAt_of_linearized_gronwall
```

This is the vector-parameter version of the residual/Gronwall argument from
`SecondFlowDerivative.lean`: given a common flow tube, compact Taylor
remainder, compact Lipschitz constant, and a linearized endpoint family
represented by a CLM at time `t`, the endpoint map has that CLM as its
Frechet derivative.

The chart-Christoffel instantiation is:

```lean
theorem Poincare.GeodesicTransport
  .chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_data
```

It pairs the augmented flow `β` with its first variation `Ξ` as

```lean
fun y' τ => (β y'.1 τ, Ξ y'.1 y'.2 τ)
```

and verifies by substitution that this paired curve solves the doubly
augmented field

```lean
fun y' =>
  let F := augmentedGeodesicFlowField (chartChristoffelField g x₀)
  (F y'.1, (fderiv ℝ F y'.1) y'.2)
```

The proof discharges the doubly augmented residual ingredients using:

- `FlowSmoothness.lean` via
  `exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall`
  to get the `C2` augmented field and a compact Lipschitz constant for the
  doubled field;
- `FieldC1.lean` via
  `chartChristoffel_doublyAugmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex`
  for the compact Taylor remainder;
- the supplied third-variation ODE family `Ω`, with endpoint identification
  `Ω h t = D h`, to conclude the `HasFDerivAt` endpoint statement.

This file intentionally does not prove the later continuity or `C1` assembly
for `q ↦ fderiv ℝ e q`.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/DoublyResidual.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/DoublyResidual.lean
git diff --check -- Poincare/Global/DoublyResidual.lean
lake build Poincare.Global.DoublyResidual
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
35:theorem eventually_const_mul_norm_le_nhds_zero_normed {C δ : ℝ}
59:theorem residual_uniform_isLittleO_on_Icc_of_gronwall_bound_param
115:theorem residual_isLittleO_at_fixedTime_of_uniform_param
134:theorem flowEndpoint_hasFDerivAt_of_linearized_gronwall
416:theorem chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_data

git diff --check -- Poincare/Global/DoublyResidual.lean
exit status 0

lake build Poincare.Global.DoublyResidual
✔ [2843/2843] Built Poincare.Global.DoublyResidual (17s)
Build completed successfully (2843 jobs).
```

The build replayed pre-existing imported-module warnings; none were new errors
in `Poincare.Global.DoublyResidual`.
