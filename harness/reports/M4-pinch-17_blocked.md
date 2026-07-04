# M4-pinch-17 blocked: frozen pinching quotient damping is too strong

## Verdict

I did not change the frozen target
`SatisfiesHamiltonPinchingEvolutionInequality3At`.  The requested preliminary
quotient-rule sanity check refutes its current damping coefficient on the
non-Einstein diagonal test pattern already present in `Poincare.Global.RicciNorm`.

The space-form coefficient pin passes, but the `(1,1,2)` pattern fails:
the quotient reaction obtained from the proven parabolic inputs is `-1/4`,
whereas the frozen damping term is `-1/3`.  Since `-1/4 > -1/3`, the target
inequality would demand a strictly stronger bound than the two proven
parabolic forms supply.

## Frozen target shape

`SatisfiesHamiltonPinchingEvolutionInequality3At` requires, at `R > 0`,

```text
Q' <= ΔQ + (2/R) <∇R, ∇Q> - (2/R) |Ric°|^2
```

where `Q = |Ric|^2/R^2` and
`pinchingTracelessDampingAt = -(2/R) * tracelessRicciNormSqAt`.

## Quotient-rule reaction algebra

Write

```text
N = |Ric|^2
R = scalar
V = R^2
Q = N/V
```

Ignoring spatial derivatives for the algebraic coefficient check, the proven
inputs give

```text
Q_reaction = N_reaction / R^2 - N * (R^2)_reaction / R^4
           = N_reaction / R^2 - N * (4 R N) / R^4.
```

The product-rule drift `+(2/R)<∇R,∇Q>` is irrelevant for this constant
diagonal check because the spatial gradients vanish.

## Space-form check

For `(λ, λ, λ)`:

```text
R = 3λ
N = 3λ^2
N_reaction = 12λ^3       -- metric-motion contribution, lower-Ricci reaction zero
(R^2)_reaction = 4RN = 36λ^3
```

Then

```text
Q_reaction = 12λ^3 / (9λ^2) - (3λ^2 * 36λ^3) / (81λ^4)
           = 4λ/3 - 4λ/3
           = 0.
```

The traceless damping is also zero, so the space-form cancellation is correct.

## Non-Einstein check: diagonal `(1,1,2)`

Existing pinned diagonal facts in `Poincare.Global.RicciNorm` give:

```text
R = 4
N = 6
|Ric°|^2 = N - R^2/3 = 2/3
2<reaction,Ric> = -8
metric-motion contribution = +4 tr(Ric^3) = 40
```

Thus the `|Ric|^2` algebraic reaction/motion term is

```text
N_reaction = -8 + 40 = 32.
```

The scalar-square reaction is

```text
(R^2)_reaction = 4RN = 4 * 4 * 6 = 96.
```

Therefore the quotient reaction supplied by the proven parabolic forms is

```text
Q_reaction = 32 / 16 - 6 * 96 / 16^2
           = 2 - 576/256
           = 2 - 9/4
           = -1/4.
```

But the frozen damping term is

```text
-(2/R) |Ric°|^2 = -(2/4) * (2/3) = -1/3.
```

With zero spatial gradients and zero spatial Laplacian in this coefficient
test, the frozen target would require

```text
-1/4 <= -1/3,
```

which is false.

## Relevant Lean anchors

- `SatisfiesHamiltonPinchingEvolutionInequality3At`
- `pinchingQuotientGradientDrift3At`
- `pinchingTracelessDampingAt`
- `diagonalTracelessRicciNormSq3_one_one_two`
- `diagonalRicciNormEvolutionReactionTrace3_one_one_two`
- `diagonalRicciNormMetricMotionNegTwoRicci3_one_one_two`
- `hasDerivAt_scalarAt_sq_of_satisfiesHamiltonScalarEvolutionAt`
- `deriv_ricciNormSqAt_le_laplacianAt_add_reactionMotionTrace3`

## Consequence

Per the worker contract, I stopped instead of proving quotient calculus lemmas
against a frozen target whose damping coefficient is refuted by the required
non-Einstein sanity check.  A later target likely needs either an explicit
algebraic quotient remainder term or a corrected damping decomposition before
the quotient-rule proof layer can be soundly landed.
