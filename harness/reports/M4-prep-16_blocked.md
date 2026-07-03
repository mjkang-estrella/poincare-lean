# M4-prep-16 blocked report

## Status

The requested final curvature-action trace fold is false under the current
definitions.  I stopped before altering the frozen
`RicciSecondDerivCurvatureCommutationAt` target or adding any assumption.

The obstruction is already visible in the required constant-curvature sanity
check.

## Refuted fold

The blocked report from M4-prep-15 asks for:

```lean
(∑ i, covTensor2SecondDerivCurvatureActionAt
    g (ricciVariationField g) x (b i) u w (sharp i))
  +
(∑ i, covTensor2SecondDerivCurvatureActionAt
    g (ricciVariationField g) x (b i) w u (sharp i))
=
  2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
    - ricciActionOnTensorAt g (ricciVariationField g) x u w
    - ricciQuadraticAt g x u w
```

But for the Ricci field,

```lean
ricciQuadraticAt g x u w =
  2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
```

by `ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField`.
So the displayed right-hand side reduces to:

```lean
- ricciActionOnTensorAt g (ricciVariationField g) x u w
```

## Constant-curvature sanity check

Use the repository's constant-curvature convention

```text
Rm(a,b,c,d) = k * (g(a,c) g(b,d) - g(a,d) g(b,c))
```

from `constCurvatureForm`.  Its Ricci trace is

```text
Ric = lambda * g,  lambda = (1 - n) * k
```

as recorded by `constCurvatureForm_ricci_trace`.

For any nonflat space form with `lambda != 0`, the two terms in each
curvature-action trace cancel:

```text
CAu =
  - sum_i Ric(R(b_i,u)w, sharp_i)
  - sum_i Ric(w, R(b_i,u)sharp_i)
= -lambda^2 * g(u,w) + lambda^2 * g(u,w)
= 0

CAw =
  - sum_i Ric(R(b_i,w)u, sharp_i)
  - sum_i Ric(u, R(b_i,w)sharp_i)
= -lambda^2 * g(u,w) + lambda^2 * g(u,w)
= 0
```

So the left-hand side of the displayed fold is `0`.

The right-hand side, however, is:

```text
- ricciActionOnTensorAt Ric
= -(Ric(lambda * u, w) + Ric(u, lambda * w))
= -2 * lambda^2 * g(u,w)
```

This is nonzero when `lambda != 0` and `g(u,w) != 0`.  Therefore the fold as
displayed cannot be proved from the current definitions.

## Convention mismatch

The mismatch is not in the corrected mixed definition of
`lichnerowiczCurvatureAt`: its Ricci-field quadratic relation is
definitionally the current `ricciQuadraticAt`.

The mismatch is the expected fold target for the trace of
`covTensor2SecondDerivCurvatureActionAt`.  With its current definition

```lean
-h x (R(u,v)p) q - h x p (R(u,v)q)
```

the constant-curvature trace of the two curvature-action blocks cancels
internally.  It cannot produce the negative Ricci-endomorphism action required
by the displayed fold.

Consequently, the M4-prep-15 assembly cannot be completed as stated.  The next
safe step is to revisit the sign or slot convention connecting the traced
tensor Ricci identity curvature action to the expanded Lichnerowicz/Ricci
action/quadratic vocabulary, then rerun this same space-form sanity check
before attempting the Lean proof.
