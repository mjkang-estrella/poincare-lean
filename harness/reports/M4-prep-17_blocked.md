# M4-prep-17 blocked report

## Status

The curvature-action trace fold was re-derived from the current definitions.
It does not produce the frozen `RicciSecondDerivCurvatureCommutationAt` RHS.

Per the worker contract and task instructions, I stopped before changing the
frozen evolution statement or adding an assumption.  No Lean theorem was added.

## Definitions used

Write

```text
R(a,b,c,d) = g.inner x (curvatureOp g.leviCivita a b c) d
L(u,w) = lichnerowiczCurvatureAt g (ricciVariationField g) x u w
A(u,w) = ricciActionOnTensorAt g (ricciVariationField g) x u w
Q(u,w) = ricciQuadraticAt g x u w
```

The current definitions give

```text
CA(a,b,p,q)
  = covTensor2SecondDerivCurvatureActionAt g Ric x a b p q
  = - Ric(R(a,b)p, q) - Ric(p, R(a,b)q)

L(u,w) = sum_i Ric(R(b_i,u)w, sharp_i)
A(u,w) = Ric(Ric# u, w) + Ric(u, Ric# w)
Q(u,w) = 2 * L(u,w)
```

The last equality is already formalized as
`ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField`.

## Correct fold

For the first trace block,

```text
sum_i CA(b_i,u,w,sharp_i)
  = -sum_i Ric(R(b_i,u)w, sharp_i)
    -sum_i Ric(w, R(b_i,u)sharp_i)
```

The first summand is `-L(u,w)`.

For the second summand, the traced curvature vector is

```text
sum_i R(b_i,u)sharp_i = -Ric# u
```

because pairing with an arbitrary `z` gives

```text
sum_i R(b_i,u,sharp_i,z)
  = -sum_i R(b_i,u,z,sharp_i)
  = -Ric(u,z).
```

Therefore

```text
-sum_i Ric(w, R(b_i,u)sharp_i) = Ric(w, Ric# u) = Ric(Ric# u, w).
```

So

```text
sum_i CA(b_i,u,w,sharp_i) = -L(u,w) + Ric(Ric# u, w).
```

The same calculation with `u` and `w` swapped gives

```text
sum_i CA(b_i,w,u,sharp_i) = -L(w,u) + Ric(u, Ric# w).
```

Using the Riemann pair symmetry and last-pair antisymmetry, and the symmetry of
`Ric`, the mixed contraction is symmetric on the Ricci field:

```text
L(w,u) = L(u,w).
```

Thus the actual fold is

```text
sum_i CA(b_i,u,w,sharp_i) + sum_i CA(b_i,w,u,sharp_i)
  = A(u,w) - 2 * L(u,w)
  = A(u,w) - Q(u,w).
```

No new Riemann-contraction vocabulary is needed.

This is not the M4-prep-15 target

```text
2 * L(u,w) - A(u,w) - Q(u,w) = -A(u,w).
```

## Coefficient pinning

### Space form

For the repository's constant-curvature convention

```text
R(a,b,c,d) = k * (g(a,c)g(b,d) - g(a,d)g(b,c)),
Ric = lambda * g,  lambda = (1 - n) * k,
```

the M4-prep-16 computation gives

```text
sum CA + sum CA = 0.
```

The corrected fold gives

```text
A - Q = 2 * lambda^2 * g(u,w) - 2 * lambda^2 * g(u,w) = 0.
```

The M4-prep-15 fold gives `-A`, i.e.

```text
-2 * lambda^2 * g(u,w),
```

which is nonzero for a nonflat space form with `g(u,w) != 0`.

### Non-Einstein 3D algebraic pattern

Take an orthonormal frame in dimension three with diagonal Ricci eigenvalues

```text
r1 = 1, r2 = 2, r3 = 4.
```

The sectional components satisfying the three-dimensional Ricci trace equations
are

```text
K12 = (r1 + r2 - r3) / 2 = -1/2
K13 = (r1 + r3 - r2) / 2 =  3/2
K23 = (r2 + r3 - r1) / 2 =  5/2.
```

For `u = w = e1`,

```text
L(e1,e1) = r2 * K12 + r3 * K13 = 2 * (-1/2) + 4 * (3/2) = 5,
A(e1,e1) = 2 * r1^2 = 2,
Q(e1,e1) = 2 * L(e1,e1) = 10.
```

The corrected fold predicts

```text
A - Q = 2 - 10 = -8.
```

Directly expanding the two CA traces gives the same number:

```text
CAu = -L + Ric(Ric# e1, e1) = -5 + 1 = -4,
CAw = -5 + 1 = -4,
CAu + CAw = -8.
```

The false fold would give `-A = -2`, so this pattern separates the
Lichnerowicz and Ricci-action coefficients.

## Downstream consequence

M4-prep-15 proved the Hessian-cancelled assembly shape

```text
deltaRicciSecondDerivContractionAt g (-2 Ric) x u w
  = roughTensorLaplacianAt g Ric x u w - CAu - CAw.
```

Substituting the corrected fold gives

```text
rough - (A - Q) = rough - A + Q.
```

Since `Q = 2 * L`, this is

```text
rough + 2 * L - A.
```

The frozen `RicciSecondDerivCurvatureCommutationAt` RHS is

```text
rough - 2 * L + A + Q = rough + A.
```

These agree only under the extra accidental condition `L = A`.  They are
already different on a nonflat space form: the Hessian-cancelled assembly gives
`rough`, while the frozen RHS gives `rough + 2 * lambda^2 * g(u,w)`.

Therefore the frozen `RicciSecondDerivCurvatureCommutationAt` / downstream
`SatisfiesRicciEvolutionAt` RHS is inconsistent with the corrected algebraic
fold from the current definitions.  This is a definition/target-level issue for
orchestrator review.

## Verification

Command run:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: succeeded.  The build emitted existing warnings only.
