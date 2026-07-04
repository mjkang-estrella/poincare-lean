# M4-ivey-5 blocked: gradient reserve proves nonpositivity, not the frozen full damping target

## Summary

The requested theorem name is `satisfiesTracelessPinchingEvolutionAt_of_ricciFlow`.
The current formal target predicate is
`ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt`,
whose right hand side includes the full completed-square term
`tracelessPinchingGradientDampingAt`.

The exact item-5 algebra from `M4-ivey-4_progress.md` shows that, with

```text
R = scalarAt, N = |Ric|^2, A = |nabla Ric|^2, S = |nabla R|^2,
B = <nabla Ric, nabla R tensor Ric>, p = 2 - delta,
```

the assembled gradient numerator is

```text
-2 * R^2 * A + 2 * p * R * B + (delta / 3) * R^2 * S - p * N * S
```

whereas the existing damping vocabulary is

```text
-2 * (R^2 * A - 2 * R * B + N * S).
```

Their difference is exactly

```text
delta * ((N + R^2 / 3) * S - 2 * R * B).
```

This difference is not pointwise nonpositive, even under positive Ricci
pinching, for any `delta > 0`.

## Gradient pins

Flat/parallel pin:

```text
R = N = A = B = S = 0.
```

Both the exact gradient numerator and the completed-square damping numerator
are zero. This is a neutral sanity check.

Linear-scalar pure-trace pin:

Work in a 3D orthonormal frame at one point. Take

```text
nabla Ric = (nabla R / 3) * g
```

and take a non-Einstein positive Ricci tensor. Then

```text
A = S / 3
B = R * S / 3
N = R^2 / 3 + |Ric^0|^2.
```

Therefore the defect becomes

```text
delta * ((N + R^2 / 3) * S - 2 * R * B)
  = delta * |Ric^0|^2 * S.
```

This is strictly positive whenever `delta > 0`, `S > 0`, and the Ricci tensor
is not Einstein.

On the same data, the exact gradient numerator is

```text
-(2 - delta) * |Ric^0|^2 * S,
```

while the existing damping numerator is

```text
-2 * |Ric^0|^2 * S.
```

Thus the exact gradient contribution is larger than the current damping target
by

```text
delta * |Ric^0|^2 * S.
```

Shrinking the admissible range for `delta` does not fix this unless
`delta = 0`, but the predicate requires `0 < delta` and the improved pinching
argument needs a positive exponent.

## Consequence

The orchestrator's reserve route is mathematically consistent with proving
that the total gradient contribution is nonpositive:

```text
exact gradient <= 0
```

after bounding the positive defect by part of the `-2 * |nabla Ric|^2`
reserve. However, it does not prove the stronger current predicate RHS with
the full `tracelessPinchingGradientDampingAt` term:

```text
exact gradient <= tracelessPinchingGradientDampingAt.
```

That stronger inequality is refuted by the pure-trace pin above.

## Required correction

To proceed, the formal target must be changed in one of these non-equivalent
ways:

1. Replace the full completed-square damping in
   `SatisfiesTracelessPinchingImprovementEvolutionAt` by an honest
   reserve-absorbed gradient term, or by no explicit negative gradient term
   after proving the total gradient contribution is nonpositive.
2. Carry the explicit defect term in the evolution predicate and prove the
   reserve-absorbed total gradient sign separately.
3. Define a new corrected theorem/predicate rather than proving the current
   full-damping predicate.

Per the worker contract, I did not alter the existing frozen target predicate
or force a proof of a statement contradicted by the gradient pin.

