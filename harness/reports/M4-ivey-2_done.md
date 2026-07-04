# M4-ivey-2 done: eigenvalue improvement lemma

## Implemented surface

- `PinchingAlgebra.diagonalRicciNormSq3_nonneg`
- `PinchingAlgebra.diagonalTracelessRicciNormSq3_nonneg`
- `PinchingAlgebra.pinchedTracelessAdmissibleDelta3_le_actual_min_bound`
- `PinchingAlgebra.diagonalActualMinPinchingBoundaryNumerator3_eq_neg`
- `PinchingAlgebra.diagonalActualMinPinchingBoundaryNumerator3_nonpos`
- `PinchingAlgebra.diagonalTracelessPinchingReactionNumerator3_nonpos_of_ordered_actual_min`
- `PinchingAlgebra.diagonalTracelessPinchingReactionNumerator3_swap12`
- `PinchingAlgebra.diagonalTracelessPinchingReactionNumerator3_swap23`
- `PinchingAlgebra.TracelessPinchingEigenvalueImprovementLemma3_holds`

## Proof route

The proof keeps the frozen `TracelessPinchingEigenvalueImprovementLemma3`
statement unchanged and adds a theorem proving it.

For ordered eigenvalues `a <= b <= c`, the actual minimum ratio `a / R`
dominates the stated pinching constant.  The admissible delta bound is
therefore transferred to

```text
delta <= 6 a^2 / (R^2 - 2 a R + 3 a^2).
```

At that sharp boundary, the denominator-multiplied numerator factors as

```text
-4 (c - b)^2 * P(a, b - a, c - b),
```

where `P` is a polynomial with nonnegative coefficients in the ordered
slacks.  This gives the boundary nonpositivity.  The existing decomposition

```text
old Hamilton-Schur numerator + 2 delta |Ric|^2 |Ric°|^2
```

then bounds the correction term by the boundary correction.  The final theorem
case-splits the six possible eigenvalue orderings and uses adjacent-swap
symmetry of the numerator.

## Verification

- `lake env lean Poincare/Global/RicciNorm.lean` succeeded.
- `lake build Poincare.Global.RicciNorm` succeeded.
- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/RicciNorm.lean` returned no matches.
- `git diff --check` succeeded.
