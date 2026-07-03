# M4-pinch-2 blocked: 3D curvature decomposition reconstruction

## Verified progress

- Added the coefficient-pinned diagonal 3D reaction algebra in
  `Poincare/Global/RicciNorm.lean`.
- New names:
  - `PinchingAlgebra.diagonalTwoLichnerowiczFromRicci3Entry{1,2,3}`
  - `PinchingAlgebra.diagonalTwoLichnerowiczPure3Entry{1,2,3}`
  - `PinchingAlgebra.diagonalTwoLichnerowiczFromRicci3Entry{1,2,3}_eq_pure`
  - `PinchingAlgebra.diagonalRicciEvolutionReaction3Entry{1,2,3}`
  - `PinchingAlgebra.diagonalRicciEvolutionReaction3Entry{1,2,3}_eq`
  - `PinchingAlgebra.diagonalTwoLichnerowiczFromRicci3_spaceForm`
  - `PinchingAlgebra.diagonalRicciEvolutionReaction3_spaceForm`
  - `PinchingAlgebra.diagonalTwoLichnerowiczFromRicci3_one_one_two`
  - `PinchingAlgebra.diagonalRicciEvolutionReaction3_one_one_two`

The pinned formula is:

```text
2 Rm(Ric,.) = 3 R Ric - 4 Ric^2 + (2 |Ric|^2 - R^2) g
```

After subtracting the proven `ricciActionOnTensorAt` term (`2 Ric^2`), the
Ricci-evolution reaction becomes:

```text
3 R Ric - 6 Ric^2 + (2 |Ric|^2 - R^2) g
```

The checks now formally validate:

- space form `Ric = lambda g`: `2 Rm(Ric,.) = 2 lambda^2 g`, and the full
  reaction vanishes;
- non-Einstein diagonal pattern `(1,1,2)`: `2 Rm(Ric,.)` entries are all `4`,
  and the full reaction entries are `2, 2, -4`.

## Blocker

The task's Step 1 asks for the unconditional closed-manifold theorem

```text
g.inner x (curvatureOp g.leviCivita (extend p) (extend q) (extend r) x) s
  = g.riemannFromRicci3At x p q r s
```

under the dimension hypothesis `n = 3`.  The current library has the geometric
symmetries of the closed curvature tensor (`closedCurvaturePairSymmAt`,
`closedCurvaturePairLastPairAntisymmAt`, `closedCurvatureOp_first_bianchiAt`)
and the Ricci trace contraction, and the model file has the trace-free
Schouten/Weyl-candidate metric-trace statement.  It does not yet have the
needed abstract fiber lemma:

```text
Over a 3-dimensional real inner-product space, any multilinear (0,4) tensor
with Riemann symmetries and zero Ricci trace is identically zero.
```

Nor does the closed side currently package curvature-entry differences as a
public 4-linear object with a public 4-slot basis reconstruction theorem.  The
available basis expansion helpers are mainly for `(0,2)` tensors (for example
the private `tensor2_basis_expansion_left`) and trace contractions.  Without
that 3D reconstruction/extensionality lemma, proving the full equality would
require either an unsound assumption or a fake statement-layer shortcut, both
forbidden by the worker contract.

## Verification

- Baseline before edits:
  `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`
  succeeded.
- After coefficient edits:
  `lake build Poincare.Global.RicciNorm` succeeded.

## Next atom

Prove the abstract 3D fiber reconstruction lemma over
`EuclideanSpace ℝ (Fin 3)` or a 3-dimensional inner-product space, with:

1. a public 4-linear basis reconstruction/extensionality lemma;
2. hypotheses for the two pair antisymmetries, pair symmetry, first Bianchi,
   and zero Ricci trace;
3. conclusion that the tensor is zero on all four vectors.

Then instantiate it with the difference between the actual closed curvature
entry and `riemannFromRicci3At`.
