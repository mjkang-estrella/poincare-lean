# M4-pinch-24 done: maximum principle closes Hamilton pinching preservation

## Formalized

- Added the compactness witness and maximum-track API:
  - `exists_pinchingQuotientAt_isMaxOn`
  - `pinchingMaximumAt`
  - `pinchingMaximumTrack`
  - `pinchingMaximumAt_eq_of_isMaxOn`
  - `pinchingQuotientAt_le_pinchingMaximumAt`

- Added the local maximum/minimum calculus used by the quotient maximum step:
  - `gradientAt_eq_zero_of_isLocalMin`
  - `gradientAt_eq_zero_of_isLocalMax`
  - `laplacianAt_nonpos_of_isLocalMax`
  - `hamilton_pinching_spatial_max_step_at`

- Proved the preservation theorem:
  - `hamilton_pinching_preserved`

The final theorem is stated in maximum-track form: on a compact closed
three-dimensional Ricci-flow track satisfying the quotient evolution and
regularity hypotheses, `pinchingMaximumTrack gt t0 tau` is bounded above by
its initial value on `tau in [0,T]`.

The proof applies the existing closed parabolic minimum principle to
`u = C - Q`, where `C` is the initial pinching maximum and
`Q = pinchingQuotientAt`.  The abstract operator is
`Delta + (2/R)<grad R, grad .>`.  At a spatial minimum of `u`, the new
gradient-vanishing lemma kills the drift term and the existing closed
minimum Laplacian lemma supplies nonnegativity.  The quotient evolution,
gradient damping nonpositivity, and three-dimensional reaction sign give the
required supersolution inequality.

## Commits

- `a33da177` - Add pinching quotient maximum witness
- `79b836b0` - Add pinching quotient maximum step
- `0d8cc40f` - Prove Hamilton pinching preservation

## Verification

- `lake env lean Poincare/Global/ScalarEvolution.lean`
- `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`
- `git diff --check`
- Forbidden-token code diff scan: clean.

The requested combined build completed successfully.  Remaining output is
pre-existing linter noise, with the final `ScalarEvolution.lean` warning at
line 606 suggesting `simp` instead of `simpa`.
