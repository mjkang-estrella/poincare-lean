# M5-sphere-3 done: locally constant glue to constant curvature

## Completed

- Added the reusable manifold lemma
  `isLocallyConstant_of_extDerivFun_eq_zero` in
  `Poincare/ChartIdentification.lean`.
- The proof is chart-local: it identifies `extDerivFun` with the Fréchet
  derivative of the chart representative via `extDerivFun_apply_fixed_chart`,
  proves the representative derivative vanishes on the chart target, obtains an
  open level-set neighborhood from Mathlib's derivative-zero constancy lemma,
  and pulls that local constancy back through the chart.
- Added
  `scalarAt_constant_of_extDerivFun_eq_zero_connected` in
  `Poincare/Global/ScalarVariation.lean`, using `PreconnectedSpace` and
  `IsLocallyConstant.apply_eq_of_preconnectedSpace`.
- Added the unconditional composition theorem
  `hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected`.
  It chains the zero-traceless-Ricci Einstein criterion, the Schur
  `extDerivFun` vanishing step, the new connected scalar-constancy bridge, and
  the existing conditional constant-sectional-curvature theorem.

The final theorem keeps the scalar differentiability hypothesis explicit and
uses `hR0 : exists x0, g.scalarAt x0 = R0` only to name the global scalar value.
It no longer requires a global scalar-constancy hypothesis.

## Verification

The requested build completed successfully:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm
Build completed successfully (2928 jobs).
```

Additional checks:

```text
git diff --check
```

completed cleanly, and a source-file scan of the touched Lean files found no
forbidden proof-gap constructs.

## Outlook

- Item 4: introduce and stabilize the `PositiveConstantCurvatureSpaceForm3`
  interface on top of `HasConstantSectionalCurvature3`.
- Item 5: use that interface to state and prove the conditional sphere theorem
  from the frontier survey.
