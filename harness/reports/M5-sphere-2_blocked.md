# M5-sphere-2 blocked: Schur bridge to constant sectional curvature

## Verified progress

- Commit `e378119b` proves
  `covTensor2DerivAt_scalar_metric`: the covariant derivative of
  `f * g` is `(df)(v) * g(p,q)` under a pointwise differentiability
  hypothesis on `f`.
- Commit `e326462a` proves
  `tensorDivergenceOneFormAt_scalar_metric`: the divergence of
  `f * g` is `df`, using the raised-dual-basis trace reconstruction.
- Commit `cd4621f7` proves
  `extDerivFun_scalarAt_eq_zero_of_isEinstein3`, with the scalar
  differentiability hypothesis explicit.  This is the Schur coefficient step:
  Einstein plus closed contracted Bianchi gives `(1 / 3) dR = (1 / 2) dR`.
- Commit `4d405740` adds the non-vacuous predicate
  `HasConstantSectionalCurvature3`, a direct mismatch falsifier, and the
  conditional space-form theorems:
  `hasConstantSectionalCurvature3_of_isEinstein3_of_scalar_const` and
  `hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_of_scalar_const`.

## Verification

The requested build completed successfully:

```text
lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
Build completed successfully (2938 jobs).
```

No forbidden proof-gap constructs were introduced in the new Lean diffs.

## Remaining blocker

The full requested chain is not yet provable as stated because item 4 is still
missing: there is no exposed closed-manifold bridge from

```lean
forall x w, extDerivFun (fun y => g.scalarAt y) x w = 0
```

to global constancy of `scalarAt` on a connected closed manifold.

The repository has the needed local raw ingredients:

- `extDerivFun_apply_chart` and `extDerivFun_apply_fixed_chart`
  identify `extDerivFun` with chart-representative `fderiv`.
- Mathlib has `isLocallyConstant_of_fderiv_eq_zero` and
  `IsLocallyConstant.apply_eq_of_preconnectedSpace`.

What remains is a reusable manifold lemma packaging the chart-local argument:
zero `extDerivFun` everywhere plus differentiability of the scalar function
implies `IsLocallyConstant`, then connectedness implies constancy.

## Outlook

Recommended next interface:

```lean
isLocallyConstant_of_extDerivFun_eq_zero
```

with hypotheses roughly:

```lean
(hf : forall x, MDifferentiableAt I _ f x) ->
(hzero : forall x w, extDerivFun f x w = 0) ->
IsLocallyConstant f
```

Then specialize it to `f = fun y => g.scalarAt y`, combine with connectedness,
and remove the explicit scalar-constant hypothesis from the current conditional
space-form theorem.  After that, the desired unconditional theorem should be a
short composition:

```lean
tracelessRicciNormSqAt = 0 everywhere
  -> IsEinstein3
  -> extDerivFun scalarAt = 0 everywhere
  -> scalarAt constant
  -> HasConstantSectionalCurvature3 g (R0 / 6)
```
