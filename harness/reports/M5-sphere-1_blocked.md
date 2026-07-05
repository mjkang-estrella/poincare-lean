# M5-sphere-1 blocked: global Schur bridge

## Verified progress

- Commit `fe236739` defines the non-vacuous global predicate
  `ClosedSmoothRiemannianMetric.IsEinstein3`.
- The same commit proves
  `isEinstein3_iff_forall_tracelessRicciNormSqAt_eq_zero`, plus the forward
  and reverse convenience theorems.
- `lake build Poincare.Global.RicciNorm` completed successfully for that
  commit.

## Blocker

The requested second deliverable,

```lean
IsEinstein3 g -> scalarAt is constant on a closed connected 3-manifold
```

is not currently derivable from the exposed closed-manifold API without adding
several nontrivial bridge lemmas.

Existing ingredients are present but stop short of the global Schur theorem:

- `ClosedContractedBianchiOneFormAt` and
  `eventually_closedContractedBianchiOneFormAt_canonical` expose the closed
  one-form Bianchi identity `div Ric = (1 / 2) dR`.
- `schur_fderiv_coordScalar_eq_zero_of_einstein_field` proves the model-space
  local Schur step, but its hypothesis is a field-level coordinate Einstein
  identity on a model neighborhood.
- `closedCurvatureFourLinearAt_spaceForm_coeff` proves the 3D pointwise
  space-form curvature collapse once `Ric = lam * g` and `R = 3 * lam` are
  available at the point.

The missing closed bridge consists of:

1. A variable-scalar metric divergence rule:

   ```lean
   tensorDivergenceOneFormAt g
     (fun y v w => f y * g.inner y v w) x w =
       extDerivFun f x w
   ```

   under an honest differentiability hypothesis on `f`.

2. A way to apply that rule to `f = fun y => g.scalarAt y / 3`.
   The current closed scalar regularity lemmas are not a general
   differentiability theorem for `scalarAt`; the available scalar regularity
   surfaces are tied to more specialized hypotheses.

3. Either a direct closed proof that
   `IsEinstein3 g` gives `div Ric = (1 / 3) dR`, or a chart/blended-metric
   transport theorem that turns global `IsEinstein3` into the model-space
   field-level hypothesis used by
   `schur_fderiv_coordScalar_eq_zero_of_einstein_field`.

4. A global constant bridge:

   ```lean
   (forall x w, extDerivFun (fun y => g.scalarAt y) x w = 0)
     -> forall x y, g.scalarAt x = g.scalarAt y
   ```

   for connected closed manifolds. Mathlib has locally-constant and
   preconnected-space machinery, but this repository does not yet expose the
   chart representative bridge from vanishing `extDerivFun` everywhere to
   `IsLocallyConstant`.

Because item 2 is blocked, the requested unconditional item 3 is also blocked:
`closedCurvatureFourLinearAt_spaceForm_coeff` can collapse the curvature
pointwise from Einstein plus the scalar trace relation, but the task asks to
derive the constant scalar input from Schur rather than assume it.

## Recommended next interfaces

Add and prove these in the closed layer before retrying the global theorem:

- `covTensor2DerivAt_scalar_metric`
- `tensorDivergenceOneFormAt_scalar_metric`
- `extDerivFun_scalarAt_eq_zero_of_isEinstein3`
- `scalarAt_constant_of_extDerivFun_eq_zero_connected`
- `HasSpaceFormCurvature3` and `HasConstantSectionalCurvature3`, with
  theorem-backed falsifier lemmas and a theorem
  `hasConstantSectionalCurvature3_of_isEinstein3_of_scalarAt_eq_six`

With those bridges, the intended chain is:

```lean
tracelessRicciNormSqAt = 0 everywhere
  -> IsEinstein3 g
  -> extDerivFun scalarAt = 0 everywhere
  -> scalarAt constant
  -> HasConstantSectionalCurvature3 g (R0 / 6)
```
