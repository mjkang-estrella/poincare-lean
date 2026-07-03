# M4-prep-10 blocked

## Result

Partial verified progress was landed in `Poincare/Global/ScalarVariation.lean`.

New proved helper:

- `closedChristoffel_antisymm_deriv_eq_curvature`

This is the closed analogue of the model's
`christoffel_antisymm_deriv_eq_curvature` at the vector-field level in
canonical-extension slots:

```lean
g.leviCivita (fun y => g.leviCivita (extend E p) y (extend E v y)) x u
  - g.leviCivita (fun y => g.leviCivita (extend E p) y (extend E u y)) x v
= CovariantDerivative.curvatureOp g.leviCivita
    (extend E u) (extend E v) (extend E p) x
```

The proof is a direct read of `CovariantDerivative.curvatureOp_apply` plus
`mlieBracket_extend_extend_apply_self`, so the bracket term vanishes at the
base point.

Verification:

- `lake build Poincare.Global.ScalarVariation` succeeded after the code slice.

## Blocker

The requested first slice cannot be honestly proved from the stated
`CovTensor2ExtContMDiffAt h x 2` hypothesis alone.

The missing bridge is a generic moving-slot product rule for an arbitrary raw
field `h`:

```lean
fun y => h y
  (g.leviCivita (extend E p) y (extend E v y))
  (extend E q y)

fun y => h y
  (extend E p y)
  (g.leviCivita (extend E q) y (extend E v y))
```

`CovTensor2ExtContMDiffAt h x 2` only says that fixed canonical scalar entries

```lean
fun y => h y (extend E p y) (extend E q y)
```

are `C²`.  It does not package tensor-slot bilinearity, and it does not expose a
field-valued derivative rule for evaluating `h` on an arbitrary moving tangent
field.  Without bilinearity the intended product rule is false for a raw
function of the tangent vector slots: differentiating a moving vector argument
would involve the actual derivative of `h` in that vector argument, not just
`h x` applied to the derivative of the vector field.

The named existing bridge pattern does not remove this gap:

- `DeltaGammaEntryDerivativeBridgeAt` differentiates
  `g.inner (deltaGammaField) (extend q)` by metric compatibility.
- `ClosedCurvatureEntryDerivativeBridgeAt` differentiates
  `g.inner (curvatureField) (extend q)` by the same metric compatibility route.

Those proofs are not generic tensor-slot product rules for an arbitrary `h`;
they use the special product rule supplied by `g.leviCivita_metricCompatibleAt`.

## Needed next slice

Add a non-vacuous moving-slot tensor product-rule interface, or prove the
finite-frame version directly.  A useful target shape is:

```lean
extDerivFun (fun y => h y (K y) (extend E q y)) x u =
  covTensor2DerivAt g h x u (K x) q
    + h x (g.leviCivita K x u) q
    + h x (K x) (g.leviCivita (extend E q) x u)
```

and the right-slot analogue:

```lean
extDerivFun (fun y => h y (extend E p y) (K y)) x u =
  covTensor2DerivAt g h x u p (K x)
    + h x (g.leviCivita (extend E p) x u) (K x)
    + h x p (g.leviCivita K x u)
```

This should require at least:

- `Tensor2AddLeft h`, `Tensor2SMulLeft h`,
  `Tensor2AddRight h`, and `Tensor2SMulRight h`,
- `CovTensor2ExtContMDiffAt h x 2`,
- `MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% K) x`,
- a finite-frame proof that differentiating the scalar expansion of
  `h y (K y) (extend E q y)` agrees with the covariant expression above.

After those two bridges exist, instantiate them with

```lean
K y = g.leviCivita (extend E p) y (extend E v y)
K y = g.leviCivita (extend E q) y (extend E v y)
```

then use the landed
`closedChristoffel_antisymm_deriv_eq_curvature`, together with
`covTensor2SecondDerivAt_antisymm_expansion` and
`covTensor2SecondDerivAt_pure_schwarz_cancel`, to finish the tensor Ricci
identity and then the `ricciVariationField g` specialization.
