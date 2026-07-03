# M4-prep-12 blocked

## Result

Proof-bearing progress was added and committed in
`Poincare/Global/ScalarVariation.lean`.

Verified commits for this slice:

- `1d7eb7f1` — `Add moving Gram coefficient derivative`
- `e4633ec8` — `Add moving inverse Gram contraction`
- `fd832a01` — `Add moving K-slot derivative bridges`
- `c45e518b` — `Add connection K-slot curvature bridges`
- `16137a28` — `Collapse connection slot corrections to curvature action`

The requested moving-K coefficient contraction and both K-slot product-rule
bridges are now proved.  The connection-value instantiations are also proved,
including the antisymmetrized left/right connection-slot formulas and their
combined cancellation to the curvature-action side:

```lean
tensor2_connection_slot_antisymm_corrections_eq_curvatureAction
```

This lemma shows that the two K-slot bridge families, after subtracting the
two first-order `covTensor2DerivAt` correction blocks from
`covTensor2SecondDerivAt_antisymm_expansion`, collapse exactly to

```lean
covTensor2SecondDerivCurvatureActionAt g h x u v p q
```

Verification after the last Lean edit:

```text
lake build Poincare.Global.ScalarVariation
```

succeeded, with pre-existing warnings only.  Additional hygiene checks passed:
no forbidden proof placeholders in `Poincare/Global/ScalarVariation.lean`, and
`git diff --check` was clean before each commit.

## Remaining blocker

The algebraic K-slot side is closed.  The remaining missing bridge is the raw
outer derivative expansion for the first term in

```lean
covTensor2SecondDerivAt_antisymm_expansion
```

At the moving base point `y`, `covTensor2DerivAt g h y
(extend E v y) (extend E p y) (extend E q y)` internally differentiates scalar
entries built from canonical extensions based at `y`, not from the fixed
anchor `x`:

```lean
extend E (extend E p y)
extend E (extend E q y)
```

The available Schwarz cancellation applies to the fixed `x`-anchored scalar
entry

```lean
fun z => h z (extend E p z) (extend E q z)
```

so the final tensor Ricci identity still needs an extension-independence or
two-moving-slot derivative bridge of the following shape:

```lean
extDerivFun
  (fun y =>
    covTensor2DerivAt g h y
      (extend E v y) (extend E p y) (extend E q y)) x u
=
  extDerivFun
    (fun y =>
      extDerivFun
        (fun z => h z (extend E p z) (extend E q z))
        y (extend E v y)) x u
  - extDerivFun
      (fun y =>
        h y
          (g.leviCivita (extend E p) y (extend E v y))
          (extend E q y)) x u
  - extDerivFun
      (fun y =>
        h y (extend E p y)
          (g.leviCivita (extend E q) y (extend E v y))) x u
```

or an equivalent tensoriality theorem saying that `covTensor2DerivAt` is
independent of the chosen differentiable extensions of its tensor slots.

Once that bridge is available, the remaining assembly should be direct:

1. Use `covTensor2SecondDerivAt_antisymm_expansion`.
2. Rewrite the raw derivative difference with the bridge above.
3. Apply `covTensor2SecondDerivAt_pure_schwarz_cancel` to the fixed scalar
   second-derivative block.
4. Apply
   `tensor2_connection_slot_antisymm_corrections_eq_curvatureAction`.
5. Specialize the resulting tensor Ricci identity to `ricciVariationField g`
   using the existing Ricci-field bilinearity and differentiability lemmas.
