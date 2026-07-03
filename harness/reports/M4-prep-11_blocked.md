# M4-prep-11 blocked

## Result

Partial proof-bearing progress was added in
`Poincare/Global/ScalarVariation.lean`.

New finite-frame expansion helpers:

- `tensor2_moving_left_eventually_eq_sum_gram_inv`
- `tensor2_moving_right_eventually_eq_sum_gram_inv`

These are the non-vacuous front half of the requested K-slot bridge.  For any
pointwise bilinear raw `(0,2)` tensor, they rewrite the moving-slot scalar
entries near `x` as finite sums over the anchored Gram frame:

```lean
fun y => h y (K y) (extend E q y)
```

and

```lean
fun y => h y (extend E p y) (K y)
```

become sums whose coefficients are

```lean
(gramMatrix g x y)⁻¹ i j * g.inner y (K y) (gramFrame x y j)
```

and whose tensor entries are fixed anchored-frame entries.  This matches the
finite-frame expansion requested in the task and uses the existing
`gramFrameBasis` machinery.

## Remaining blocker

The full target bridge still needs a proved derivative-identification layer:

```lean
extDerivFun (fun y => h y (K y) (extend E q y)) x u =
  covTensor2DerivAt g h x u (K x) q
    + h x (g.leviCivita K x u) q
    + h x (K x) (g.leviCivita (extend E q) x u)
```

and the right-slot analogue.

The added expansions reduce those goals to differentiating finite sums of
products.  What is still missing is the reusable closed lemma that differentiates
the coefficient block

```lean
fun y => (gramMatrix g x y)⁻¹ i j *
  g.inner y (K y) (gramFrame x y j)
```

and contracts the result back to the covariant derivative value
`g.leviCivita K x u`, with the inverse-Gram derivative terms canceling the
anchored-frame Christoffel corrections.  This is analogous to the existing
`gram_inv_deriv_contraction_eq_leviCivita_corrections`, but with an arbitrary
moving field `K` in place of the fixed trace-contraction slots.

Until that coefficient-derivative contraction is present, the two K-slot product
rules cannot be honestly closed, so the tensor Ricci identity and
`ricciVariationField g` specialization remain unproved in this slice.
