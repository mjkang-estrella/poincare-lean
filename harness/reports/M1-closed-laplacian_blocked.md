# M1-closed-laplacian blocked report

## Hessian symmetry

The new `Poincare.Global.Laplacian` module defines the closed-manifold gradient,
covariant Hessian, and scalar Laplacian, and proves the metric-duality,
linearity, and constant-function sanity checks.

The classical Hessian symmetry theorem is not included yet. The available
global API has torsion-freeness of `g.leviCivita`, but the proof also needs a
manifold-level bridge from smoothness of `f` to differentiability of
`g.gradient f`, plus the second-derivative commutation identity for the scalar
field terms appearing in
`X(Y f) - Y(X f) - [X,Y] f`.

Those pieces are part of the same regularity chain tracked by ledger task
`M1-lc-regularity`. Once that task discharges gradient-field regularity and the
needed scalar second-derivative commutator at the closed-manifold level, the
expected statement is:

```lean
g.hessianAt f x v w = g.hessianAt f x w v
```

under the corresponding smoothness hypotheses on `f`.
