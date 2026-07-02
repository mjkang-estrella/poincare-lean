# M3-predicates-44 blocked report

## Summary

I added a verified scalar-entry expansion layer for the closed cyclic second
Bianchi target in `Poincare/Global/ScalarVariation.lean`.

New theorem surface:

```lean
closedCurvatureEntryDerivAt
closedCurvatureCovDerivAtCorrectionAt
closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
closedCurvatureCovDerivAt_cyclic_inner_expansion
```

This lands the first expansion step of the requested route: after pairing with
an arbitrary output vector `q`, each `closedCurvatureCovDerivAt` term is
rewritten via the canonical curvature-entry bridge as the flat exterior
derivative of a scalar curvature entry minus the four Christoffel-slot
corrections.

The cyclic scalar expansion now has the exact form

```lean
g.inner x (closedCurvatureCovDerivAt g x v u w z) q
  + g.inner x (closedCurvatureCovDerivAt g x u w v z) q
  + g.inner x (closedCurvatureCovDerivAt g x w v u z) q
=
  closedCurvatureEntryDerivAt g x v u w z q
    + closedCurvatureEntryDerivAt g x u w v z q
    + closedCurvatureEntryDerivAt g x w v u z q
    - (closedCurvatureCovDerivAtCorrectionAt g x v u w z q
      + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
      + closedCurvatureCovDerivAtCorrectionAt g x w v u z q)
```

## Remaining exact goal state

The requested neighborhood theorem is still not proved:

```lean
theorem eventually_closed_cyclic_second_bianchi
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    ∀ᶠ y in nhds x, ∀ u v w z : TM y,
      closedCurvatureCovDerivAt g y v u w z
        + closedCurvatureCovDerivAt g y u w v z
        + closedCurvatureCovDerivAt g y w v u z = 0
```

The immediate missing closed atoms are:

1. A closed analogue of the model `fderiv_coordCurvatureOp_family` expansion
   for `closedCurvatureEntryDerivAt`, exposing the second connection
   derivatives and the `Γ * ∂Γ` terms.
2. The cyclic Schwarz cancellation for those exposed second connection
   derivatives, corresponding to the `rw [(hsymΓ ...)]` group in
   `coord_second_bianchi`.
3. The cyclic cancellation of the remaining `Γ * ∂Γ` terms and the four
   Christoffel-slot correction blocks.

The model proof read for this task is:

```lean
coord_second_bianchi
```

It closes only after rewriting through `fderiv_coordCurvatureOp_family`,
unfolding `coordCurvatureOp`, applying Christoffel symmetry and mixed-second
derivative symmetry, then finishing by `abel`.  The closed file now has the
canonical curvature-entry bridge and the cyclic scalar expansion, but not yet
the closed theorem that exposes the corresponding `coordCurvatureOp`-level
connection-derivative terms.

## Handoff notes

There were no `M3-predicates-43_done.md` or
`M3-predicates-43_blocked.md` files in this checkout's `harness/reports/`.
The available latest handoff context was `M3-predicates-41_blocked.md` plus
the source state already containing the canonical curvature-entry bridge and
the Ricci derivative expansion.

## Verification

Source-local check after the edit:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with existing warnings only.

Required task build:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, with existing warnings only, ending with:

```text
Build completed successfully (2805 jobs).
```

Additional checks:

```bash
git diff --check
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ScalarVariation.lean
```

Results: whitespace check succeeded; the edited Lean file has no forbidden
placeholder matches.
