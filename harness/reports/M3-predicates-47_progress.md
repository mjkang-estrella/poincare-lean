# M3-predicates-47 progress report

## Summary

This task landed verified infrastructure for the cyclic second-Bianchi
endgame in `Poincare/Global/ScalarVariation.lean`, but did not complete the
full cyclic cancellation.

New theorem surface:

```lean
curvatureOp_congr_fst_of_value_eq
curvatureOp_congr_snd_of_value_eq
closedCurvatureCovDerivAt_eq_field_slots
closed_cyclic_second_bianchi_at_of_inner_sum
eventually_closed_cyclic_second_bianchi_of_inner_sum
closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion
```

The main new route theorem is
`closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion`, which combines the
predicates-44 scalar-paired cyclic expansion with `closedCurvature_koszul`.
It rewrites the cyclic scalar pairing into three
`closedCurvatureDefExpansionAt` terms minus the cyclic correction block.

The new field-slot bridge
`closedCurvatureCovDerivAt_eq_field_slots` replaces the constant extensions of
the connection-slot values in `closedCurvatureCovDerivAt` by the actual
fields `y ↦ ∇_{X y} U`, etc., using curvature tensoriality.  This is intended
to make the remaining abstract second-Bianchi cancellation closer to the
standard covariant-derivative-of-curvature expression.

The new adapter
`eventually_closed_cyclic_second_bianchi_of_inner_sum` reduces the exact
vector-valued neighborhood target to a scalar-paired cyclic cancellation for
all output vectors.

## Remaining exact goal state

The requested theorem is still open:

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

Equivalently, by the new adapter it is enough to prove:

```lean
∀ᶠ y in nhds x, ∀ u v w z q : TM y,
  g.inner y (closedCurvatureCovDerivAt g y v u w z) q
    + g.inner y (closedCurvatureCovDerivAt g y u w v z) q
    + g.inner y (closedCurvatureCovDerivAt g y w v u z) q = 0
```

After `closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion`, the remaining
unproved cancellation is exactly:

```lean
closedCurvatureDefExpansionAt g y v u w z q
  + closedCurvatureDefExpansionAt g y u w v z q
  + closedCurvatureDefExpansionAt g y w v u z q
  - (closedCurvatureCovDerivAtCorrectionAt g y v u w z q
    + closedCurvatureCovDerivAtCorrectionAt g y u w v z q
    + closedCurvatureCovDerivAtCorrectionAt g y w v u z q) = 0
```

The open cancellation groups remain:

1. mixed second-connection derivative cancellation,
2. torsion-free alignment of the `Γ · ∂Γ`/field-slot terms,
3. cyclic cancellation of the curvature correction block.

## Verification

Verified after the edit:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: both commands succeeded, with existing warnings only.
