# M3-predicates-49 progress report

## Summary

This task landed a verified group-2 torsion-free alignment unit in
`Poincare/Global/ScalarVariation.lean`.

New theorem surface:

```lean
closedBracketConnectionEntryFieldAt_eq_connectionEntry_sub
closedBracketConnectionEntryFieldAt_outputConnection_eq_connectionEntry_sub
closedBracketConnectionEntryFieldAt_cyclic_outputConnection_eq_connectionEntry_sub
```

The main new rewrite is
`closedBracketConnectionEntryFieldAt_eq_connectionEntry_sub`.  It uses
`g.leviCivita_torsionFreeAt` on canonical extensions to replace the bracket
connection entry `g(∇_[a,u] w, q)` by the difference of the two connection-slot
products coming from `∇_a u - ∇_u a`.

The output-slot specialization and cyclic wrapper package the exact
`g.leviCivita (extend E q) x _` bracket block that appears in the cyclic
`closedCurvatureDefExpansionAt` bookkeeping.  This is the group-2 minimum
needed before the later `ring`/`abel` cancellation can pair those terms with
the remaining first-order connection products.

## Remaining exact goal state

The full requested neighborhood theorem is still open:

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

By `eventually_closed_cyclic_second_bianchi_of_inner_sum`, the remaining scalar
obligation is:

```lean
∀ᶠ y in nhds x, ∀ u v w z q : TM y,
  g.inner y (closedCurvatureCovDerivAt g y v u w z) q
    + g.inner y (closedCurvatureCovDerivAt g y u w v z) q
    + g.inner y (closedCurvatureCovDerivAt g y w v u z) q = 0
```

After `closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion`, the displayed
unproved cancellation remains exactly:

```lean
closedCurvatureDefExpansionAt g y v u w z q
  + closedCurvatureDefExpansionAt g y u w v z q
  + closedCurvatureDefExpansionAt g y w v u z q
  - (closedCurvatureCovDerivAtCorrectionAt g y v u w z q
    + closedCurvatureCovDerivAtCorrectionAt g y u w v z q
    + closedCurvatureCovDerivAtCorrectionAt g y w v u z q) = 0
```

The next proof step should wire the group-1 raw mixed-second derivative
cancellation through the `covTensor2DerivAt` terms in
`closedCurvatureDefExpansionAt`, then apply the new cyclic bracket-output
alignment to the group-2 block.  The metric/bracket correction group-3 block is
still not proved.

## Verification

Verified after the edit:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: both commands succeeded, with existing warnings only.  The required
build ended with:

```text
Build completed successfully (2806 jobs).
```
