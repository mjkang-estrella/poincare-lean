# M3-predicates-51 progress report

## Summary

This task landed a verified group-3 orientation bridge for the correction side
of the cyclic residue equation.

New theorem surface in `Poincare/Global/ScalarVariation.lean`:

```lean
closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms
```

The theorem expands one `closedCurvatureCovDerivAtCorrectionAt` block through
the defining curvature formula into the same
`closedIteratedConnectionEntryFieldAt` and
`closedBracketConnectionEntryFieldAt` vocabulary used by
`closedCurvatureDefExpansionResidueAt`.  The proof is definitional plus
bilinear-pairing cleanup:

```lean
simp only [closedCurvatureCovDerivAtCorrectionAt,
  CovariantDerivative.curvatureOp_apply,
  closedIteratedConnectionEntryFieldAt,
  closedBracketConnectionEntryFieldAt,
  extend_apply_self,
  map_sub,
  ContinuousLinearMap.sub_apply]
```

This confirms the correction orientation: no sign or slot mismatch was found
in the four correction terms after unfolding.

## Remaining exact goal state

The primary cyclic residue cancellation is still open:

```lean
closedCurvatureDefExpansionResidueAt g y v u w z q
  + closedCurvatureDefExpansionResidueAt g y u w v z q
  + closedCurvatureDefExpansionResidueAt g y w v u z q
  - (closedCurvatureCovDerivAtCorrectionAt g y v u w z q
    + closedCurvatureCovDerivAtCorrectionAt g y u w v z q
    + closedCurvatureCovDerivAtCorrectionAt g y w v u z q) = 0
```

Equivalently, the next useful theorem shape is:

```lean
theorem closedCurvatureDefExpansionResidueAt_cyclic_eq_correction_cyclic
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (u v w z q : TM x) :
    closedCurvatureDefExpansionResidueAt g x v u w z q
      + closedCurvatureDefExpansionResidueAt g x u w v z q
      + closedCurvatureDefExpansionResidueAt g x w v u z q =
        closedCurvatureCovDerivAtCorrectionAt g x v u w z q
          + closedCurvatureCovDerivAtCorrectionAt g x u w v z q
          + closedCurvatureCovDerivAtCorrectionAt g x w v u z q
```

After rewriting the correction side with
`closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms`, Lean still
has the cyclic raw derivative block from the residue side.  Written without
abbreviation, that derivative block is:

```lean
- extDerivFun
    (fun y : M =>
      closedBracketConnectionEntryFieldAt g u w z y (extend E q y)) x v
  - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u w z q) x v
  + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w u z q) x v
- extDerivFun
    (fun y : M =>
      closedBracketConnectionEntryFieldAt g w v z y (extend E q y)) x u
  - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w v z q) x u
  + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v w z q) x u
- extDerivFun
    (fun y : M =>
      closedBracketConnectionEntryFieldAt g v u z y (extend E q y)) x w
  - extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v u z q) x w
  + extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u v z q) x w
```

The next missing proof-bearing bridge appears to be the product-rule/metric
compatibility expansion for this cyclic bracket-plus-output derivative block,
followed by torsion-free bracket alignment and algebraic cancellation against
the new correction expansion.  The already-landed output value wrappers are
not enough by themselves; the surviving terms are derivative terms, not a
detected correction-orientation mismatch.

## Downstream status

Because the residue atom remains open, the following were not assembled in
this task:

```lean
eventually_closed_cyclic_second_bianchi_of_inner_sum
hMiddle
eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
ClosedContractedBianchiAt.of_closed_trace_contraction_canonical
satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
```

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
