# M3-predicates-50 progress report

## Summary

This task landed verified group-1 wiring in
`Poincare/Global/ScalarVariation.lean`.

New theorem surface:

```lean
closedConnectionEntryOutputConnectionFieldAt
closedConnectionEntry_extDerivFun_extend_eq_iterated_add_output_eventually
closedConnectionEntryOutputConnection_mdiffAt
closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output
closedCurvatureDefExpansionAt_eq_secondDirectional_residue
closedCurvatureDefExpansionResidueAt
closedCurvatureDefExpansionAt_eq_secondDirectional_add_residue
closedCurvatureDefExpansionAt_cyclic_eq_residue_cyclic
closedCurvatureDefExpansionAt_cyclic_sub_corrections_eq_residue_sub_corrections
```

The main new bridge is
`closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output`.
It connects the `covTensor2DerivAt`-shaped iterated connection terms in
`closedCurvatureDefExpansionAt` to the raw
`closedSecondDirectionalEntryAt` terms used by
`closedConnectionEntry_mixed_second_cyclic_cancel`.

The group-1 cyclic cancellation is now packaged as
`closedCurvatureDefExpansionAt_cyclic_eq_residue_cyclic`: after rewriting
each curvature defining expansion through the corrected second directional
bridge, the raw mixed-second scalar terms cancel by the existing Schwarz
lemma, leaving only the named residue blocks.

## Remaining exact goal state

The full displayed cancellation from `M3-predicates-49` now reduces by
`closedCurvatureDefExpansionAt_cyclic_sub_corrections_eq_residue_sub_corrections`
to the following exact group-3 residue:

```lean
closedCurvatureDefExpansionResidueAt g y v u w z q
  + closedCurvatureDefExpansionResidueAt g y u w v z q
  + closedCurvatureDefExpansionResidueAt g y w v u z q
  - (closedCurvatureCovDerivAtCorrectionAt g y v u w z q
    + closedCurvatureCovDerivAtCorrectionAt g y u w v z q
    + closedCurvatureCovDerivAtCorrectionAt g y w v u z q) = 0
```

Unfolding the named residue, one expansion contributes:

```lean
- extDerivFun
    (fun y : M =>
      closedBracketConnectionEntryFieldAt g a u z y
        (extend E q y)) x v
  - extDerivFun
    (closedConnectionEntryOutputConnectionFieldAt g a u z q) x v
  + extDerivFun
    (closedConnectionEntryOutputConnectionFieldAt g u a z q) x v
  + closedIteratedConnectionEntryFieldAt g u z x
    (g.leviCivita (extend E a) x v) q
  - closedIteratedConnectionEntryFieldAt g a z x
    (g.leviCivita (extend E u) x v) q
  + closedConnectionEntryOutputConnectionFieldAt g
    (g.leviCivita (extend E a) x v) u z q x
  - closedConnectionEntryOutputConnectionFieldAt g
    (g.leviCivita (extend E u) x v) a z q x
```

Next step: prove that the cyclic sum of these three residue blocks is exactly
the cyclic `closedCurvatureCovDerivAtCorrectionAt` block, using the existing
torsion-free bracket alignment lemmas and the remaining metric/output-slot
bookkeeping.

## Verification

Verified after the edit:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: both commands succeeded, with existing warnings only. The required
build ended with:

```text
Build completed successfully (2806 jobs).
```
