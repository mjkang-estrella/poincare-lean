# M3-predicates-53 blocked report

## Summary

This slice proved the cheap route-1 atom and strengthened it to the form
actually needed by the differentiated bracket-entry fields:

```lean
mfderiv_extChartAt_extend_apply
chartTransportedLeviCivitaSection_extend_apply_chart
mlieBracket_extend_extend_apply_self
mlieBracket_extend_extend_eventually_eq_zero
closedBracketConnectionEntryFieldAt_extend_eventually_eq_zero
closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero
closedBracketConnectionEntryFieldAt_apply_self_eq_zero
```

The important correction to the previous concern is that the bracket does
vanish on an anchor-chart neighborhood, not merely at the anchor.  Thus the
differentiated bracket-entry fields in the cyclic residue can legitimately be
rewritten to zero by eventual equality and `CovariantDerivative.extDerivFun_congr`.

However, route 1 alone still does not eliminate the full nine-term block.  It
kills the three bracket derivative terms and all value-level bracket correction
terms, but the output-connection derivative pair terms remain and require a
route-2/product-rule bridge.

## Probe theorem

The theorem shape probed was:

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

After rewriting the three corrections with
`closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms`, unfolding
`closedCurvatureDefExpansionResidueAt`, rewriting the three bracket derivative
terms with `closedBracketConnectionEntryFieldAt_extend_extDerivFun_eq_zero`,
and simplifying all value-level bracket terms with
`closedBracketConnectionEntryFieldAt_apply_self_eq_zero`, Lean leaves this
residual goal:

```lean
goal: -(extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u w z q) x) v
    + (extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w u z q) x) v
    + closedIteratedConnectionEntryFieldAt g w z x ((g.leviCivita (extend E u) x) v) q
    - closedIteratedConnectionEntryFieldAt g u z x ((g.leviCivita (extend E w) x) v) q
    + closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E u) x) v) w z q x
    - closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E w) x) v) u z q x
    - (extDerivFun (closedConnectionEntryOutputConnectionFieldAt g w v z q) x) u
    + (extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v w z q) x) u
    + closedIteratedConnectionEntryFieldAt g v z x ((g.leviCivita (extend E w) x) u) q
    - closedIteratedConnectionEntryFieldAt g w z x ((g.leviCivita (extend E v) x) u) q
    + closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E w) x) u) v z q x
    - closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E v) x) u) w z q x
    - (extDerivFun (closedConnectionEntryOutputConnectionFieldAt g v u z q) x) w
    + (extDerivFun (closedConnectionEntryOutputConnectionFieldAt g u v z q) x) w
    + closedIteratedConnectionEntryFieldAt g u z x ((g.leviCivita (extend E v) x) w) q
    - closedIteratedConnectionEntryFieldAt g v z x ((g.leviCivita (extend E u) x) w) q
    + closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E v) x) w) u z q x
    - closedConnectionEntryOutputConnectionFieldAt g ((g.leviCivita (extend E u) x) w) v z q x
  =
    closedIteratedConnectionEntryFieldAt g w z x ((g.leviCivita (extend E u) x) v) q
    - closedIteratedConnectionEntryFieldAt g u z x ((g.leviCivita (extend E w) x) v) q
    + closedIteratedConnectionEntryFieldAt g v z x ((g.leviCivita (extend E w) x) u) q
    - closedIteratedConnectionEntryFieldAt g w z x ((g.leviCivita (extend E v) x) u) q
    + closedIteratedConnectionEntryFieldAt g u z x ((g.leviCivita (extend E v) x) w) q
    - closedIteratedConnectionEntryFieldAt g v z x ((g.leviCivita (extend E u) x) w) q
    - closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E u) x) v) z x w q
    + closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E w) x) v) z x u q
    + closedIteratedConnectionEntryFieldAt g w ((g.leviCivita (extend E z) x) v) x u q
    - closedIteratedConnectionEntryFieldAt g u ((g.leviCivita (extend E z) x) v) x w q
    + closedIteratedConnectionEntryFieldAt g w z x u ((g.leviCivita (extend E q) x) v)
    - closedIteratedConnectionEntryFieldAt g u z x w ((g.leviCivita (extend E q) x) v)
    - closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E w) x) u) z x v q
    + closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E v) x) u) z x w q
    + closedIteratedConnectionEntryFieldAt g v ((g.leviCivita (extend E z) x) u) x w q
    - closedIteratedConnectionEntryFieldAt g w ((g.leviCivita (extend E z) x) u) x v q
    + closedIteratedConnectionEntryFieldAt g v z x w ((g.leviCivita (extend E q) x) u)
    - closedIteratedConnectionEntryFieldAt g w z x v ((g.leviCivita (extend E q) x) u)
    - closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E v) x) w) z x u q
    + closedIteratedConnectionEntryFieldAt g ((g.leviCivita (extend E u) x) w) z x v q
    + closedIteratedConnectionEntryFieldAt g u ((g.leviCivita (extend E z) x) w) x v q
    - closedIteratedConnectionEntryFieldAt g v ((g.leviCivita (extend E z) x) w) x u q
    + closedIteratedConnectionEntryFieldAt g u z x v ((g.leviCivita (extend E q) x) w)
    - closedIteratedConnectionEntryFieldAt g v z x u ((g.leviCivita (extend E q) x) w)
```

I also expanded `closedConnectionEntry_mixed_second_cyclic_cancel` through
`closedSecondDirectionalEntryAt_connectionEntry_eq_iterated_add_output` and
`closedIteratedConnectionEntry_extDerivFun_eq`.  That accounts for the six
output-connection derivative terms, but it leaves `covTensor2DerivAt` atoms.
The missing bridge is the next route-2 atom: rewrite those cyclic
`covTensor2DerivAt (closedIteratedConnectionEntryFieldAt ...)` terms into the
remaining first-slot, middle-slot, and output-slot correction terms above.

## Next step

Do not keep pushing route 1.  The bracket-vanishing part is complete and
verified.  The next proof-bearing step is a route-2 bridge mirroring the
`coord_second_bianchi` product-rule replay:

1. Expand the six output-connection derivative terms using the existing
   corrected second-directional cancellation.
2. Package the resulting cyclic `covTensor2DerivAt` block for
   `closedIteratedConnectionEntryFieldAt`.
3. Prove that block equals the remaining correction-side iterated terms.
4. Then `ring_nf`/`abel` should close
   `closedCurvatureDefExpansionResidueAt_cyclic_eq_correction_cyclic`.

## Verification

After adding the route-1 lemmas:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, existing warnings only.
