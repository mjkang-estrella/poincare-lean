# M3-predicates-52 blocked report

## Summary

I did not close the cyclic second-Bianchi/Hamilton chain in this slice.

The useful verified observation is that the neighborhood consumer already
re-anchors pointwise.  In
`eventually_closed_cyclic_second_bianchi_of_inner_sum`, the filter proof is:

```lean
filter_upwards [hScalar] with y hy
exact closed_cyclic_second_bianchi_at_of_inner_sum (g := g) (x := y) hy
```

Thus the `∀ᶠ y in nhds x` theorem only needs the scalar cyclic identity at
each current point `y`, with tangent vectors in `TM y`.  The task's
re-anchoring idea is valid at the quantifier level.

## Exact surviving derivative block

From `harness/reports/M3-predicates-51_progress.md`, the raw cyclic
bracket/output derivative block is:

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

## What I tried

I probed the next theorem shape from the predicates-51 report:

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

After rewriting all three correction terms with
`closedCurvatureCovDerivAtCorrectionAt_eq_connection_entry_terms`, unfolding
`closedCurvatureDefExpansionResidueAt`, and running `ring_nf`, Lean does not
reduce the goal to zero.  It leaves the nine derivative terms plus additional
unmatched `closedIteratedConnectionEntryFieldAt`,
`closedConnectionEntryOutputConnectionFieldAt`, and
`closedBracketConnectionEntryFieldAt` value terms.

A stronger probe trying to prove that

```lean
residue cyclic - correction cyclic = raw derivative block
```

also failed.  The error state still contained non-derivative correction
terms, so this is not currently a pure `ring` or orientation mismatch.

## Current blocker

The available anchored output-slot wrapper

```lean
closedBracketConnectionEntryFieldAt_cyclic_outputConnection_eq_connectionEntry_sub
```

is value-level.  It does not rewrite the derivative-level block directly, and
the naive expanded correction goal does not contain the exact sum pattern
needed by that theorem until more algebraic grouping is supplied.

The next missing proof-bearing bridge is one of:

1. A local theorem that canonical tangent `extend` sections have zero Lie
   bracket near their own anchor, strong enough to eliminate the differentiated
   bracket-entry fields.
2. A closed analogue of the model `coord_second_bianchi` Christoffel-family
   proof: product-rule expansion for the output-connection derivative block,
   slot symmetry from torsion-freeness, Schwarz symmetry for the remaining
   second derivatives, then `abel`.

The model theorem to mirror is:

```lean
RicciFlow.RicciFlow.coord_second_bianchi
```

## Downstream status

Because the cyclic scalar identity remains open, these were not assembled:

```lean
eventually_closed_cyclic_second_bianchi_of_inner_sum
hMiddle
eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
ClosedContractedBianchiAt.of_closed_trace_contraction_canonical
satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
```

## Verification

Before this report, refreshed stale Lean artifacts and verified:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, existing warnings only.

After adding this report, ran the required final build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, existing warnings only.
