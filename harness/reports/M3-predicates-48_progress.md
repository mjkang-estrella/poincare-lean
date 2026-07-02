# M3-predicates-48 progress report

## Summary

This task landed the group-1 mixed second-connection cancellation
infrastructure in `Poincare/Global/ScalarVariation.lean`.

New theorem surface:

```lean
closedConnectionEntryFieldAt
closedConnectionEntry_contMDiffAt_two
closedSecondDirectionalEntryAt
closedSecondDirectionalEntryAt_comm
closedConnectionEntry_secondDirectional_comm
closedConnectionEntry_mixed_second_cyclic_cancel
```

The main new cancellation theorem is
`closedConnectionEntry_mixed_second_cyclic_cancel`.  It packages the three
raw mixed second-directional scalar connection-entry pairs
`g(∇_w z, q)`, `g(∇_v z, q)`, and `g(∇_u z, q)` into one finite cyclic
sum and proves that the sum is zero by the closed Schwarz lemma
`extDerivFun_extDerivFun_extend_corrected_symm`.

The required `C²` input for those scalar connection entries is supplied by
`closedConnectionEntry_contMDiffAt_two`, using the existing canonical
Levi-Civita `C²` regularity and the existing covariant-section regularity
bridge.

## Remaining exact goal state

The full requested theorem is still open:

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

By `eventually_closed_cyclic_second_bianchi_of_inner_sum`, it remains enough
to prove the scalar-paired cyclic sum:

```lean
∀ᶠ y in nhds x, ∀ u v w z q : TM y,
  g.inner y (closedCurvatureCovDerivAt g y v u w z) q
    + g.inner y (closedCurvatureCovDerivAt g y u w v z) q
    + g.inner y (closedCurvatureCovDerivAt g y w v u z) q = 0
```

After `closedCurvatureCovDerivAt_cyclic_inner_koszul_expansion`, the
remaining displayed cancellation is exactly:

```lean
closedCurvatureDefExpansionAt g y v u w z q
  + closedCurvatureDefExpansionAt g y u w v z q
  + closedCurvatureDefExpansionAt g y w v u z q
  - (closedCurvatureCovDerivAtCorrectionAt g y v u w z q
    + closedCurvatureCovDerivAtCorrectionAt g y u w v z q
    + closedCurvatureCovDerivAtCorrectionAt g y w v u z q) = 0
```

The group-1 lemma is not yet wired through the unfolded
`closedCurvatureDefExpansionAt`/`closedCurvatureCovDerivAtCorrectionAt`
bookkeeping.  The still-open cancellation groups are:

1. alignment of the new raw mixed second-connection cancellation with the
   `covTensor2DerivAt` terms in `closedCurvatureDefExpansionAt`,
2. torsion-free alignment of the first-order product terms,
3. cyclic cancellation of the metric/bracket correction block.

## Verification

Verified during the task:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation
rg -n '\b(sorry|admit|axiom|native_decide)\b' \
  Poincare/Global/ScalarVariation.lean \
  harness/reports/M3-predicates-48_progress.md
git diff --check
```

Result: Lean source check and required build succeeded, with existing warnings
only.  The placeholder scan found no matches, and `git diff --check` was clean.
