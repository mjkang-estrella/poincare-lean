# M3-predicates-41 blocked report

## Summary

The closed Levi-Civita regularity upgrade itself is proved and the canonical
curvature-entry derivative bridge is now available.

New theorem surfaces:

```lean
CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
CovariantDerivative.chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₂
CovariantDerivative.chartTransportedLeviCivitaHom_contMDiffAt₂
LeviCivitaExistence.closedLeviCivitaConnection_contMDiff₂
ClosedSmoothRiemannianMetric.leviCivita_contMDiff₂
closedCurvatureFieldMDifferentiableAt_canonical
closedCurvatureEntryDerivativeBridgeAt_canonical
```

The first four move the closed Levi-Civita gluing chain from order `1` to
order `2`.  The curvature-field differentiability witness then follows by
expanding `curvatureOp` and applying the new localized `C²` covariant
derivative regularity lemma to the inner derivative fields.

## Completed part

The canonical bridge is now theorem-shaped:

```lean
theorem closedCurvatureEntryDerivativeBridgeAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ClosedCurvatureEntryDerivativeBridgeAt g x
```

This closes the exact remaining atom from `M3-predicates-40_blocked.md`.

## Remaining exact goal state

The Ricci trace expansion is still not discharged:

```lean
theorem closedRicciDerivativeExpansionAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ClosedRicciDerivativeExpansionAt g x
```

and its neighborhood form:

```lean
theorem eventually_closedRicciDerivativeExpansionAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, ClosedRicciDerivativeExpansionAt g y
```

The remaining non-algebraic step is the anchored Gram/Ricci trace derivative:
for fixed `u w : TM x`, package the scalar curvature entries

```lean
fun y a q =>
  g.inner y
    (CovariantDerivative.curvatureOp g.leviCivita
      (extend E a) (extend E u) (extend E w) y)
    q
```

as a local bilinear `(0,2)` tensor, use
`closedCurvatureEntryDerivativeBridgeAt_canonical` for its scalar-entry
derivatives, and contract the resulting Gram trace.  The existing downstream
consumers are already present:

```lean
eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt
eventually_closedScalarContractionDerivTraceAt_eq_extDerivFun_scalarAt
ClosedContractedBianchiAt.of_closed_trace_contraction_near
```

After the Ricci expansion and the already-recorded raised middle-term
contraction are supplied, bridge (3), the cyclic second-Bianchi core, remains
the sole intrinsic Bianchi item.

## Verification notes

The changed theorem surfaces are intended to be verified with:

```bash
lake build Poincare.Global.LeviCivitaRegularity \
  Poincare.Global.ScalarVariation \
  Poincare.Global.ScalarEvolution
```

The final build result for this worktree is recorded in the task response.
