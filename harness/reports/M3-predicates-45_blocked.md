# M3-predicates-45 blocked report

## Summary

I did not land the closed cyclic second-Bianchi proof.

The current worktree builds at the module level, and the existing predicates-44
surface is present:

```lean
closedCurvatureEntryDerivAt
closedCurvatureCovDerivAtCorrectionAt
closedCurvatureCovDerivAt_inner_eq_entry_deriv_sub_correction
closedCurvatureCovDerivAt_cyclic_inner_expansion
```

The exact cyclic scalar expansion remains the best available native closed
surface.  It rewrites the scalar pairing of the cyclic sum of
`closedCurvatureCovDerivAt` into the three flat scalar curvature-entry
derivatives minus the three four-term slot-correction blocks.

## Exact goal still open

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

This is exactly the `hSecond` shape consumed by:

```lean
eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
```

## Why it is blocked

The model proof closes through:

```lean
RicciFlow.RicciFlow.coord_second_bianchi
```

whose key rewrite is:

```lean
RicciFlow.RicciFlow.fderiv_coordCurvatureOp_family
```

That model theorem expands `fderiv` of `coordCurvatureOp` into second
Christoffel derivatives plus the product terms.  The closed file still lacks
the corresponding native bridge:

```lean
closedCurvatureEntryDerivAt
  =
    second connection-derivative terms
      + connection-product derivative terms
```

for `CovariantDerivative.curvatureOp g.leviCivita` in anchored extension
slots.  Without that exposed formula, the cyclic scalar expansion cannot reach
the Schwarz rewrites and final `abel` bookkeeping used by the model proof.

I also checked the two plausible shortcut surfaces:

1. `Poincare.AnalyticFoundation` exposes abstract second-Bianchi evidence as
   `Poincare.HasSecondBianchiIdentity` /
   `Poincare.RiemannCurvatureSecondBianchiData`, but those are for
   `TimeDependentRiemannianMetric`.  There is no current bridge from that
   package evidence to `ClosedSmoothRiemannianMetric` or to
   `closedCurvatureCovDerivAt`.
2. `Poincare.Global.LeviCivitaTransport` proves value-level chart transport for
   one Levi-Civita application on a cutoff-one neighborhood.  It does not yet
   provide a curvature-operator or covariant-curvature-derivative transport
   theorem, so the model `coord_second_bianchi` cannot be rewritten into the
   closed native target by existing lemmas.

The missing next lemma should be the closed analogue of
`fderiv_coordCurvatureOp_family`, probably proved by differentiating the
unfolded definition of `CovariantDerivative.curvatureOp` through the existing
entry-derivative and metric-compatibility machinery.  Once that formula exists,
the remaining route should mirror `coord_second_bianchi`:

```lean
unfold closed curvature derivative expansion
rewrite connection slot symmetry from g.leviCivita_torsionFreeAt
rewrite mixed second derivatives by the closed Schwarz lemmas
simp only [map_add/map_sub/comp-style distributivity as needed]
abel
```

## Verification

Baseline module build on the unmodified Lean sources:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, existing warnings only, ending with:

```text
Build completed successfully (2805 jobs).
```

Probe of the relevant theorem surfaces:

```bash
lake env lean --stdin
```

with imports:

```lean
import Poincare.Global.ScalarVariation
import Poincare.AnalyticFoundation
import Poincare.ModelLaplacian
```

confirmed the available surfaces:

```lean
Poincare.closedCurvatureCovDerivAt_cyclic_inner_expansion
Poincare.eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi
Poincare.HasSecondBianchiIdentity
Poincare.RiemannCurvatureSecondBianchiData
RicciFlow.RicciFlow.coord_second_bianchi
RicciFlow.RicciFlow.covCurvDeriv
```

No Lean source file was edited in this task.
