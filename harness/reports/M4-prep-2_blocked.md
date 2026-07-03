# M4-prep-2 blocked

## Blocker

The requested trace-consistency target is not provable from the current
`lichnerowiczCurvatureAt` definition.  The definition at
`Poincare/Global/ScalarVariation.lean:13378` contracts the curvature operator
over its first two slots:

```lean
∑ i,
  h x
    (CovariantDerivative.curvatureOp g.leviCivita
      (extend E (b i)) (extend E (sharp i)) (extend E u) x)
    w
  + h x u
    (CovariantDerivative.curvatureOp g.leviCivita
      (extend E (b i)) (extend E (sharp i)) (extend E w) x)
```

For the requested trace identity with `h = ricciVariationField g`, the expected
goal shape is:

```lean
(letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
 let b := Module.finBasis ℝ (TM x)
 let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
   fun i ↦ metricDualVectorAt g x (b.coord i)
 ∑ j, lichnerowiczCurvatureAt g (ricciVariationField g) x (b j) (sharp j))
  = g.ricciNormSqAt x
```

But the left side is built from the metric trace of the first antisymmetric
curvature pair.  The model layer already records this contraction as zero:

```lean
RicciFlow.coordRiemann_first_pair_metric_trace_zero
```

at `Poincare/ModelLaplacian.lean:26017`, with the comment:

```text
Σᵢ Rm(bᵢ, ♯bⁱ, a, b) = 0
```

The global curvature operator has the same first-slot antisymmetry:

```lean
CovariantDerivative.curvatureOp_antisymm_apply
```

at `Poincare/RiemannCurvatureOperator.lean:72`.

So the current `lichnerowiczCurvatureAt` slot order is the "wrong curvature
contraction" described by the model trace algebra: it traces an antisymmetric
pair before the Ricci tensor can produce a `|Ric|²` contribution.  A constant
sectional-curvature sanity check gives the same contradiction: in an orthonormal
frame the current contraction contains `R(eᵢ, eᵢ)`, hence vanishes, while
`|Ric|²` is nonzero for nonflat constant curvature.

## Consequence

Subtask 2 cannot produce the requested
`tr_g(lichnerowiczCurvatureAt g (ricciVariationField g)) = ricciNormSqAt g`
identity without changing the definition or changing the expected statement.
Therefore the trace-consistency payoff in subtask 6 is blocked as stated.

The likely correction is to replace this first-pair trace with the mixed
Riemann/Ricci contraction used by the Ricci trace convention, e.g. a term built
from `curvatureOp ... (extend E (b i)) (extend E u) (extend E w)` paired against
`sharp i`, rather than `curvatureOp ... (extend E (b i)) (extend E (sharp i))`.

## Verification

No Lean source files were changed.  The requested build was run to confirm the
unchanged baseline before reporting this blocker:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: succeeded, with existing warnings only.
