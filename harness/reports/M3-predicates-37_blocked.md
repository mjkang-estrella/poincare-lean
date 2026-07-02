# M3-predicates-37 blocked report

## Summary

The three requested native Bianchi bridges were not discharged.

No frozen predicate statement was changed, and no Lean source theorem was
weakened.  I did not add assumption-only wrappers because the existing
scaffold already has the relevant conditional adapters; adding more wrappers
would not close any of the three requested bridges.

## What was checked first

Read and obeyed `harness/worker_contract.md`.

Read `harness/reports/M3-predicates-36_progress.md`; it correctly identifies
the remaining neighborhood target as the three near-`x` identities:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    closedRicciDivergenceTraceAt g y w
```

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  closedScalarContractionDerivTraceAt g y w =
    extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  2 * closedRicciDivergenceTraceAt g y w =
    closedScalarContractionDerivTraceAt g y w
```

The current worktree was clean before investigation.

## Direct bridge probe

The shared key bridge for the first two goals is the pointwise Ricci derivative
trace expansion:

```lean
covTensor2DerivAt g (ricciVariationField g) x v u w =
  closedCovRicciDerivAt g x v u w
```

After refreshing the module artifact with:

```bash
lake build Poincare.Global.ScalarVariation
```

the direct proof probe:

```lean
example
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w : TM x) :
    covTensor2DerivAt g (ricciVariationField g) x v u w =
      closedCovRicciDerivAt g x v u w := by
  classical
  unfold covTensor2DerivAt ricciVariationField
    closedCovRicciDerivAt closedCurvatureCovDerivAt
  simp
```

does not close.  Lean reduces it to the real missing theorem:

```lean
∂_v (g.ricciAt · (extend u) (extend w))
  - Ric(∇_v u, w) - Ric(u, ∇_v w)
=
Σ_i coord_i ((∇_v R)(b_i, u) w)
```

This is exactly the closed analogue of the model lemma:

```lean
RicciFlow.RicciFlow.covRicciDeriv_eq_tensor_deriv
```

## Why the existing Ricci contraction theorem is not enough

The closest closed theorem is:

```lean
ricciAt_eq_curvature_contraction
```

At a fixed point it rewrites Ricci as a curvature trace in that point's tangent
basis.  But for the derivative field needed here, applying it at a nearby
point `y` produces the moving basis `Module.finBasis ℝ (TM y)` and sections
`extend E (extend E u y)`, not the anchored `x`-basis trace used in
`closedCovRicciDerivAt`.

A direct probe of the desired anchored rewrite fails with this mismatch: the
source theorem gives a trace over `TM y`, while the bridge needs the
extend-frame trace from `TM x` and the derivative of that trace.  This is the
same derivative-level Ricci trace boundary described in
`M3-predicates-35_blocked.md`, now isolated inside the native vocabulary.

## Exact missing theorem surfaces

To close bridges (1) and (2), the next required theorem is:

```lean
theorem covTensor2DerivAt_ricciVariationField_eq_closedCovRicciDerivAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v u w : TM x) :
    covTensor2DerivAt g (ricciVariationField g) x v u w =
      closedCovRicciDerivAt g x v u w
```

This should be the closed port of the model chain:

- `coordRicci_trace_slot_cancel`
- `fderiv_coordRicci_eq`
- `covRicciDeriv_eq_tensor_deriv`

With that theorem, bridge (1) follows from
`tensorDivergenceOneFormAt_ricciVariationField_swap`; bridge (2) follows from
`traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt` plus
`traceMetricVariationAt_ricci`.

To close bridge (3), the existing scaffold still needs native proofs of:

```lean
∀ v w z : TM x,
  closedCovRicciDerivAt g x v w z
    + closedCurvatureDivergenceAt g x w v z
    - closedCovRicciDerivAt g x w v z = 0
```

and

```lean
∀ w : TM x,
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
   let b := Module.finBasis ℝ (TM x)
   ∑ i, closedCurvatureDivergenceAt g x w
     (metricDualVectorAt g x (b.coord i)) (b i))
    = closedRicciDivergenceTraceAt g x w
```

The first is the closed first-contracted second-Bianchi theorem.  The second
is the raised middle-term contraction.  The model proof of the second uses:

- `covCurvDeriv_pair_symm`
- `sum_raised_contraction_swap`
- `covCurvDeriv_first_bianchi`
- `covCurvDeriv_applied_skew`

No corresponding closed lemmas for `closedCurvatureCovDerivAt` currently exist
in `Poincare/Global/ScalarVariation.lean`.

## Exact current goal state

The final target remains:

```lean
∀ᶠ y in nhds x, ClosedContractedBianchiOneFormAt g y
```

Equivalently:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

Once this one-form identity is proved, the existing adapter
`ClosedContractedBianchiAt.of_oneForm_near` still fires the frozen
`ClosedContractedBianchiAt` predicate, and the Hamilton scalar-evolution
wrappers remain ready to consume it.

## Verification

Current source check before this report:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with existing warnings only.

Module build used to refresh the import artifact:

```bash
lake build Poincare.Global.ScalarVariation
```

Result: success, ending with:

```text
Build completed successfully (2805 jobs).
```

Standing checks after writing this report:

```bash
forbidden-placeholder scan on Poincare/Global/ScalarVariation.lean \
  and Poincare/Global/ScalarEvolution.lean
git diff --check
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- Forbidden-placeholder scan: no matches.
- Whitespace check: success.
- Requested two-module build: success, ending with
  `Build completed successfully (2806 jobs).`
