# M5-glob-47 blocked: derivative fields chosen, C1 field regularity missing

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/FieldProducer.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.FieldProducer
  .exists_source_target_expChart_derivative_fields_on_aligned_ball
```

The theorem uses
`UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`
to choose actual fields:

```lean
sourceD targetD : E3 -> E3 ->L[ℝ] E3
```

and proves the neighborhood derivative-field facts currently available from
the ball-uniform selector:

```lean
∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q
∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q
```

It also proves the pointwise facts at the aligned pair:

```lean
HasFDerivAt eM (sourceD v) v
HasFDerivAt eS (targetD (L v)) (L v)
```

The target field is indexed on the target chart by pulling back through
`L.toContinuousLinearEquiv.symm`, so its neighborhood is an honest
neighborhood of `L v`.

## Blocking boundary

This does not yet feed `PackageLands.lean` to the F-transition law, because
`ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields` still
requires:

```lean
ContDiffAt ℝ 1 sourceD v
ContDiffAt ℝ 1 targetD (L v)
```

The present public exports give pointwise strict derivatives and neighborhood
`HasFDerivAt` facts for the selected fields, plus Lipschitz dependence of
augmented endpoints.  They do not export differentiability of the selected
CLM-valued field `q ↦ sourceD q` or `q ↦ targetD q`.

That missing `ContDiffAt ℝ 1` field regularity is the remaining producer
boundary.  Filling it appears to require a genuine second-variation
field-differentiability residual, i.e. the next smooth-dependence layer for the
selected derivative field, not merely the existing Lipschitz dependence
estimate.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/FieldProducer.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/FieldProducer.lean
git diff --check -- Poincare/Global/FieldProducer.lean
lake build Poincare.Global.FieldProducer
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
45:theorem exists_source_target_expChart_derivative_fields_on_aligned_ball

git diff --check -- Poincare/Global/FieldProducer.lean
exit status 0

lake build Poincare.Global.FieldProducer
✔ [3206/3206] Built Poincare.Global.FieldProducer (8.8s)
Build completed successfully (3206 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
