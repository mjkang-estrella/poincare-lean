# M5-glob-53 blocked: canonical C1 consumer bridge landed

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/CanonicalC1.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.CanonicalC1
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_canonical_fderiv_c1
```

It composes the already verified pieces:

- `TowerCloses.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_derivative_fields_c1`
- `LevelThreeFeed.selected_expChart_derivative_fields_contDiffAt_one_of_fderiv_contDiffAt_one`

For each produced punctured-ball datum, the theorem consumes the canonical
regularity hypotheses

```lean
ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eM q) v
ContDiffAt ℝ 1 (fun q : E3 => fderiv ℝ eS q) (L v)
```

and uses the local `HasFDerivAt` facts for the selected fields to derive

```lean
ContDiffAt ℝ 1 sourceD v
ContDiffAt ℝ 1 targetD (L v)
```

which are then fed into the existing tower consumer to obtain the signed
Christoffel F-transition law.

## Blocking boundary

This still does not prove the unconditional F-transition law requested by the
task title.  The repository still lacks an exported theorem that applies the
level-three residual/smooth-dependence ingredients to prove the canonical
regularity inputs above for the exponential charts.

The missing exported bridge remains:

1. instantiate the doubly augmented ODE facts at the hosted source and target
   data;
2. feed the third-variation residual theorem to prove
   `HasFDerivAt (fun q => fderiv ℝ e q) CLM q` at nearby ball points;
3. prove continuous dependence of those third-variation endpoint `CLM`s in
   `q`, yielding
   `ContDiffAt ℝ 1 (fun q => fderiv ℝ e q) q`.

Existing files provide reusable ingredients (`ThirdVariation.lean`,
`FieldC1.lean`, `FlowSmoothness.lean`, `SecondFlowDerivative.lean`,
`SecondDischarge.lean`, and `AugmentedDependence.lean`), but not that combined
hosted endpoint theorem.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/CanonicalC1.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/CanonicalC1.lean
git diff --check -- Poincare/Global/CanonicalC1.lean
lake build Poincare.Global.CanonicalC1
```

Actual result:

```text
forbidden-token scan: no matches
top-level declaration scan:
42:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_canonical_fderiv_c1

git diff --check -- Poincare/Global/CanonicalC1.lean
exit status 0

lake build Poincare.Global.CanonicalC1
✔ [3237/3237] Built Poincare.Global.CanonicalC1 (14s)
Build completed successfully (3237 jobs).
```

The build emitted warnings while replaying pre-existing modules; none were new
errors in `Poincare.Global.CanonicalC1`.
