# M5-glob-51 blocked: produced derivative fields feed the tower

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/TowerCloses.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.TowerCloses
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_derivative_fields_c1
```

It composes the current producer and consumer chain:

```text
FieldProducer -> ExpChartC2 -> ContDiffTwo -> EndpointBridge -> FTransitionDone
```

The theorem chooses the actual source and target derivative fields exported by
`FieldProducer.exists_source_target_expChart_derivative_fields_on_aligned_ball`,
shrinks to a common radius with the F-transition consumer, and exposes the
producer facts:

```lean
HasFDerivAt eM (sourceD v) v
HasFDerivAt eS (targetD (L v)) (L v)
∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q
∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q
```

Supplying `ContDiffAt ℝ 1 sourceD v` and
`ContDiffAt ℝ 1 targetD (L v)` for those same produced fields now feeds the
already verified `PackageLands` transition assembly and yields the signed
Christoffel F-transition law on the common punctured ball.

## Blocking boundary

This does not prove the unconditional F-transition law.  The repository still
does not export the non-hypothetical `C1` regularity of `FieldProducer`'s
selected fields:

```lean
ContDiffAt ℝ 1 sourceD v
ContDiffAt ℝ 1 targetD (L v)
```

The level-three inputs now present in `ThirdVariation.lean`, `FieldC1.lean`,
and `FlowSmoothness.lean` give the PL package, compact-uniform remainder, and
field regularity for the doubly augmented system.  What is still missing is the
actual bridge from those generic third-variation ingredients to the specific
noncomputably selected endpoint-derivative fields in `FieldProducer`, including
identification with a continuously differentiable endpoint field near each
hosted point.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/TowerCloses.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/TowerCloses.lean
git diff --check -- Poincare/Global/TowerCloses.lean
lake build Poincare.Global.TowerCloses
```

Actual result:

```text
forbidden-token scan: no matches
top-level declaration scan:
42:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_derivative_fields_c1

git diff --check -- Poincare/Global/TowerCloses.lean
exit status 0

lake build Poincare.Global.TowerCloses
✔ [3235/3235] Built Poincare.Global.TowerCloses (2.8s)
Build completed successfully (3235 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module
built successfully.
