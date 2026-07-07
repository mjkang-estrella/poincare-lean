# M5-glob-46 blocked: neighborhood derivative-field package consumer lands

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/PackageLands.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.PackageLands
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_expChart_derivative_fields
```

It composes the already-exported chain:

```text
ExpChartC2 -> ContDiffTwo -> EndpointBridge -> FTransitionDone
```

The theorem keeps the existing `FTransitionDone` existential interface
(`ρ`, `Afield`, `Bfield`, `DF`) and proves the signed Christoffel
F-transition law from the exact neighborhood derivative-field package demanded
by `ExpChartC2`:

```lean
sourceD targetD : E3 → E3 →L[ℝ] E3
∃ U ∈ 𝓝 v, ∀ q ∈ U, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
HasFDerivAt eM (sourceIso : E3 →L[ℝ] E3) v
∃ U ∈ 𝓝 (L v), ∀ q ∈ U, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

Thus the transition-law consumer no longer asks separately for:

```lean
ContDiffAt ℝ 2 (CartanDifferential.cartanChartMap g x0 p0 L) (eM v)
```

That `C²` fact is built internally by feeding the derivative-field package to
`ExpChartC2.cartanChartMap_contDiffAt_two_of_expChart_derivative_fields`, then
the result is passed to
`EndpointBridge.exists_cartanChartMap_christoffelAt_F_transition_law_of_contDiffAt_two`.

## Blocking boundary

The full unconditional task is still blocked at the producer side.  The new
theorem does not construct the actual `sourceD` and `targetD` fields from the
augmented flow/second-variation endpoints, nor does it prove their
neighborhood `HasFDerivAt` facts or `ContDiffAt ℝ 1` dependence.

The exact remaining non-hypothetical producer is still:

```lean
sourceD targetD : E3 → E3 →L[ℝ] E3
∀ q near v, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
∀ q near L v, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

with `sourceD` and `targetD` identified with the flow-derivative /
second-variation endpoint fields supplied by the augmented Gronwall chain, on
both the source side and the round-sphere target side.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/PackageLands.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/PackageLands.lean
git diff --check -- Poincare/Global/PackageLands.lean
lake build Poincare.Global.PackageLands
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
39:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_expChart_derivative_fields

git diff --check -- Poincare/Global/PackageLands.lean
exit status 0

lake build Poincare.Global.PackageLands
✔ [3233/3233] Built Poincare.Global.PackageLands (14s)
Build completed successfully (3233 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
