# M5-glob-43 blocked: augmented field C1 exported

## Status

Strict-partial progress was added in the required new Lean file:

- `Poincare/Global/AugmentedC1.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall
```

For any chart-Christoffel field of a closed smooth Riemannian metric, it proves
the stage-one augmented regularity package:

```lean
ContDiff ℝ 1
    (augmentedGeodesicFlowField (chartChristoffelField g x₀)) ∧
  ∃ K : ℝ≥0,
    LipschitzOnWith K
      (augmentedGeodesicFlowField (chartChristoffelField g x₀))
      (closedBall p (a + 1))
```

The proof derives `ContDiff ℝ 2` regularity of the chart Christoffel field from
the blended chart metric, obtains `ContDiff ℝ 2` for the first-order geodesic
field, then applies `contDiff_fderiv_apply` to prove the augmented
`(p, ψ) ↦ (F p, D F p ψ)` field is `C1`.  The closed-ball Lipschitz constant is
then obtained from the existing `ContDiffOn.exists_lipschitzOnWith` compact
convex argument.

## Blocking boundary

This does not close the full derivative-field package demanded by
`ExpChartC2`.  The repository still lacks an exported theorem constructing, on
a neighborhood of each hosted datum,

```lean
sourceD targetD : E3 → E3 →L[ℝ] E3
```

with:

```lean
∀ q ∈ U, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
∀ q ∈ U, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

The new theorem supplies the concrete augmented-field `C1`/compact-Lipschitz
input for the replay, but the remaining steps still need to connect the
augmented fixed-time flow derivative from the second-variation system to the
canonical `fderiv` field of `expAtChartOpenPartialHomeomorph`, uniformly on a
neighborhood.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/AugmentedC1.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/AugmentedC1.lean
git diff --check -- Poincare/Global/AugmentedC1.lean
lake build Poincare.Global.AugmentedC1
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
38:theorem exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall

git diff --check -- Poincare/Global/AugmentedC1.lean
exit status 0

lake build Poincare.Global.AugmentedC1
✔ [2834/2834] Built Poincare.Global.AugmentedC1 (4.2s)
Build completed successfully (2834 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
