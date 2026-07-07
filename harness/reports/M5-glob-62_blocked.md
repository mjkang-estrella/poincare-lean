# M5-glob-62 blocked: indexed endpoint-package consumer lands, selector producer still missing

## Status

Verified partial progress was added in the required new Lean module:

- `Poincare/Global/IndexedSelection.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports exactly one theorem:

```lean
theorem Poincare.IndexedSelection
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_indexed_endpoint_gronwall_packages
```

This is the non-vacuous final consumer step for the indexed endpoint package.
It starts from the existing
`ContinuityPackages.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_gronwall_endpoint_bounds`
result and groups the remaining source/target endpoint input as a concrete
existential package at each punctured normal vector:

```lean
∃ sourceEndpoint targetEndpoint sourceU targetU Ks Kt,
  sourceU ∈ 𝓝 v ∧
  (∀ q ∈ sourceU, ∀ q' ∈ sourceU,
    ‖sourceEndpoint q' - sourceEndpoint q‖ ≤ (Ks : ℝ) * dist q' q) ∧
  (∀ q ∈ sourceU,
    HasFDerivAt (fun q' : E3 => fderiv ℝ eM q') (sourceEndpoint q) q) ∧
  targetU ∈ 𝓝 (L v) ∧
  (∀ q ∈ targetU, ∀ q' ∈ targetU,
    ‖targetEndpoint q' - targetEndpoint q‖ ≤ (Kt : ℝ) * dist q' q) ∧
  ∀ q ∈ targetU,
    HasFDerivAt (fun q' : E3 => fderiv ℝ eS q') (targetEndpoint q) q
```

Given that package, the theorem eliminates the endpoint callback and returns
the signed F-transition law under only the already-separate inverse-source and
metric-derivative inputs.

## Remaining blocking boundary

The requested unconditional F-transition law is still not closed because this
worktree still does not export the actual selector producer

```lean
q ↦ ζ_q, Ω_q, D_q
```

over source and target neighborhoods.

The concrete missing bridge is the construction, from the hosted
third-variation data, of endpoint fields satisfying the package above.  In
particular, the public exports still do not assemble all of the following into
one neighborhood-indexed source/target package:

1. a selected doubly-augmented base curve `ζ_q` at every `q` in the
   neighborhood;
2. a selected hosted third-variation family `Ω_q`;
3. a selected endpoint CLM `D_q`;
4. the projected derivative representation
   `HasFDerivAt (fun q' => fderiv ℝ e q') (endpoint q) q`;
5. the cross-point Gronwall estimate for the selected family,
   `‖endpoint q' - endpoint q‖ ≤ C * dist q' q`.

The available facts are still separate: `OmegaGronwall` proves the paired-base
Gronwall bound once two compatible endpoint CLMs/families are supplied, and
`HostedCLM` constructs an endpoint CLM from stronger hosted-family hypotheses.
There is no exported theorem tying those into the neighborhood-indexed
`Classical.choice` selection and proving the cross-point bound for the selected
objects.  Assuming that package here would be the missing producer in different
notation, so the full target remains blocked at that precise boundary.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/IndexedSelection.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b' Poincare/Global/IndexedSelection.lean
git diff --check -- Poincare/Global/IndexedSelection.lean
lake build Poincare.Global.IndexedSelection
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
39:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_indexed_endpoint_gronwall_packages

git diff --check -- Poincare/Global/IndexedSelection.lean
exit status 0

lake build Poincare.Global.IndexedSelection
✔ [3249/3249] Built Poincare.Global.IndexedSelection (3.6s)
Build completed successfully (3249 jobs).
```

The build replayed pre-existing imported-module warnings; no error remained in
`Poincare/Global/IndexedSelection.lean`.
