# M5-glob-44 blocked: augmented Gronwall dependence exported

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/AugmentedDependence.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .exists_chartChristoffel_augmentedFlow_lipschitzOn_of_ODE
```

For any supplied common solution family

```lean
β : ((E × E) × (E × E)) → ℝ → ((E × E) × (E × E))
```

of the augmented chart-Christoffel system

```lean
z' = augmentedGeodesicFlowField (chartChristoffelField g x₀) z
```

whose trajectories remain in a common closed ball, the theorem obtains the
closed-tube Lipschitz constant from `AugmentedC1` and proves fixed-time
Lipschitz dependence on the augmented initial state:

```lean
∃ K : ℝ≥0,
  LipschitzOnWith
    ⟨Real.exp ((K : ℝ) * T), (Real.exp_pos _).le⟩
    (fun z : (E × E) × (E × E) => β z t) S
```

This is the stage-(2) Grönwall dependence replay for the augmented system.  It
uses the existing field-generic `dist_le_of_trajectories_ODE_of_mem` comparison
instead of replaying the Grönwall proof.

## Blocking boundary

This does not close the full M5-glob-44 target.  The repository still lacks the
non-hypothetical neighborhood-level derivative-field package required by
`ExpChartC2`:

```lean
sourceD targetD : E3 → E3 →L[ℝ] E3
∀ q ∈ U, HasFDerivAt eM (sourceD q) q
ContDiffAt ℝ 1 sourceD v
∀ q ∈ U, HasFDerivAt eS (targetD q) q
ContDiffAt ℝ 1 targetD (L v)
```

The remaining replay is still:

- package the augmented field's uniform Taylor remainders on the concrete
  compact tubes;
- instantiate the fixed-time augmented derivative theorem with a genuine
  neighborhood family of augmented solutions;
- identify the second-variation endpoint CLMs with the canonical
  `q ↦ fderiv ℝ (expAtChartOpenPartialHomeomorph ...) q` field and prove that
  field is `C¹` near the hosted datum.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/AugmentedDependence.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/AugmentedDependence.lean
git diff --check -- Poincare/Global/AugmentedDependence.lean
lake build Poincare.Global.AugmentedDependence
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
39:theorem exists_chartChristoffel_augmentedFlow_lipschitzOn_of_ODE

git diff --check -- Poincare/Global/AugmentedDependence.lean
exit status 0

lake build Poincare.Global.AugmentedDependence
✔ [2835/2835] Built Poincare.Global.AugmentedDependence (1.0s)
Build completed successfully (2835 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
