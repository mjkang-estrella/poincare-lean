# M5-glob-58 done: Omega instantiation and Gronwall endpoint bound

## Status

Verified Lean payload was added in the required new module:

- `Poincare/Global/OmegaGronwall.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The module exports exactly the two requested facts:

1. `Poincare.GeodesicTransport.exists_hosted_thirdVariation_solution_family_on_paired_base`
   instantiates
   `exists_hosted_thirdVariation_solution_family_on_pl_closedBall` at the
   concrete paired hosted base curve
   `τ ↦ (β y.1 τ, Ξ y.1 y.2 τ)`, producing `Ω` with initial-value,
   third-variation ODE, and closed-ball facts in the downstream shape.

2. `Poincare.GeodesicTransport.chartChristoffel_thirdVariation_endpoint_gronwall_bound`
   proves the endpoint CLM bound
   `‖D₂ - D₁‖ ≤ C * δnorm` for two third-variation families over nearby
   doubly-augmented base curves, assuming the uniform base-curve bound
   `‖ζ₂ τ - ζ₁ τ‖ ≤ δnorm` on the time interval.  The proof derives the
   coefficient Lipschitz constant from one higher `ContDiff` regularity of the
   chart-Christoffel doubly-augmented field and then applies the inhomogeneous
   Gronwall comparison.

Private helper lemmas in the file prove the one-higher regularity,
coefficient Lipschitz-on-closed-ball fact, and the generic linear-ODE endpoint
Gronwall estimate used by the second exported theorem.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/OmegaGronwall.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b|^private theorem' Poincare/Global/OmegaGronwall.lean
git diff --check -- Poincare/Global/OmegaGronwall.lean
lake build Poincare.Global.OmegaGronwall
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
39:private theorem chartChristoffel_doublyAugmentedField_contDiff_two
125:private theorem exists_lipschitzOnWith_chartChristoffel_thirdVariation_coefficient_closedBall
151:private theorem linearODE_endpoint_clm_lipschitz_of_coefficients
306:theorem exists_hosted_thirdVariation_solution_family_on_paired_base
335:theorem chartChristoffel_thirdVariation_endpoint_gronwall_bound

git diff --check -- Poincare/Global/OmegaGronwall.lean
exit status 0

lake build Poincare.Global.OmegaGronwall
✔ [2845/2845] Built Poincare.Global.OmegaGronwall (5.1s)
Build completed successfully (2845 jobs).
```

The build replayed pre-existing imported-module warnings; no warning was
emitted from `Poincare/Global/OmegaGronwall.lean`.

