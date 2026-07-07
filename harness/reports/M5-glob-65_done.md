# M5-glob-65 done: Ω rescale strict partial verified

## Status

Added the required new Lean module:

- `Poincare/Global/OmegaRescale.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports one non-vacuous theorem:

- `OmegaRescale.exists_rescaled_hosted_thirdVariation_solution_family_linear`

For any continuous hosted doubly-augmented base curve `ζ`, the theorem chooses
the zero-centered third-variation Picard-Lindelof package, normalizes every
perturbation into the PL ball, scales the local solution back, and proves:

- exact initial value `Ω η 0 = η` for every perturbation `η`;
- the hosted third-variation linear ODE for every `η` on `Icc (-ε) ε`;
- additivity `Ω (η + η') t = Ω η t + Ω η' t` on the interval;
- homogeneity `Ω (c • η) t = c • Ω η t` on the interval.

The additivity and homogeneity steps use the same solution-uniqueness
dissolution pattern as `SolutionsFeed.lean`: both compared curves are scaled
into the zero-centered PL ball and identified by
`linearODE_solution_uniqueOn_Icc`.

## Remaining boundary

This strict partial does not claim the full `HostedCLM` or indexed
F-transition tower.  The remaining public-interface gap is still the
`HostedCLM.exists_hostedCLMPackage` centered membership family:

```lean
∀ η t, Ω η t ∈ closedBall η a
∀ η η' t, Ω η t + Ω η' t ∈ closedBall (η + η') a
∀ c η t, c • Ω η t ∈ closedBall (c • η) a
```

The rescaled Ω family now supplies all-perturbation initial values, ODE data,
and solution linearity, but this file intentionally does not assert the
centered all-perturbation membership facts.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/OmegaRescale.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b|^omit .* in$' Poincare/Global/OmegaRescale.lean
git diff --check -- Poincare/Global/OmegaRescale.lean
lake build Poincare.Global.OmegaRescale
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
34:omit [T2Space M] in
44:theorem exists_rescaled_hosted_thirdVariation_solution_family_linear

git diff --check -- Poincare/Global/OmegaRescale.lean
exit status 0

lake build Poincare.Global.OmegaRescale
✔ [2838/2838] Built Poincare.Global.OmegaRescale (4.3s)
Build completed successfully (2838 jobs).
```

The build replayed pre-existing imported-module warnings; no warning or error
was emitted for `Poincare/Global/OmegaRescale.lean`.
