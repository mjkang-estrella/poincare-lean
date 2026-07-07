# M5-glob-66 done: centered membership package for rescaled Ω

## Status

Added the required new Lean module:

- `Poincare/Global/CenteredMembership.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The module exports one non-vacuous theorem:

- `CenteredMembership.exists_rescaled_hosted_thirdVariation_centered_membership_clm_package`

For any continuous hosted doubly-augmented base curve `ζ`, the theorem rebuilds
the rescaled all-perturbation third-variation family and proves:

- exact initial value `Ω η 0 = η`;
- the hosted third-variation linear ODE on `Icc (-ε) ε`;
- additivity and homogeneity on that interval;
- centered membership with the concrete enlarged per-center radius
  `scale η * (a + r)`;
- additive and homogeneous centered-membership variants with the corresponding
  enlarged radii;
- for every `T ∈ Icc (-ε) ε`, a `TheSelector.HostedCLMPackage` for the endpoint
  `η ↦ Ω η T`, built directly from additivity and homogeneity.

The fixed-radius assumptions in `HostedCLM.exists_hostedCLMPackage` are not
used here: for an all-center linear ODE package over an unbounded vector space,
the PL `norm_le` bound depends on the center.  This strict partial instead
records the scaled centered-membership radius and feeds the endpoint CLM
package directly.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/CenteredMembership.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b|^omit .* in$' Poincare/Global/CenteredMembership.lean
git diff --check -- Poincare/Global/CenteredMembership.lean
lake build Poincare.Global.CenteredMembership
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
35:omit [T2Space M] in
46:theorem exists_rescaled_hosted_thirdVariation_centered_membership_clm_package

git diff --check -- Poincare/Global/CenteredMembership.lean
exit status 0

lake build Poincare.Global.CenteredMembership
✔ [3250/3250] Built Poincare.Global.CenteredMembership (5.5s)
Build completed successfully (3250 jobs).
```

The build replayed pre-existing imported-module warnings; no warning or error
was emitted for `Poincare/Global/CenteredMembership.lean`.
