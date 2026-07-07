# M5-glob-64 blocked: Ξ connector verified, Ω-to-CLM bridge still missing

## Status

Added the required new Lean module:

- `Poincare/Global/TwoConnectors.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports one non-vacuous theorem:

- `TwoConnectors.exists_xiSelectorPackage_on_pl_closedBall`

This is the requested Ξ-side connector available from the current public
exports.  For any continuous augmented base curve `ζ`, it selects a local
second-variation family `Ξ` from
`GeodesicTransport.exists_isPicardLindelof_chartChristoffel_secondVariation_linearODE`
and exports:

- positive time radius `ε`;
- positive PL perturbation radius `r`;
- exact initial value `Ξ η 0 = η` for `η ∈ closedBall 0 r`;
- the second-variation ODE on `Icc (-ε) ε`;
- closed-ball membership on the same interval.

This is the actual PL-ball selector needed to form the hosted
doubly-augmented base once the selected perturbation is known to lie in the PL
ball.

## Remaining blocking boundary

The Ω-to-CLM bridge still cannot be honestly constructed from the public
exports.

`OmegaGronwall.exists_hosted_thirdVariation_solution_family_on_paired_base`
exports a local family:

```lean
∀ h : A × A, h ∈ closedBall (0 : A × A) r → ...
```

but `HostedCLM.chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc`
requires all-perturbation hypotheses with one uniform PL package and
one uniform membership radius:

```lean
∀ η : A × A, Ω η 0 = η
∀ η : A × A, ∀ t ∈ Icc tmin tmax, HasDerivWithinAt ...
∀ η : A × A, ∀ t ∈ Icc tmin tmax, Ω η t ∈ closedBall η a
∀ η η' : A × A, ∀ t ∈ Icc tmin tmax,
  Ω η t + Ω η' t ∈ closedBall (η + η') a
∀ c η, ∀ t ∈ Icc tmin tmax,
  c • Ω η t ∈ closedBall (c • η) a
```

The linear rescaling pattern can normalize initial perturbations into the
local PL ball and recover initial values and ODEs by homogeneity.  However,
the public local Ω theorem only gives membership in a fixed ball around `0`;
after scaling back, it does not provide the fixed-radius centered membership
`Ω η t ∈ closedBall η a` uniformly for all `η`, nor the corresponding add/smul
membership facts.  The existing generic linear ODE PL constructor also chooses
the vector-field bound from the center norm, so it does not provide the single
uniform all-center PL package required by `HostedCLM`.

Because that bridge is still missing, the selected `D_q` packages cannot be
constructed from the selected local `Ω_q`, the indexed endpoint packages cannot
be assembled, and `IndexedSelection`'s F-transition consumer cannot be fired
unconditionally in this slice.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/TwoConnectors.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b|^omit .* in$' Poincare/Global/TwoConnectors.lean
git diff --check -- Poincare/Global/TwoConnectors.lean
lake build Poincare.Global.TwoConnectors
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
36:omit [T2Space M] in
47:theorem exists_xiSelectorPackage_on_pl_closedBall

git diff --check -- Poincare/Global/TwoConnectors.lean
exit status 0

lake build Poincare.Global.TwoConnectors
✔ [3249/3249] Built Poincare.Global.TwoConnectors (11s)
Build completed successfully (3249 jobs).
```

The build replayed pre-existing imported-module warnings; no warning or error
was emitted for `Poincare/Global/TwoConnectors.lean`.
