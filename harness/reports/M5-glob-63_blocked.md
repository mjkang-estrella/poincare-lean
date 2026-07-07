# M5-glob-63 blocked: selector surface verified, global cross-point producer still missing

## Status

Added the required new Lean module:

- `Poincare/Global/TheSelector.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports the selector-level surface that is currently justified
by public theorem statements:

- `TheSelector.hostedDoublyAugmentedBase`
- `TheSelector.selectedZeta`
- `TheSelector.OmegaPackage`
- `TheSelector.exists_omegaPackage`
- `TheSelector.selectedOmegaPackage`
- `TheSelector.selectedOmegaEpsilon`
- `TheSelector.selectedOmegaBound`
- `TheSelector.selectedOmegaRadius`
- `TheSelector.selectedOmega`
- `TheSelector.selectedOmegaAt`
- `TheSelector.selectedOmegaEpsilon_pos`
- `TheSelector.selectedOmegaRadius_pos`
- `TheSelector.selectedOmega_spec`
- `TheSelector.HostedCLMPackage`
- `TheSelector.exists_hostedCLMPackage`
- `TheSelector.selectedHostedCLM`
- `TheSelector.selectedHostedCLM_endpoint_eq`
- `TheSelector.selected_endpoint_gronwall_bound`

The key choices are noncomputable `Classical.choice` selectors over the
existing exports:

- `selectedOmega*` chooses from
  `GeodesicTransport.exists_hosted_thirdVariation_solution_family_on_paired_base`.
- `selectedHostedCLM` chooses from
  `GeodesicTransport.chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc`.
- `selected_endpoint_gronwall_bound` is the direct transfer into
  `GeodesicTransport.chartChristoffel_thirdVariation_endpoint_gronwall_bound`
  once the selected endpoint CLMs have exact endpoint equalities.

## Remaining blocking boundary

The full task asks for the unconditional neighborhood selector

```lean
q ↦ ζ_q, Ω_q, D_q
```

with the cross-point Gronwall bound for the selected `D_q, D_q'`.  The current
public exports still do not supply two required links.

First, the hosted doubly-augmented base `ζ_q` needs a selected
second-variation family `Ξ` at each point.  `UniformFlowExport` exports the
base and linearized first-variation packages, and `SecondDischarge` consumes a
supplied `Ξ`; but there is no public all-direction second-variation family
selector analogous to the linearized-family selector.  `SecondVariation`
exports a PL package, not a neighborhood-indexed selected `Ξ_q` with the
facts needed to build `ζ_q`.

Second, the `Ω_q` chosen by
`OmegaGronwall.exists_hosted_thirdVariation_solution_family_on_paired_base`
is local in the perturbation:

```lean
∀ h ∈ closedBall 0 r, ...
```

`HostedCLM.chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc`
requires stronger all-perturbation hypotheses:

```lean
∀ η, Ω η 0 = η
∀ η, ∀ t, HasDerivWithinAt ...
∀ η, ∀ t, Ω η t ∈ closedBall η a
```

plus add/smul closed-ball membership.  Those facts are not exported by
`OmegaGronwall`'s selected local family, so the requested `D_q` cannot be
constructed from that `Ω_q` without an extra strengthening or rescaling bridge.

Because of those gaps, the final requested uniqueness transfer cannot yet be
proved for the actual selected objects.  The generic uniqueness lemma
`linearODE_solution_uniqueOn_Icc` is present, but using it here requires the
same PL package and closed-ball membership for both choices; those hypotheses
are exactly the missing public bridge between the local `Ω_q` choice and the
stronger `HostedCLM` endpoint-CLM construction.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/TheSelector.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b|^omit .* in$' Poincare/Global/TheSelector.lean
git diff --check -- Poincare/Global/TheSelector.lean
lake build Poincare.Global.TheSelector
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
40:def hostedDoublyAugmentedBase
46:def selectedZeta
52:theorem selectedZeta_apply
59:def OmegaPackage
80:omit [T2Space M] in
81:theorem exists_omegaPackage
93:def selectedOmegaPackage
101:def selectedOmegaEpsilon
108:def selectedOmegaBound
115:def selectedOmegaRadius
122:def selectedOmega
130:def selectedOmegaAt
137:omit [T2Space M] in
138:theorem selectedOmegaEpsilon_pos
145:omit [T2Space M] in
146:theorem selectedOmegaRadius_pos
153:omit [T2Space M] in
154:theorem selectedOmega_spec
180:def HostedCLMPackage
187:omit [T2Space M] in
188:theorem exists_hostedCLMPackage
234:def selectedHostedCLM
272:omit [T2Space M] in
273:theorem selectedHostedCLM_endpoint_eq
318:omit [T2Space M] in
319:theorem selected_endpoint_gronwall_bound

git diff --check -- Poincare/Global/TheSelector.lean
exit status 0

lake build Poincare.Global.TheSelector
✔ [3248/3248] Built Poincare.Global.TheSelector (3.0s)
Build completed successfully (3248 jobs).
```

The build replayed pre-existing imported-module warnings; no warning or error
remained in `Poincare/Global/TheSelector.lean`.
