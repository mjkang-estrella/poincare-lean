# M5-glob-67 blocked: centered selector pieces assembled, indexed producer still missing

## Status

Added the required new Lean module:

- `Poincare/Global/SelectorAssembly.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports two non-vacuous assembly theorems:

- `SelectorAssembly.exists_centered_hosted_endpoint_hasFDerivAt`
- `SelectorAssembly.exists_centered_endpoint_gronwall_bound`

The first theorem feeds
`CenteredMembership.exists_rescaled_hosted_thirdVariation_centered_membership_clm_package`
into
`GeodesicTransport.chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually`.
For a fixed continuous hosted doubly-augmented base, it selects the centered
all-direction `Ω`, selects the endpoint `HostedCLMPackage` at any hosted time
inside the centered interval, and proves the endpoint `HasFDerivAt` conclusion
from the standard base and perturbation hypotheses.

The second theorem feeds two centered all-direction `Ω` packages into
`TheSelector.selected_endpoint_gronwall_bound`.  It selects endpoint CLMs on
both sides at the requested endpoint time and proves the transferred Gronwall
bound once the two hosted base curves satisfy the required membership and
distance hypotheses.

## Remaining blocking boundary

The requested unconditional F-transition law is not yet closed because the
public exports still do not produce the neighborhood-indexed source/target
endpoint package consumed by `IndexedSelection`.

The single resisting shape is this package, at each punctured normal vector:

```lean
∃ sourceEndpoint :
    E3 → E3 →L[ℝ] E3 →L[ℝ] E3,
  ∃ targetEndpoint :
    E3 → E3 →L[ℝ] E3 →L[ℝ] E3,
  ∃ sourceU : Set E3,
  ∃ targetU : Set E3,
  ∃ Ks Kt : ℝ≥0,
    sourceU ∈ 𝓝 v ∧
      (∀ q ∈ sourceU, ∀ q' ∈ sourceU,
        ‖sourceEndpoint q' - sourceEndpoint q‖ ≤
          (Ks : ℝ) * dist q' q) ∧
      (∀ q ∈ sourceU,
        HasFDerivAt
          (fun q' : E3 => fderiv ℝ eM q')
          (sourceEndpoint q) q) ∧
      targetU ∈ 𝓝 (L v) ∧
      (∀ q ∈ targetU, ∀ q' ∈ targetU,
        ‖targetEndpoint q' - targetEndpoint q‖ ≤
          (Kt : ℝ) * dist q' q) ∧
      ∀ q ∈ targetU,
        HasFDerivAt
          (fun q' : E3 => fderiv ℝ eS q')
          (targetEndpoint q) q
```

`SelectorAssembly.lean` proves the two centered pieces needed inside this
package, but there is still no exported theorem that constructs, on actual
source and sphere neighborhoods, the indexed hosted curves `q ↦ ζ_q`, centered
families `q ↦ Ω_q`, selected CLMs `q ↦ D_q`, the base/perturbation hypotheses
for the derivative theorem, and the cross-point ζ membership/distance
hypotheses needed by the Gronwall theorem.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/SelectorAssembly.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def|abbrev)\b|^omit .* in$' Poincare/Global/SelectorAssembly.lean
git diff --check -- Poincare/Global/SelectorAssembly.lean
lake build Poincare.Global.SelectorAssembly
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
37:omit [T2Space M] in
43:theorem exists_centered_hosted_endpoint_hasFDerivAt
186:omit [T2Space M] in
192:theorem exists_centered_endpoint_gronwall_bound

git diff --check -- Poincare/Global/SelectorAssembly.lean
exit status 0

lake build Poincare.Global.SelectorAssembly
✔ [3253/3253] Built Poincare.Global.SelectorAssembly (12s)
Build completed successfully (3253 jobs).
```

The build replayed pre-existing imported-module warnings; no warning or error
was emitted for `Poincare/Global/SelectorAssembly.lean`.
