# M5-glob-61 blocked: continuity-package conversion lands, indexed endpoint field still missing

## Status

Verified partial progress was added in the required new Lean module:

- `Poincare/Global/ContinuityPackages.lean`

No existing Lean module was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module exports the continuity-package assembly layer:

```lean
theorem Poincare.ContinuityPackages.lipschitzOnWith_of_dist_bound
theorem Poincare.ContinuityPackages.continuousOn_of_dist_bound
theorem Poincare.ContinuityPackages.normedField_lipschitzOnWith_of_norm_sub_le
theorem Poincare.ContinuityPackages.normedField_continuousOn_of_norm_sub_le
```

These are the concrete Gronwall-bound conversion facts: a uniform endpoint-field
norm bound gives `LipschitzOnWith`, hence `ContinuousOn`.

The file also exports the endpoint package constructors:

```lean
theorem Poincare.ContinuityPackages.contDiffAt_one_fderiv_of_endpoint_continuity
theorem Poincare.ContinuityPackages.source_target_fderiv_contDiffAt_one_of_endpoint_continuity
theorem Poincare.ContinuityPackages.source_target_fderiv_contDiffAt_one_of_gronwall_endpoint_bounds
```

These turn source and target endpoint-continuity packages into the canonical
`ContDiffAt ℝ 1 (fun q => fderiv ℝ e q)` facts demanded by the bridge chain.

Finally, the module feeds those Gronwall-style endpoint bounds into the
existing consumer:

```lean
theorem Poincare.ContinuityPackages
  .exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_gronwall_endpoint_bounds
```

This theorem calls
`EndpointContinuity.exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_endpoint_continuity`
and replaces its explicit `ContinuousOn sourceEndpoint sourceU` /
`ContinuousOn targetEndpoint targetU` callback assumptions by uniform
Gronwall-style bounds:

```lean
∀ q ∈ sourceU, ∀ q' ∈ sourceU,
  ‖sourceEndpoint q' - sourceEndpoint q‖ ≤ (Ks : ℝ) * dist q' q

∀ q ∈ targetU, ∀ q' ∈ targetU,
  ‖targetEndpoint q' - targetEndpoint q‖ ≤ (Kt : ℝ) * dist q' q
```

## Remaining blocking boundary

The unconditional F-transition law is still not closed because the repo still
does not export the actual neighborhood-indexed endpoint package that would
instantiate the callback for source and target.

The first missing shape is not another continuity conversion. It is the
canonical indexed third-variation endpoint field, on each side:

```lean
sourceEndpoint : E3 → E3 →L[ℝ] E3 →L[ℝ] E3
sourceU ∈ 𝓝 v
∀ q ∈ sourceU,
  HasFDerivAt (fun q' : E3 => fderiv ℝ eM q')
    (sourceEndpoint q) q
∀ q ∈ sourceU, ∀ q' ∈ sourceU,
  ‖sourceEndpoint q' - sourceEndpoint q‖ ≤ C * dist q' q
```

and identically for the target side at `roundSphereMetric3` and `L v`.

`HostedCLM.lean` now constructs a fixed hosted-family endpoint CLM, and
`OmegaGronwall.lean` proves the endpoint CLM Gronwall estimate once two endpoint
CLMs/families are supplied.  What is still missing from the public exports is
the uniform neighborhood-indexed data tying them together:

```lean
q ↦ ζ_q, Ω_q, D_q
```

with:

1. hosted third-variation families over all `q` in a source/target neighborhood;
2. fixed-time endpoint CLMs `D_q` produced by `HostedCLM`;
3. the `TransitionLands` derivative representation identifying the projected
   `D_q` with the derivative of `q ↦ fderiv ℝ e q`;
4. a uniform base-curve distance estimate strong enough to instantiate
   `OmegaGronwall` with `δnorm = dist q' q`.

Without that indexed producer/identification package, the new conversion theorem
cannot be instantiated to eliminate the final callback, so the requested
unconditional F-transition law remains blocked at this precise exported-data
boundary.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ContinuityPackages.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ContinuityPackages.lean
git diff --check -- Poincare/Global/ContinuityPackages.lean
lake build Poincare.Global.ContinuityPackages
```

Actual result:

```text
forbidden-token scan: no matches

top-level declaration scan:
22:theorem lipschitzOnWith_of_dist_bound
37:theorem continuousOn_of_dist_bound
46:theorem normedField_lipschitzOnWith_of_norm_sub_le
57:theorem normedField_continuousOn_of_norm_sub_le
70:theorem contDiffAt_one_fderiv_of_endpoint_continuity
86:theorem source_target_fderiv_contDiffAt_one_of_endpoint_continuity
109:theorem source_target_fderiv_contDiffAt_one_of_gronwall_endpoint_bounds
154:theorem exists_cartanChartMap_christoffelAt_F_transition_law_of_produced_expChart_gronwall_endpoint_bounds

git diff --check -- Poincare/Global/ContinuityPackages.lean
exit status 0

lake build Poincare.Global.ContinuityPackages
✔ [3248/3248] Built Poincare.Global.ContinuityPackages (16s)
Build completed successfully (3248 jobs).
```

The build replayed pre-existing imported-module warnings; no error remained in
`Poincare/Global/ContinuityPackages.lean`.
