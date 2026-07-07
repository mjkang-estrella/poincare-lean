# M5-glob-20 done report

## Status

Done in a new Lean file only:
`Poincare/Global/ChainRuleInput.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one_unconditional
```

## Proved

The theorem removes the explicit velocity chain-rule hypothesis left by
`SideConditions.lean`.

For the shifted chart solution
`γ t = geodesicGermChartSolution g x₀ v₀ (t₀ + t)`, it proves eventually near
`0`:

```lean
HasDerivAt
  (fun s =>
    chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2)
  (chartTransitionDeriv x₀ y₀ (γ t).1
      (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) +
    (fderiv ℝ (chartTransitionDeriv x₀ y₀) (γ t).1 (γ t).2) (γ t).2)
  t
```

This is obtained from:

- the shifted geodesic ODE supplied by `geodesicGermChartSolution_spec`;
- `geodesic_position_hasDerivAt` and `geodesic_velocity_hasDerivAt`;
- overlap-derived `ContDiffAt ℝ 2` for `chartTransition x₀ y₀`;
- `ContDiffAt.fderiv_right`, `HasFDerivAt.comp_hasDerivAt`, and
  `HasDerivAt.clm_apply`.

It then applies
`shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one`,
so the re-anchor law is now unconditional on the cutoff-one overlap zone
instead of requiring a separate `hchain` input.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/ChainRuleInput.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ChainRuleInput.lean
git diff --check -- Poincare/Global/ChainRuleInput.lean
lake build Poincare.Global.ChainRuleInput
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
35:theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one_unconditional

lake build Poincare.Global.ChainRuleInput
✔ [2840/2840] Built Poincare.Global.ChainRuleInput (12s)
Build completed successfully (2840 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
