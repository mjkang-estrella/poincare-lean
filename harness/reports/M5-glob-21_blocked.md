# M5-glob-21 blocked report

## Status

Blocked on the requested `RigidStepCompatibleWith` / chain theorem, with a
verified strict-partial theorem in the required new Lean file:

- `Poincare/Global/NaturalityCascade.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.NaturalityCascade
  .source_target_shifted_geodesicGermAt_eventuallyEq_reanchored_unconditional
```

It applies the unconditional re-anchor law from `ChainRuleInput.lean` twice:

1. to the source geodesic of a `CartanChain.ChainState g`, shifted from
   `s.anchor` to `x₁`;
2. to the aligned round-sphere target geodesic, shifted from `s.target` to
   `s.map x₁`.

The conclusion is a paired source/target eventual equality near `0`:

```lean
(fun τ => geodesicGermAt g s.anchor v₀ (t₀ + τ))
  =ᶠ[𝓝 0]
geodesicGermAt g x₁
  (reanchoredVelocity g s.anchor x₁ v₀ t₀)
```

and

```lean
(fun τ =>
  geodesicGermAt roundSphereMetric3 s.target (s.alignment v₀) (t₀ + τ))
  =ᶠ[𝓝 0]
geodesicGermAt roundSphereMetric3 (s.map x₁)
  (reanchoredVelocity roundSphereMetric3 s.target (s.map x₁)
    (s.alignment v₀) t₀)
```

This removes the old velocity-chain-rule side condition from the paired
source/target re-anchoring surface.

## Blocking boundary

This still does not produce
`InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁`.

The remaining gap is the upgrade from one-dimensional shifted geodesic germs
to the full common-source `EqOn`:

```lean
EqOn s.germ
  (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ
  (s.germ.source ∩
    (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source)
```

The current interfaces do not provide a theorem showing that every point of
this common normal-coordinate overlap is covered by shifted old geodesic rays
whose target rays satisfy the matching endpoint hypothesis, nor a theorem
identifying the target-side reanchored velocity from the paired reanchor law
with the explicitly supplied induced alignment `L₁`.  Without that open-set
re-centering theorem, the proven consumers in `OffAnchorNaturality.lean`,
`ExpNaturality.lean`, and `CartanChain.lean` cannot be fired noncircularly.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/NaturalityCascade.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/NaturalityCascade.lean
git diff --check -- Poincare/Global/NaturalityCascade.lean
lake build Poincare.Global.NaturalityCascade
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
44:theorem source_target_shifted_geodesicGermAt_eventuallyEq_reanchored_unconditional

lake build Poincare.Global.NaturalityCascade
✔ [3004/3004] Built Poincare.Global.NaturalityCascade (2.4s)
Build completed successfully (3004 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
