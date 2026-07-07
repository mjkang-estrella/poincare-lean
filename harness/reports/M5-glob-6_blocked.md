# M5-glob-6 blocked report

## Delivered files

- `Poincare/Global/InducedAlignment.lean`
- `harness/reports/M5-glob-6_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`InducedAlignment.lean` imports the germ-determinacy, chart-transition metric
transport, and local-isometry consumer interfaces, then adds the non-arbitrary
induced-alignment surface:

- `Poincare.InducedAlignment.continuousLinearEquivOfInvertible`
- `Poincare.InducedAlignment.inducedTangentAlignmentOfChartPullback`
- `Poincare.InducedAlignment.CompatibleStep.nextWithAlignment`
- `Poincare.InducedAlignment.CompatibleStep.RigidStepCompatibleWith`

The main constructor proves a genuine `CartanMap.TangentAlignment g x₁ p₁`
from:

1. source and target chart-overlap membership for the new anchors;
2. coordinate identities identifying the old source/target chart coordinates
   with the old exponential-chart point;
3. the carried chart-metric pullback identity for
   `CartanLocalIsometry.cartanChartDifferential L₀ A B`.

The proof transports the source anchor metric from the `x₁` chart to the old
`x₀` chart, applies the old Cartan differential pullback identity, and then
transports the target metric back from the old `p₀` chart to the new `p₁`
chart.  The resulting linear equivalence is

```lean
(sourceTransition.trans oldD).trans targetTransition.symm
```

where `oldD = (A.symm.trans L₀.toContinuousLinearEquiv).trans B`, i.e. the
equivalence form of `cartanChartDifferential L₀ A B`.

The compatible-step definitions also remove the arbitrary
`Classical.choice` from `CartanChain.ChainState.next`: a successor state is
re-anchored with an explicitly supplied alignment, intended to be the induced
alignment above.

## Blocking boundary

The full requested compatible-chain step is still not provable from the current
interfaces.  `GermDeterminacy.cartanGerm_determinacy_of_tangentAlignment_apply_eq`
compares two same-anchor Cartan germs once both are already expressed at
`x₁` with the same target and tangent action.  The missing non-vacuous theorem
is the re-centering statement:

```lean
EqOn s.germ
  (CartanMap.openPartialHomeomorph g x₁ (s.map x₁) inducedAlignment)
  (s.germ.source ∩
    (CartanMap.openPartialHomeomorph g x₁ (s.map x₁) inducedAlignment).source)
```

That is, the old Cartan germ must first be identified on a strict overlap with
the same-anchor Cartan germ determined by the induced differential at `x₁`.
Without this re-centering/source-overlap theorem, applying `GermDeterminacy`
directly would only compare the induced re-anchored germ with itself, not with
the old germ.  Filling that gap remains the next required step before
`RigidStepCompatibleWith` can be proved by construction and consumed along
subdivisions.

## Verification

Command run:

```bash
lake build Poincare.Global.InducedAlignment
```

Actual result:

```text
⚠ [3229/3229] Built Poincare.Global.InducedAlignment (4.0s)
Build completed successfully (3229 jobs).
```

Additional contract checks:

```bash
rg -n "\\b(sorry|admit|axiom|native_decide)\\b" Poincare/Global/InducedAlignment.lean
git diff --check
```

Actual result: no matches from `rg`; `git diff --check` exited successfully.
