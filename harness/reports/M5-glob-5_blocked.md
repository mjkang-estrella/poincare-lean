# M5-glob-5 blocked report

## Delivered files

- `Poincare/Global/GermDeterminacy.lean`
- `harness/reports/M5-glob-5_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`GermDeterminacy.lean` imports the Cartan chain interface and the normal-coordinate
conjugation theorem, then proves one isolated statement:

- `Poincare.GermDeterminacy.cartanGerm_determinacy_of_tangentAlignment_apply_eq`

For two same-anchor Cartan germs with the same target value and pointwise-equal
underlying tangent-alignment action, the theorem proves:

1. the chart Cartan maps agree on the explicit exponential-chart overlap
   obtained by mapping the common source vectors through the source exponential
   partial homeomorphism; this proof uses
   `CartanNormalCoords.expChart_symm_cartanChartMap_expChart_eq_tangentAlignment`
   to read both conjugated maps as the same linear action;
2. the corresponding Cartan `OpenPartialHomeomorph`s agree on their common
   strict source.

This discharges the same-anchor "conjugation makes the maps linear" determinacy
surface without adding any `sorry`, axioms, `native_decide`, vacuous
certificates, or new structures.

## Blocking boundary

The requested `CartanChain.ChainState.RigidStepCompatible s x₁` for
`s.next x₁` still does not follow from the current interfaces.  The new theorem
requires both Cartan germs to be expressed at the same anchor and target, with
an identified tangent-alignment action.  In the chain step, the first germ is
anchored at `s.anchor`, while the successor is anchored at `x₁` and uses the
arbitrary

```lean
Classical.choice
  (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := x₁) (p₀ := s.map x₁))
```

from `CartanChain.ChainState.next`.

There is still no theorem recentering the old germ at `x₁` in exponential
coordinates and identifying its induced differential action with that chosen
alignment.  Without that non-vacuous identification, producing
`RigidStepCompatible` would amount to assuming the exact `EqOn` surface that
`CartanContinuation.twoStep_*` already consumes.

## Verification

Command run:

```bash
lake build Poincare.Global.GermDeterminacy
```

Actual result:

```text
✔ [3151/3151] Built Poincare.Global.GermDeterminacy (2.1s)
Build completed successfully (3151 jobs).
```

Additional contract check:

```bash
rg -n "\\b(sorry|admit|axiom|native_decide)\\b" Poincare/Global/GermDeterminacy.lean
```

Actual result: no matches.
