# M5-glob-4 blocked report

## Delivered files

- `Poincare/Global/IsometryConsumers.lean`
- `harness/reports/M5-glob-4_blocked.md`

No existing Lean files or `Poincare.lean` were edited.

## Verified Lean payload

`IsometryConsumers.lean` imports the completed rigidity theorem and the staged
globalization consumers, then proves:

- `Poincare.IsometryConsumers.exists_cartanChartMap_ift_partialHomeomorph_on_punctured_ball`

This is the direct inverse-function-theorem consumer of
`RigidityComplete.cartanMap_isLocalIsometry`.  For every nonzero vector in the
shrunk normal ball it packages the derivative
`CartanLocalIsometry.cartanChartDifferential L A B` as the continuous linear
equivalence `(A.symm.trans L.toContinuousLinearEquiv).trans B`, applies
`HasStrictFDerivAt.toOpenPartialHomeomorph` to the chart-level Cartan map, and
retains the full chart-metric pullback identity through that equivalence.

This gives the requested strict-partial local homeomorphism at chart level:
the returned `OpenPartialHomeomorph E3 E3` coerces to
`CartanDifferential.cartanChartMap g x0 p0 L`, and the indicated source
exponential coordinate lies in its source.

## Blocking boundary

The theorem above does not yet discharge the `CartanContinuation`/`CartanChain`
`EqOn` surface.  Those consumers require equality of the manifold-level Cartan
`OpenPartialHomeomorph`s on the whole common source:

```lean
CartanChain.ChainState.RigidStepCompatible s x1
```

The completed local-isometry theorem supplies local chart partial
homeomorphisms and pullback identities pointwise.  It does not by itself prove
the missing germ-uniqueness step that promotes matching local isometry data to
`EqOn` on the common source, nor does it identify the arbitrary re-anchored
`Classical.choice` tangent alignment in `ChainState.next` with the differential
action induced by the previous germ at the re-anchor.  The old glob-3 blocker
therefore remains the exact next boundary: prove a non-vacuous local-isometry
determinacy/source-overlap theorem yielding `RigidStepCompatible` for a
re-anchored step.  Once that is available, `CartanContinuation.twoStep_*` and
`CartanChain.chain_step_restr_eqOnSource` consume it directly.

## Verification

Command run:

```bash
lake build Poincare.Global.IsometryConsumers
```

Actual result:

```text
✔ [3225/3225] Built Poincare.Global.IsometryConsumers (2.8s)
Build completed successfully (3225 jobs).
```
