# Chart and metric migration shapes, attempt a01

Read-only inspection of clean aligned `757d0dda020470783afef7b0edfe1601da00274c`. Both inspected modules are byte-identical to original production `55e4859b54acb9044d7966a12df7a12afa8b52fd`. The third-layer source log/result records this same source HEAD, terminal exit 1, duration 49.22 seconds. No process was started, restarted, stopped or otherwise controlled; no Lean invocation, build, source edit or helper agent was used here.

This enables retained-root compatibility and the separately verified smooth-Poincare adapter. It constructs no new original core existence input. The final endpoint and root acceptance remain separate gates.

## Disjoint metric proof scope

`Poincare/Global/SmoothInitialMetricLocalPullback.lean` has one recorded failure: line 56, inside `Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates`. After `simpa [eHom,eR] using hx`, actual hx is membership in `(chartAt (ClosedSmoothModel 3) p).source`, while Lean expects membership in the locally bound tangent trivialization's `e.baseSet`.

Current Mathlib still proves `TangentBundle.trivializationAt_baseSet` by rfl at VectorBundle/Tangent.lean:223, and `Bundle.Trivialization.baseSet_continuousLinearMap` by rfl at Topology/VectorBundle/Hom.lean:248, with Hom base set the intersection of the two base sets. The mismatch is local proof elaboration; it does not justify changing the coordinate domain or adding chart-source assumptions.

Smallest initial permitted edit is only the `localEuclideanInner_coordinates` proof body. Freeze exact original types/universe order for the module's four declarations: `localEuclideanInner_symm`, `localEuclideanInner_pos`, `localEuclideanInner_coordinates`, and `localEuclideanInner_contMDiffOn`, all in the namespace above. Preserve every other byte, including domain baseSet hypotheses, smooth ENat.top regularity, nested bilinear trivialization expression, canonical innerSL, imports and the other three proofs. The actual computational `SmoothInitialMetricDefinitions.localEuclideanInner` must remain byte-identical in its owning module: true tangent trivialization, continuousLinearMapAt, canonical Euclidean inner product, and both pullback slots. This scope needs no signature or operator normalization.

## Chart API and separate inverse-chart proof scope

`Poincare/ChartIdentification.lean:65` independently fails in `mpullbackWithin_extChartAt_symm_self`, specifically the proof-local h2 inverse-chart derivative identity. Actual hcomp is an equality of CLMs from `TangentSpace I x`, containing inverse-chart derivative composed with `id` on that fiber. The required equality is from the self-model tangent fiber at the chart image to the actual target tangent fiber, against `id` on E. The displayed composition and nominal fiber/dictionary differences must be proved away within this theorem body; do not change actual chart, pullback, inverse, norm or connection definitions or the theorem's result.

Other recorded errors reject scalar functions where current `extDerivFun` expects explicit model I. There are 17 applied derivative occurrences and three proof unfolding identifiers. First generic/model-I section contains four applications, lines 88,110,170,211, requiring the existing I; all thirteen applications in the real DerivationIdentity section require its existing I'. The three `simp only [extDerivFun,...]` identifiers at 98,150,385 require the current unfolding name if that rename is chosen. Public theorem names containing extDerivFun must stay unchanged.

Normalize actual `extDerivFun f` to `mvfderiv I f`, or `mvfderiv I' f` in the real section, including both layers of nested directional derivatives. Seven theorem signatures contain these operators; five application occurrences and the three unfoldings are inside existing proof bodies. This is reviewed interface/API normalization, not solely a proof-body edit. Before freezing the current literals, verify old/new shared-operator formulas by rfl for arbitrary nontrivially normed scalar field K, model I, charted M and scalar f : M -> K:

```lean
fun x => (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
  (mfderiv I 𝓘(K, K) f x)
```

Prior real-scalar API evidence covers the real section, but does not replace the generic-field check. Preserve the original scalar type and supplied model; never substitute ordinary fderiv on an arbitrary manifold.

Freeze all ten primary public types/universe orders and all ten existing `_eq` companions: `mlieBracket_apply_chart`, `mpullbackWithin_extChartAt_symm_self`, `extDerivFun_apply_chart`, `extDerivFun_apply_fixed_chart`, `isLocallyConstant_of_extDerivFun_eq_zero`, `extDerivFun_apply_mlieBracket_chart`, `mpullback_extChartAt_symm_apply`, `extDerivFun_section_eventually_chart`, `extDerivFun_extDerivFun_chart`, and `extDerivFun_apply_mlieBracket`.

Retain exact chart-source/target and range-I restrictions, actual mpullback/mfderiv/inverse operators and field directions. Keep arbitrary generic K in the first section; keep boundarylessness and precise existing IsManifold 1 omissions/hypotheses. The real derivation section retains IsManifold I' 2 N, Boundaryless I' and CompleteSpace E', plus original pointwise C2/scalar and MDiff field premises. No stronger smoothness, compactness, metric, completeness or dimension premise may be introduced. This module contains theorem proofs, not a new metric or connection data construction.

## Exact next scoped gates

Use separate file leases for metric-local-pullback and ChartIdentification. For the metric task, first direct-check the repaired file, then its scoped build, four rigid type/axiom/safety checks and whole-source body guard. For ChartIdentification, stage the reviewed derivative normalization under the same single file lease, record fresh direct Lean diagnostics, and allow only the known inverse-chart theorem proof body or separately reviewed bodies exposed by that fresh check. Keep all other bytes intact modulo the exact reviewed API spelling changes.

Initial compiler commands are `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/SmoothInitialMetricLocalPullback.lean` and `LEAN_NUM_THREADS=1 lake env lean Poincare/ChartIdentification.lean`. Final focused targets are `Poincare.Global.SmoothInitialMetricLocalPullback` and `Poincare.ChartIdentification`, with the exact frozen declaration/universe, permitted-axiom/unsafe/partial, source/operator-normalization, token and diff gates. No new context pins, source patches or proof acceptance are supplied by this inventory.
