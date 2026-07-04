# M4-audit-2 blocked / honesty update

Read `harness/worker_contract.md` first.

## What changed

Added:

```lean
closedRicciFlowExtensionRegularAt_const_of_closedC2_extend
```

in `Poincare/Global/MetricVariation.lean`.

This proves the static-flow extension-regularity bundle from the exact missing
global hypothesis:

```lean
∀ v : TM x, ClosedC2TangentField (extend E v)
```

The `DerivRegularAt` half is discharged by the existing canonical lemma
`CovariantDerivative.derivRegularAt_extend`, so the remaining gap is isolated
to global `C²` admissibility of canonical extension fields.

## Item 1 status

The requested unconditional witness

```lean
closedRicciFlowExtensionRegularAt_static_ricciFlat
```

was not proved.

Reason: `ClosedRicciFlowExtensionRegularAt` requires, for every `v : TM x`,
the global field regularity

```lean
ClosedC2TangentField (extend E v)
```

but Mathlib's canonical `extend` API supplies local smoothness at the anchor:

```lean
FiberBundle.contMDiffAt_extend'
FiberBundle.exists_contMDiffOn_extend
```

The definition of `FiberBundle.extend` uses the trivialization at the seed
point. Its smoothness is available on that trivialization's base set, not as a
global `ContMDiff` section on an arbitrary manifold. This is exactly the
global-vs-local issue flagged in `M4-audit-1_report.md`.

Static Ricci-flatness does not change this field-admissibility side condition:
it supplies the Ricci-flow PDE witness
`isClosedRicciFlowSolutionAt_const_of_ricciFlat`, but
`ClosedRicciFlowExtensionRegularAt` independently asks for global `C²`
canonical extension fields.

Other static pieces remain genuinely inhabited or reducible to existing
constant-flow lemmas:

- `MetricFlowRegularAt (fun _ => g) t0 x` via `metricFlowRegularAt_const`.
- `TimeDifferentiableAt (fun _ => g) t0 x` via `timeDifferentiableAt_const`.
- `DeltaGammaEntryDerivativeBridgeAt (fun _ => g) t0 x` via
  `deltaGammaEntryDerivativeBridgeAt_const`.
- time-variation entry regularity via
  `timeVariationExtContMDiffAt_const` and
  `timeVariationTraceEntriesExtContMDiffAt_const`.
- the static `hRaise` derivative is the constant-path proof
  `hasDerivAt_const t0 (g.metricRaiseContinuousAt x)`, but I did not add a
  top-level helper theorem because the nested continuous-linear-map normed
  instances made that API brittle and it is not the main bundle blocker.

I did not find unconditional canonical `C²` theorems for the scalar curvature,
Ricci-norm, pinching quotient, or quotient-gradient hypotheses. Existing
gradient lemmas, for example `ClosedSmoothRiemannianMetric.mdifferentiableAt_gradient`,
consume a `ContMDiffAt ... 2` scalar input; they do not themselves prove that
`scalarAt`, `ricciNormSqAt`, or `pinchingQuotientAt` are `C²`.

## Item 6 status

I did not add a positive-epsilon wrapper theorem for
`hamilton_eigenvalue_pinching_floor_preserved`.

The existing theorem is correct and intentionally valid under the exact
algebraic hypothesis it uses:

```lean
ε ≤ 1 / 3
```

Adding a wrapper with an extra `0 < ε` premise would leave that premise unused
in the proof of the same conclusion, which conflicts with the worker-contract
rule that every hypothesis must be used or removed. Downstream theorems that
need positive epsilon should require it at the point where positivity enters
the reaction or admissible-delta argument; `hamilton_pinching_improvement`
already does this with `hεpos`.

## Updated honest-strength assessment

The M4 headline theorems remain meaningful, but the strongest non-vacuity
claim from the audit is still not fully discharged. The new constructor shows
that `ClosedRicciFlowExtensionRegularAt` would be inhabited for static flows
as soon as global `C²` canonical extension fields are available. In the current
API, only the connection-regularity half is witnessed unconditionally.

So the honest assessment is:

- Static Ricci-flat flows witness the Ricci-flow PDE side.
- Static/zero time-regularity bundles are inhabited.
- The `ClosedRicciFlowExtensionRegularAt` global extension-field requirement
  remains the highest-value open gap.
- Scalar/Ricci-norm `C²` and quotient/gradient regularity are still conditional
  unless further canonical fixed-metric regularity lemmas are exposed.
- The eigenvalue floor theorem should stay unguarded unless a future theorem
  actually uses `0 < ε`.

## Verification

Final verification command:

```bash
lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation
```

Result: success, warnings only.

I also checked the directly touched module with:

```bash
lake env lean Poincare/Global/MetricVariation.lean
```

Result: success.
