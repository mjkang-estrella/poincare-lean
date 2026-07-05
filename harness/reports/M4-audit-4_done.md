# M4-audit-4 done / bump globalization and static witness

Read `harness/worker_contract.md` first.

## Result

The continuation error was reproduced:

```bash
lake env lean Poincare/Global/BumpExtend.lean
```

failed at `Poincare/Global/BumpExtend.lean:51` because
`ricciTraceAt_congr_of_eventuallyEq` called the local curvature congruence
lemma without the required
`CovariantDerivative.ContMDiffCovariantDerivative cov 1` instance.

The salvage direction was correct, so I kept commit `87269318` and repaired the
in-progress bridge instead of reverting it.

## Delivered names

- Cutoff field:
  - `bumpExtend`
  - `bumpExtend_closedC2TangentField`
  - `bumpExtend_eventuallyEq_extend`
  - `bumpExtend_apply_anchor`
  - `bumpExtend_covariantDerivative_eq_extend`
- Locality/bridge:
  - `ricciTraceAt_congr_of_eventuallyEq`
  - `ClosedRicciFlowExtensionRegularAt`
  - `isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt`
- Static non-vacuity witnesses:
  - `closedRicciFlowExtensionRegularAt_const`
  - `eventually_isClosedRicciFlowSolutionAt_const_and_extensionRegularAt_of_ricciFlat`

## Honest-strength assessment

The previous global-extension blocker is removed from the pointwise bridge.
`ClosedRicciFlowExtensionRegularAt` now asks only for the local
`DerivRegularAt` fact on canonical extensions, and the Ricci-flow equation is
tested on the globally admissible `bumpExtend` field.  The Ricci trace is then
transferred back by germ locality.

For static flows, the extension-regularity side is now inhabited
unconditionally for any time-constant closed metric via
`closedRicciFlowExtensionRegularAt_const`.  Under the genuine Ricci-flat trace
hypothesis, the neighborhood package consumed by the scalar-evolution chain is
inhabited by
`eventually_isClosedRicciFlowSolutionAt_const_and_extensionRegularAt_of_ricciFlat`.

The full Hamilton scalar-evolution program is still conditional on the
remaining scalar-variation predicate package: metric-flow regularity, raise-map
time derivative, delta-Gamma assemblies, double-divergence linearity, and the
contracted-Bianchi inputs.  The bump/global-extension obstruction is no longer
the blocker for the Ricci-flow-to-`timeDerivAt = -2 Ric` transfer.

## Verification

Commands run:

```bash
lake env lean Poincare/Global/BumpExtend.lean
lake env lean Poincare/Global/MetricVariation.lean
lake build Poincare.Global.MetricVariation Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
rg -n <forbidden-placeholder-pattern> Poincare/Global/BumpExtend.lean Poincare/Global/MetricVariation.lean
git diff --check
```

Result: the Lean checks and requested build succeeded.  The build emitted
existing warnings only.  The forbidden-placeholder grep found no matches in the
touched Lean files, and `git diff --check` passed.
