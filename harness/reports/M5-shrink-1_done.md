# M5-shrink-1 done

## Deliverables

- Added `Poincare/Global/ScalarRegularity.lean`.
- Proved `Poincare.scalarAt_mdifferentiableAt` for arbitrary `n`, with no extra hypotheses beyond the closed smooth metric and the ambient closed smooth manifold context.
- Added `Poincare/Global/PinchedLimitInterface.lean`.
- Defined `HamiltonConvergencePinchedLimit3Core`.
- Proved `hamiltonConvergencePinchedLimit3_iff_core`.
- Proved `poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition`.

## Scalar regularity route

The proof uses the existing Gram-trace chain:

1. `traceMetricVariationAt_ricci` rewrites scalar curvature as the metric trace of `ricciVariationField g`.
2. `covTensor2ExtDifferentiableAt_ricciVariationField_canonical` supplies canonical-extension differentiability of Ricci entries.
3. `traceMetricVariationAt_mdiffAt_of_covTensor2ExtDifferentiableAt` lifts those entry regularities to differentiability of the metric trace.

No dimension-3 specialization was needed.

## Verification

Command:

```bash
lake build Poincare.Global.ScalarRegularity Poincare.Global.PinchedLimitInterface
```

Result:

```text
Build completed successfully (3069 jobs).
```

The build replayed existing modules and emitted existing linter warnings in dependencies, but both new modules built successfully.
