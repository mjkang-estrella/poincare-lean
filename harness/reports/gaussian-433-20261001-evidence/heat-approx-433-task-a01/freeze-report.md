# Heat approximate-identity migration freeze

Author: /root/workflow_bottlenecks, 2026-09-30 local date.
Independent mathematical blind read-back is pending and must be performed by a distinct reviewer. The contract draft contains no fabricated approval metadata.

Original declaration types were exported from the cached Lean environment at clean main 55e4859b54acb9044d7966a12df7a12afa8b52fd. The exact candidate base is 681e24e8fedf59c21b71747e90835567dc790e43 on the isolated upstream-integration-433 branch. HeatApproxIdentity source bytes are identical at those two commits. Source identities, toolchains and dependency revisions are recorded in source-identities.json; all inspected Mathlib tracked sources were clean.

## Frozen declarations

In this exact order:
1. Poincare.heatKernel_fourier_complex_eq_ofReal
2. Poincare.heatSolution_apply_swap
3. Poincare.tendsto_heatSolution_nhdsGT_zero

All three have one universe parameter u_1. The full reparsable Lean literals are in explicit-original-types.json and blind-snapshot.json. They were checked against the actual old compiled unapplied declaration types, at a rigid universe, with no unresolved metavariables. The final FrozenMigrationProbe.lean combines all three type probes and their standard foundational-axiom/transitive unsafe-or-partial dependency gates into one Lean invocation.

Numeric prettyprinting was enabled explicitly: pp.numericTypes=true. Both raw export attempts are retained. The first reparsing probe failed because prettyprinter arrows such as upward Real.pi were inferred as inappropriate coercions to integers. Only the printed representation was repaired: every Real-to-Complex coercion became explicit Complex.ofReal, and the finrank coercion gained an explicit Nat.cast-to-Complex ascription. The resulting type passed the old kernel's exact definitional-equality check. The raw original prettyprints and failed gate remain in raw-original-types.json and original-probe-a01 stdout/stderr/receipt artifacts.

The final original probe exited 0 and emitted exactly three FROZEN_CONTRACT_OK plus three AXIOM_CONTRACT_OK markers; original-probe-a02.result.json records the command, time and log hashes. No Lake build was invoked and no trusted Lean source was edited.

## Smallest permitted source scope

Only the existing proof body of Poincare.tendsto_heatSolution_nhdsGT_zero is editable. Its complete header through := by is frozen. The allowed body begins immediately after := by on original line107 and ends before end Poincare on line131. The immediate compiler failure is the final simpa on line129, so an explicit real-part/coercion simplification there is a plausible smallest repair; the entire existing final proof body is the formal lease boundary.

check-scope.py masks only that body and requires every other byte to equal frozen-base.lean. It therefore preserves all imports, namespace/variable/instance binders, all six public/private headers, the two other public proofs and all three private proofs. The baseline guard was run read-only against the isolated base and passed. frozen-headers.json contains all six exact source headers; the frozen-base bytes remain the source authority.

Do not change the Gaussian normalization, inherited inner-product norm, dimension, canonical volume, heatSolution convolution data, Fourier scale, complex Gaussian identity, real-to-complex integral bridge, time filter, Integrable premise, or ContinuousAt premise. Data/config hashes are frozen at the current 4.33 base in blind-snapshot.json, including HeatKernel, HeatKernelIntegral, lean-toolchain, lake-manifest and lakefile.

## Exact existing failure

The preserved third-layer build reports HeatApproxIdentity.lean:129:2. After simp, hreal is a Tendsto of Complex.re composed with complexified real convolution, while the goal is the Tendsto of real convolution itself. original-433-diagnostic.txt preserves the diagnostic, and diagnostic-source.json binds it to the full pre-existing build log and its receipt. That pre-existing run reported source HEAD757d0dda; this is historical compiler evidence, not a claim that the new frozen base has been freshly compiled.

## Mathematical preservation boundary

The selected declarations concern finite-dimensional real inner-product spaces in arbitrary dimension. Their volume is the canonical inner-product-space measure; the literal integral and Integrable types contain MeasureSpace.volume, with no arbitrary measure parameter. The positive-time Gaussian equality preserves the complex cpow versus real rpow bridge. The swap has no positivity/integrability premise and is an identity of totalized Bochner integrals, not convolution-existence for arbitrary data. Recovery requires integrable real f and continuity at the selected point, along the positive-time filter at zero.

This migration enables retained root integration for the frozen final target using separately verified smoothing and upstream smooth Poincare. It does not construct an independent universal Hamilton flow, limit input, or smoothing proof.

## Acceptance commands to include in the reviewed Task

- env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatApproxIdentity.lean
- env LEAN_NUM_THREADS=1 lake build Poincare.Global.HeatApproxIdentity at a serialized acceptance checkpoint, to expose only fresh candidate olean before its probe
- env LEAN_NUM_THREADS=1 lake env lean <absolute task-state path>/FrozenMigrationProbe.lean
- python3 <absolute task-state path>/check-scope.py
- rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/HeatApproxIdentity.lean
- git diff --check

The orchestrator must supply the distinct blind review, freeze the completed Task, arrange isolated ownership and fresh candidate acceptance, then decide integration. This author has not reviewed their own snapshot.

Snapshot digest: 37f5e40c413129e6563a62e0dc5d67915a126dd9c7811816eeb7c42058a2fa10
