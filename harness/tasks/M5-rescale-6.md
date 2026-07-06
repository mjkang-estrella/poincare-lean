Read harness/worker_contract.md first and obey it strictly.

# Task M5-rescale-6: GOAL 9 — curvature-functional transport under constant rescaling

Context: `g.constSMul c hc` (`Poincare/Global/MetricRescale.lean:40`) rescales a closed metric by `c > 0`; proven transport: `constSMul_inner` (:96), `constSMul_leviCivita_apply` (:168), `constSMul_curvatureOp_extend_apply` (:226); consumer example: `constSMul_hasConstantSectionalCurvature3_one` (`Poincare/Global/SphereTheorem.lean:273`). Missing: transport of the curvature FUNCTIONALS — `ricciAt` / `scalarAt` (`Poincare/Global/Curvature.lean:155/159`), `ricciNormSqAt` (`Poincare/Global/RicciNorm.lean:74`), `tracelessRicciNormSqAt` (`RicciNorm.lean:190`). These are needed to move pinching/limit payloads across normalization.

Deliverables, in a NEW file `Poincare/Global/MetricRescaleCurvature.lean` (do NOT edit existing files incl. `Poincare.lean` — the orchestrator wires root imports at merge):

1. Explicit power-law transport under `g.constSMul c hc`, as equalities with explicit constants, for: `ricciAt` (expected: invariant), `scalarAt` (expected: `c⁻¹ *`), `ricciNormSqAt` (expected: `c⁻² *`), `tracelessRicciNormSqAt` (expected: `c⁻² *`). FIRST derive each constant on paper from the repo's ACTUAL definitions (they contract with Gram inverses in the `extend` frame — check `CovariantDerivative.scalarCurvatureAt` and the RicciNorm Gram machinery); if a derived constant differs from the expectation above, prove the DERIVED one and document the derivation in the report. Constants are sanctioned-adjustable; the "explicit power of `c`" shape is frozen.
2. Hard-frozen corollary (constant-independent), in the 3-dimensional closed context used by `SphereTheorem.lean` (its `ContMDiffCovariantDerivative` instances are automatic via `leviCivita_contMDiff`):

`theorem constSMul_pinchedLimitPayload (g : ClosedSmoothRiemannianMetric 3 M) {c : ℝ} (hc : 0 < c) (htr : ∀ x, g.tracelessRicciNormSqAt x = 0) (hpos : ∃ x, 0 < g.scalarAt x) : (∀ x, (g.constSMul c hc).tracelessRicciNormSqAt x = 0) ∧ (∃ x, 0 < (g.constSMul c hc).scalarAt x)`

3. Report `harness/reports/M5-rescale-6_done.md` (or `_blocked.md` with a decomposition plan): derivations, final names, next consumers.

State the transport laws at the generality the definitions natively allow (general `n` if free, else `n = 3`). Prefer many small proven lemmas (frame-level Gram transport first). No vacuous wrappers; every hypothesis must be used or removed.

Verify: `lake build Poincare.Global.MetricRescaleCurvature` and report the actual result. Commit your work.
