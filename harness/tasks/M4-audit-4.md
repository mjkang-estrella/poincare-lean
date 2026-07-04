Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-4: bump-function globalization → the static witness

Read `harness/reports/M4-audit-3_blocked.md`. ORCHESTRATOR RULING: adopt its option 2 via the standard cutoff construction — do NOT change the flow interface.

The construction: `extend E v` is C² near its anchor x. Take a smooth bump function χ (Mathlib: `SmoothBumpFunction I x` on manifolds — exists on any smooth manifold; closed manifolds are paracompact/T2, instances on main) supported inside the neighborhood where extend is C², with χ ≡ 1 near x. Then `χ • extend E v` (pointwise scalar multiple, extended by zero outside the support) is a GLOBAL C² tangent field agreeing with `extend E v` on a neighborhood of x.

Deliverables (each its own commit):
1. **The cutoff field**: `def bumpExtend E v x : (y : M) → TM y`-shape + `ClosedC2TangentField (bumpExtend ...)` (smoothness: product of smooth bump and locally-C² field, zero-extension smooth since χ vanishes on a neighborhood of the support boundary — Mathlib's `SmoothBumpFunction` lemmas + `contMDiff_of_locally` patterns) + `bumpExtend =ᶠ[nhds x] extend E v` + agreement of derivatives at x.
2. **Transfer the bridge**: rerun `isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt` with the test field `bumpExtend` (globally admissible by 1) — the conclusion at x is unchanged since `DerivRegularAt`/`ricciTraceAt`/`timeDerivAt` are local and the fields agree near x (the eventual-equality congruence lemmas on main). Deliver the bridge with NO global-extend hypothesis.
3. **The static witness**: with 2, complete `closedRicciFlowExtensionRegularAt`-consumer chain for the static Ricci-flat flow → the non-vacuity witness (`hamilton_*` chain hypotheses inhabited for the static flow — as far as the chain reaches in budget; the bridge itself is the critical unlock).
4. Report: updated honest-strength assessment.

Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.MetricVariation Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
