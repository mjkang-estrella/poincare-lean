Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-3: resolve the extension-regularity gap — local vs global

Read `harness/reports/M4-audit-2_blocked.md`. The isolated gap: `ClosedRicciFlowExtensionRegularAt` requires GLOBAL `ClosedC2TangentField (extend E v)`, but `FiberBundle.extend` fields are (by construction) smooth only NEAR THE ANCHOR — global C² may be simply false for them.

Deliverables:
1. **Use-site survey** (read-only first): find EVERY theorem consuming `ClosedRicciFlowExtensionRegularAt` (grep) and determine for each whether the proof uses the extension-field regularity (a) only eventually/locally near the anchor point x (∀ᶠ y in nhds x — which is what the anchored Gram/entry machinery actually differentiates), or (b) genuinely globally. Report the table. EXPECTED: (a) everywhere — the M4 campaign's proofs are all pointwise-at-x with eventual-neighborhood expansions.
2. **If (a) — SANCTIONED WEAKENING**: redefine the bundle (deprecate-with-comment the global form) to the local/eventual form (`∀ᶠ y in nhds x, ...`-style or `ContMDiffAt`-based membership near the anchor); update the consuming theorems (mechanical hypothesis-shape change; the proofs should go through unchanged since they only used locality). Then **prove the static witness**: the local form for `extend E v` follows from the LOCAL smoothness the API exposes + the canonical instances → `closedRicciFlowExtensionRegularAt_static_ricciFlat` — the non-vacuity witness the audit demanded.
3. **If (b) somewhere**: report exactly which theorem needs globality and why; do not force.
4. Report: final honest-strength assessment update.

Standing protocols. No sorry/axiom. BUILD NOTE: patience; this touches hypothesis shapes — `lake build Poincare.Global.MetricVariation Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution` must ALL pass. Report names.
