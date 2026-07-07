Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-16: puncture the quantifier — the consistent source expansion

Context: `harness/reports/M5-rigid-15_blocked.md` + the PROVED obstruction `CartanSourceExpansion.not_weightedSourceEndpointExpansion_zero` (`CartanSourceExpansion.lean`): rigid-14's `WeightedSourceEndpointExpansion g x₀ v κ` is INCONSISTENT at `v = 0` (the scaled normal vector collapses). THE RESHAPE (sanctioned; ADDITIVE edits to `CartanLocalIsometry.lean`/`CartanExpansionBridge.lean` only — new defs/theorems, no changes to existing statements): (1) a PUNCTURED expansion predicate quantified over `v ≠ 0` in the ball (same fields otherwise); (2) reprove the corrected local-isometry consumer against: punctured expansion (for `v ≠ 0`) + the ANCHOR theorem (`CartanIsometryFinal.lean`'s unconditional anchor local isometry — covers `v = 0`) — a case split; (3) check whether the TARGET-side proof (rigid-14's, unconditional) already factors through the punctured form (it should — the sphere computation at `v ≠ 0`); restate its punctured version.

Then: (4) THE SOURCE PUNCTURED EXPANSION for constant-curvature-1 `g` from the interval facts (the Jacobi-pairing route per rigid-15's task context — now consistent, since `v ≠ 0` gives honest radial direction); (5) 🎯 THE UNCONDITIONAL CORRECTED LOCAL ISOMETRY.

Deliverables in a NEW file `Poincare/Global/CartanPunctured.lean` (+ sanctioned additive edits). Strict-partial: (1)-(3) alone are valuable; ONE isolated statement max. Report `harness/reports/M5-rigid-16_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge Poincare.Global.CartanPunctured` (ALL must pass) and report the actual result. Commit your work.
