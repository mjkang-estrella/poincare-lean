Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-13: the minus-sign transition law — LC uniqueness, sign-certain

Context: `harness/reports/M5-glob-12_blocked.md` (READ FIRST — the PIN: for `σ z = z + z²`, correction `B = 2`, compatible target value `−2`; the MINUS-sign transition is TRUE under the repo's `γ'' = −Γ` convention; the exported-API blockers listed). PROVEN: the sign pin (`KoszulNaturality.lean`); the bridge consuming the transition (`ChristoffelTransition.lean`). THE ABSTRACT LAW (minus-sign form as pinned): `Γ¹(σ x)(Dσ u, Dσ w) = Dσ(Γ⁰(x)(u,w)) − D²σ(x)(u,w)`-shaped (MATCH the pin exactly). THE LC-UNIQUENESS ROUTE: define the transported field `Γ̃(y)(a,b) := Dσ(Γ⁰(σ⁻¹y)(Dσ⁻¹a, Dσ⁻¹b)) − D²σ(…)`-shaped; show `Γ̃` is METRIC-COMPATIBLE (the target chart metric is the pullback of the source one — its derivative transports via the chain rule; the compatibility identity `chartChristoffelField_pairing_eq_blendedChartMetric`-shaped transports) and TORSION-FREE (symmetry of `Γ⁰` + `D²σ` symmetry `ContDiff.isSymmSndFDerivAt`); invoke `LeviCivitaUniqueness.lean`'s uniqueness (READ its exact hypothesis shapes — supply each) ⟹ `Γ̃ = Γ¹`. Feed the bridge → the reanchor law → naturality → `RigidStepCompatibleWith` → THE CHAIN. Strict-partial (compatibility and torsion-freeness are each standalone deliverables); ONE isolated statement max. Report `harness/reports/M5-glob-13_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TransitionLaw.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TransitionLaw` and report the actual result. Commit your work.
