Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-15: differentiated compatibility — the transported field is compatible

Context: `harness/reports/M5-glob-14_blocked.md` (READ FIRST). PROVEN: the metric pullback law `G¹(σz)(Dσu, Dσw) = G⁰(z)(u,w)` on the cutoff-one zone (`TransportedCompatibility.lean`); transported torsion-freeness (`TransitionLaw.lean`); the sign pin (`KoszulNaturality.lean`). THIS TASK: DIFFERENTIATE the pullback law along a direction `e`: LHS' = (∂G¹ along Dσe)(Dσu, Dσw) + G¹(D²σ(e,u), Dσw) + G¹(Dσu, D²σ(e,w)); RHS' = (∂G⁰ along e)(u,w); apply the SOURCE compatibility identity (`chartChristoffelField_pairing_eq_blendedChartMetric`, `GeodesicSpeed.lean` — READ its exact form: ∂G in terms of Γ-pairings) on the RHS; rearrange: the TARGET ∂G¹ equals the transported-Γ pairings (the minus-sign transported field absorbing the D²σ terms) — i.e. THE TRANSPORTED FIELD SATISFIES THE TARGET COMPATIBILITY IDENTITY. This is calculus + the proven identities — derive carefully on paper first (the sign pin guards the arrangement). Then (if room): feed `LeviCivitaUniqueness.lean` (transported = target Christoffel) → the transition law → the reanchor chain. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-15_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/DifferentiatedCompat.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.DifferentiatedCompat` and report the actual result. Commit your work.
