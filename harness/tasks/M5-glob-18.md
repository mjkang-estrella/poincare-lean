Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-18: LC uniqueness fires — THE TRANSITION LAW

Context: `harness/reports/M5-glob-17_done.md` (READ FIRST). THE FULL CHAIN IS FED: concrete `hdiff` (`HdiffInstantiate.lean`) → the algebraic step (`DifferentiatedCompat.lean` — the transported field satisfies the target Koszul pairing) + transported torsion-freeness (`TransitionLaw.lean`). THE UNIQUENESS: `LeviCivitaUniqueness.lean` (READ its exact statement and hypothesis shapes): two fields satisfying the Koszul pairing identity + torsion-freeness for the SAME chart metric are EQUAL — apply to the transported field and the target `chartChristoffelField` (which satisfies its own compatibility `chartChristoffelField_pairing_eq_blendedChartMetric` + symmetry) ⟹ 🎯 THE TRANSITION LAW: `chartChristoffelField g y₀ (σ z) (Dσ u) (Dσ w) = Dσ(chartChristoffelField g x₀ z u w) − D²σ(z)(u,w)`-shaped, on the cutoff-one overlap zone. THEN: feed the velocity-component form to `ChristoffelTransition.lean`'s bridge → `ReanchorLawFinal.lean`'s assembly → THE REANCHOR LAW → `OffAnchorNaturality/ExpNaturality` → `RigidStepCompatibleWith` → THE CHAIN FIRES (`CartanChain` along subdivisions). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-18_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/TransitionLawFires.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.TransitionLawFires` and report the actual result. Commit your work.
