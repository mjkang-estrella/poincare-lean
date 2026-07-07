Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-6: the induced alignment — the compatible chain step

Context: `harness/reports/M5-glob-5_blocked.md` (READ FIRST). PROVEN: germ determinacy on overlaps given equal alignments (`GermDeterminacy.lean`). THE STRUCTURAL GAP: `CartanChain.ChainState.next` re-anchors with a `Classical.choice` alignment — arbitrary, not the one INDUCED by the old germ. THE FIX: (1) THE INDUCED ALIGNMENT: the old germ's differential at the new anchor `x₁` IS a tangent alignment — its metric-intertwining property is EXACTLY the proven pullback identity evaluated at `x₁` (`RigidityComplete.cartanMap_isLocalIsometry`'s conclusion + `IsometryConsumers.lean`'s carried pullback) — CONSTRUCT `TangentAlignment g x₁ (Φ x₁)`-shaped from the differential `cartanChartDifferential L A B`-composed-with-charts (READ `CartanMap.TangentAlignment`'s fields — supply each from the pullback/derivative data); (2) THE COMPATIBLE STEP: a chain-step variant (NEW definitions in the new file — do NOT edit `CartanChain.lean`) that re-anchors WITH the induced alignment — then `RigidStepCompatible` holds BY CONSTRUCTION (the germ agreement is `GermDeterminacy`'s theorem with `L₁ = L₂ = induced`); (3) the chain fires along subdivisions (`CartanChain`'s iteration consumed via the compatible steps) → toward the global `Φ`. Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-glob-6_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/InducedAlignment.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.InducedAlignment` and report the actual result. Commit your work.
