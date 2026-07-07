Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-88: assemble with the enriched cascade — the isometry

Context: `harness/reports/M5-rigid-87_done.md` + `M5-rigid-86_blocked.md` (READ BOTH). THE GAP IS CLOSED: `EnrichedCascade.lean` exports `BaseCurvePackage` + `LinearizedFamilyPackage` for the SAME hosted `α` (derivative `hγ`-shape, cutoff/zone, speed fields; strict margin; both sides). THE ASSEMBLY (rigid-86's plan with the enriched exports): instantiate at the hosted datum — the enriched packages feed the base-curve hypotheses; the solutions feeds (`SolutionsFeed.lean`) give the transverse blocks; the one-sided orthogonality (`OneSidedPayload/BundleDischarge.lean`); the radial facts (`RayIdentification/SpeedReconcile.lean`); speeds (`SpeedPackage.lean`) — apply the consumer chain (`BundleDischarge` → `CombinedFeed` → `CorrectedRadial` T² → the `PairingFeed/EqualityChain`-routed conclusion). 🎯 `cartanMap_isLocalIsometry` — for closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors, some alignment: the pullback equality on a punctured shrunk normal ball, curvature-only. If ONE hypothesis genuinely cannot be fed, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/IsometryComplete.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-88_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.IsometryComplete` and report the actual result. Commit your work.
