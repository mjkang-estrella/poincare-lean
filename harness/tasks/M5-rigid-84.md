Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-84: EVERY FEED EXISTS — assemble cartanMap_isLocalIsometry

Context: `harness/reports/M5-rigid-83_done.md` (READ FIRST) + the chain of reports rigid-75..83. THE COMPLETE FEED INVENTORY (all gated):
- transverse-transverse: bounded feeds + homogeneous all-direction extension (`BoundedPackage.lean`)
- transverse orthogonality (one-sided): `OneSidedPayload.lean` + `BundleDischarge.lean`'s routing
- radial: `RayIdentification.lean` + `SpeedReconcile.lean` (both sides, T² scale)
- mixed: `CombinedFeed.lean`'s derivation
- speeds/times/hosting: `SpeedPackage/TheLocalIsometry/CartanHomogeneity.lean`
- the consumer chain: `CorrectedRadial.lean` T² variants → `PairingFeed/EqualityChain`-routed local-isometry conclusion
THE TASK: ONE ASSEMBLY — at the hosted datum (final radius intersection), instantiate every feed and apply the consumer. 🎯 `cartanMap_isLocalIsometry` — for closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors, some alignment: the pullback equality on a punctured shrunk normal ball, NO other hypotheses. This is application — the mathematics is done. If ONE hypothesis genuinely cannot be fed, isolate verbatim WITH the exact mismatch (shape, quantifier, or side condition).

Deliverables in a NEW file `Poincare/Global/TheIsometry.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-84_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.TheIsometry` and report the actual result. Commit your work.
