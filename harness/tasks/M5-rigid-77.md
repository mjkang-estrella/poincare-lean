Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-77: the combined feed — one quantification, every fact

Context: `harness/reports/M5-rigid-76_blocked.md` (READ FIRST — the exact remaining bundle). DISCHARGED: the radial blocks BOTH SIDES (`SpeedReconcile.source/target_radialPart_endpoint_pairing_eq_timeRadialScale`) + the T² consumer variants (`CorrectedRadial.lean`). REMAINING: the final theorem's assumption bundle — the ray, speed, and non-radial block facts — each EXISTS as an exported theorem, at possibly different quantifications: ray (`RayIdentification.lean`), speeds (`SpeedPackage/TheLocalIsometry.lean`), transverse/mixed (`SpeedGeneric.lean` restricted variants + `OrthogonalityFeed.lean` + interval discharges `CartanIsometryTheorem/TargetPackage.lean`), hosting (`CartanHomogeneity.lean`), alignment (`CartanMap/CartanPullback.lean`). THE TASK: ONE COMMON QUANTIFICATION — pick the hosted datum `(δ, v, u, T, Ψs, Ψt, flows)` on a final shrunk ball where EVERY fact's side conditions hold simultaneously (the radius-intersection pattern — `CartanDomainShrink.lean`; the existence statements carry their own radii: intersect), instantiate each exported theorem at it, and feed the T²-variant consumer. 🎯 `cartanMap_isLocalIsometry` — curvature-only. If ONE fact cannot be co-quantified, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/CombinedFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-77_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CombinedFeed` and report the actual result. Commit your work.
