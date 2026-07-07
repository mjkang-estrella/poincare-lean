Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-93: THE MASTER BUNDLE — every witness in one existence theorem

Context: `harness/reports/M5-rigid-92_blocked.md` (READ FIRST — the exact witness list: hosted PL, ray, norm identities). PROVEN: the common-time enriched cascade (`CommonTime.lean` — one shared `T`, both sides, via anchor-metric preservation). THE FINAL EXPORT: one existence theorem at the common-time hosted datum bundling EVERY witness the assembly consumes: the hosted PL packages (`CartanHomogeneity/GeodesicLengthFinal.lean` + the bounded norm-system data `BoundedPackage/GronwallMembership.lean`), the ray facts (`RayIdentification.lean` at the common datum), the norm/initial identities (`SpeedPackage/SpeedReconcile.lean`), the radius bounds (the intersections done piecewise in rigid-31/47/77) — the pattern: each piece's existence statement yields its witnesses; INTERSECT the radii once, package the tuple. Then APPLY the assembly chain (`AssemblyDone.lean`'s blocks + `IsometryComplete.lean`'s feeds + the consumer) → 🎯 `cartanMap_isLocalIsometry` — curvature-only. If ONE witness resists co-packaging, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/MasterBundle.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-93_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.MasterBundle` and report the actual result. Commit your work.
