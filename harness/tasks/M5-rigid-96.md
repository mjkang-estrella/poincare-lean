Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-96: the small-T common time — two more terms in the min

Context: `harness/reports/M5-rigid-95_blocked.md` (READ FIRST). PROVEN: the interval-aligned selector with strict derivative + the radial ray field for `T < ε` (`IntervalAlign.lean`); the PL packages with their `εlin` margins (`PLPackages.lean`). THE ONE EXPORT: a common-time theorem choosing `T < min(…existing terms…, εlin_source, εlin_target)` — REPLAY `CommonTime.lean`'s common theorem (READ its `T`-choice) with the two extra bounds in the min (the εlin's come from `PLPackages.lean`'s existence statements — thread the witnesses); everything else restricts (`IntervalAlign.lean`'s restriction lemmas). Then: the selectors fire on both sides (families + strict derivatives + ray fields), the master-bundle witnesses ALL exist at one datum → the assembly (`AssemblyDone/IsometryComplete/BundleDischarge → CombinedFeed → CorrectedRadial`) → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/SmallTCommon.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-96_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SmallTCommon` and report the actual result. Commit your work.
