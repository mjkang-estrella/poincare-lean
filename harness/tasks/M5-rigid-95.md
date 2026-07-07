Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-95: the interval alignment — choose T below εlin

Context: `harness/reports/M5-rigid-94_blocked.md` (READ FIRST). EXPORTED: the real zero-centered PL packages + `BaseCurvePackage` specialization + family selection on the SHRUNK interval `εlin ≤ εs/εt` (`PLPackages.lean`). THE MISMATCH: `CommonTime.lean`'s selection works on the ORIGINAL intervals. THE FIX (nesting): a common-time variant selecting `T < min(εlin_source, εlin_target)` — the common-time proof pattern (`CommonTime.lean` — READ how it chooses `T`) replayed with the smaller margin; all interval facts RESTRICT to the smaller interval trivially (`Icc`-monotonicity — the enriched package fields restrict; the PL packages now apply as-is). Then: the families select, the ray fields land (`RayIdentification` at the selected families — its uniform-flow hypotheses come from the hosted construction inside `CommonTime/CartanHomogeneity.lean`; export them alongside if missing — the report lists `δ, hα0, hαder, hαmem, hαtarget, hexp` — these ARE the hosted flow facts, thread them through), the master bundle closes → the assembly → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/IntervalAlign.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-95_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.IntervalAlign` and report the actual result. Commit your work.
