Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-98: export the uniform-flow five — the selector fires

Context: `harness/reports/M5-rigid-97_blocked.md` (READ FIRST — the five fields VERBATIM: `hα0, hαder, hαmem, hαtarget, hexp`). PROVEN: the uniform PL shrink + common time with `T < εlin` both sides + the basic selectors (`UniformShrink.lean`). THE FIVE FIELDS: the uniform-flow facts for the hosted base curve — initial value, derivative law, tube membership, target identity, exp identification — CONSTRUCTED INTERNALLY by the common-time/hosting chain (`CommonTime.lean` ← `EnrichedCascade.lean` ← `CartanHomogeneity.lean` — READ where each field is produced; the hosted flow existence statements HAVE them). THE RE-EXPORT (the rigid-87 pattern): replay/extend the common-time theorem exporting the five fields alongside (or prove an adapter from the `BaseCurvePackage` fields — CHECK whether the package's fields already imply them: `hα0` = the package's initial value, `hαder` = its derivative field, `hαmem` = its cutoff/zone field, `hαtarget/hexp` = the hosted endpoint formulas from `CartanHomogeneity.lean` — likely ADAPTERS suffice, no replay). Feed `IntervalAlign`'s enriched selector → the ray fields land both sides → the master bundle closes → the assembly → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/UniformFlowExport.lean` (do NOT edit any existing file, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-98_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.UniformFlowExport` and report the actual result. Commit your work.
