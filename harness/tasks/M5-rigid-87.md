Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-87: the enriched cascade — export the base package with the family

Context: `harness/reports/M5-rigid-86_blocked.md` (READ FIRST — the verbatim `hγ` field + the `Ts ≤ εs` margin note). THE GAP: `CartanCascade.lean`'s existence theorem exports the linearized family over an OPAQUE base curve `αs` — without the base-flow package (`HasDerivAt`, cutoff, speed fields) for THAT SAME curve; the facts exist for the hosted flow the cascade was BUILT FROM, but the export doesn't identify them. THE FIX: an ENRICHED cascade existence theorem — REPLAY `CartanCascade.lean`'s proof (READ it end to end: it constructs the family from the hosted PL flow, `CartanHomogeneity/LinearizedFamilyExport.lean`) and EXPORT ADDITIONALLY, for the same hosted datum: the base curve's `HasDerivAt` on the interval (the PL flow's derivative — `geodesicGermAt_chart_hasDerivAt`-family), the cutoff/zone membership, the speed constancy (`SpeedPackage.lean`'s facts AT this curve), and a STRICT margin `Ts < εs` (shrink the time by half in the construction — the hosted data allows it). Also the target side. Then rigid-86's assembly hypotheses ALL land → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/EnrichedCascade.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-87_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.EnrichedCascade` and report the actual result. Commit your work.
