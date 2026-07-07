Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-73: the corrected-radial consumer — plain time scale on the ray

Context: `harness/reports/M5-rigid-72_blocked.md` (READ FIRST). ISOLATED: rigid-70's decomposed consumer (`DecomposedAssembly.lean`) demands the radial-radial block with `speedPinnedScale` — which UNFOLDS TO THE TRANSVERSE SINE SCALE (`RadialBlock.lean` proves the unfolding); the ray variation has PLAIN time-scaling `T²·speed²` (no sine) — the demanded radial hypothesis is wrong-shaped. THE FIX (additive): a corrected consumer variant in a NEW file — REPLAY rigid-70's proof pattern (`DecomposedAssembly.lean`'s 4-term bilinear expansion + feed + consumer) with the RADIAL scalar corrected to the plain time-scale (`T²·speed²`-shaped; the pullback works because the radial factors MATCH through `L` — speeds agree by the alignment, `SpeedPackage.lean` — just as the sine factors matched for transverse). Then DISCHARGE all blocks: radial-radial = the ray-variation pairing (identify radial `Ψ_v` with the ray derivative by linearized uniqueness — differentiate homogeneity `exp(s·v)` in `s`, `ExponentialRayLawFull.lean`; endpoint pairing = `T²·speed²` by constant speed) — mixed (proven, `BlocksDischarge.lean`) — transverse (proven, `SpeedGeneric.lean` restricted variants + `OrthogonalityFeed.lean`). 🎯 `cartanMap_isLocalIsometry`, curvature-only hypotheses. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/CorrectedRadial.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-73_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CorrectedRadial` and report the actual result. Commit your work.
