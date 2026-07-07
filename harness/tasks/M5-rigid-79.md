Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-79: the one-sided payload — integration on [0,T] with within-derivatives

Context: `harness/reports/M5-rigid-78_blocked.md` (READ FIRST — the verbatim `hflow` mismatch). THE GAP: `OrthogonalityFeed`'s payload consumer demands the variation derivative on an OPEN `Ioo a b ∋ 0` (two-sided at 0); the export gives `Icc 0 ε` (one-sided). THE FIX (the report's option (b)): a ONE-SIDED integrated transverse Gauss payload variant — replay the orthogonality integration argument (`OrthogonalityFeed.lean`'s payload theorem + `SmoothDependenceDischarge.lean`'s integrated Gauss bridge — READ their proofs) with `HasDerivWithinAt (Icc 0 T)` hypotheses: the integration from 0 to T only needs within-interval derivatives (`Real.intervalIntegral` / the monotone-derivative lemmas used upstream work with `Icc`-within versions — the same pattern the interval discharges in `CartanIsometryTheorem.lean` used). ADDITIVE variant only (NEW file; no edits to existing files). Then: the hosted payload bundle discharges with the one-sided exports (the `Icc 0 ε` facts feed directly), the transverse orthogonality lands at the hosted datum, and the combined feed completes → 🎯 `cartanMap_isLocalIsometry`. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/OneSidedPayload.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-79_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.OneSidedPayload` and report the actual result. Commit your work.
