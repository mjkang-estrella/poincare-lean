Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-63: the source package + scalar normalizations — the last two feeds

Context: `harness/reports/M5-rigid-62_blocked.md` (READ FIRST — the verbatim remaining hypotheses). PROVEN: the unscale bridge wired through the chain to the consumer (`UnscaledFeed.lean`); the TARGET rescaled feed (`TargetPackage.lean`). REMAINING TWO: (1) THE SOURCE RESCALED FEED — the EXACT MIRROR of `TargetPackage.lean` at the source metric (`HasConstantSectionalCurvature3 g 1` hypothesis instead of the witness): REPLAY `TargetPackage.lean`'s proof structure line by line with `g` — the generic machinery is identical (`target_normA_eq_pinned_on_cutoff_one_Icc` → `source_...`; the interval work reuses `CartanIsometryTheorem.lean`'s source-side discharge which ALREADY EXISTS — check what TargetPackage actually needed and mirror); (2) THE SCALAR NORMALIZATION IDENTITIES (the explicit assumptions in `UnscaledFeed.lean` — READ them): relate the hosted speeds/times/sin factors across the rescale — from rigid-47's scale normalization (`CartanFinalComposition.lean`), the hosted construction (`CartanHomogeneity.lean`: `T·u = v`, `‖u‖ = δ/2`), and `Real.sin` algebra. Then EVERYTHING is fed → 🎯 `cartanMap_isLocalIsometry` via the wired chain. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/SourcePackage.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-63_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SourcePackage` and report the actual result. Commit your work.
