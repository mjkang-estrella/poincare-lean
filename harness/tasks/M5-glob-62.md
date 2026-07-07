Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-62: the indexed selection — ζ, Ω, D over the ball

Context: `harness/reports/M5-glob-61_blocked.md` (READ FIRST — the VERBATIM neighborhood-indexed `q ↦ ζ_q, Ω_q, D_q` package). PROVEN: the conversion bridges + the consumer accepting Grönwall bounds (`ContinuityPackages.lean`); the per-point existence statements: the doubly-augmented base (`SecondDischarge/FlowSmoothness`'s hosted flows AT each q — the selector machinery `UniformFlowExport/CommonTime` quantifies over the ball), Ω on the paired base (`OmegaGronwall.exists_hosted_thirdVariation_solution_family_on_paired_base`), the CLM `D` (`HostedCLM`). THE SELECTION (the `DifferentialField.lean` choice pattern): define `q ↦ (ζ_q, Ω_q, D_q)` by `Classical.choice` over the per-point existentials on the ball; the specs hold pointwise (`choose_spec`); the GRÖNWALL BOUNDS relate DIFFERENT points' selections — the uniqueness of the objects (PL/linearODE uniqueness identifies any two valid selections at overlapping data — the same-solution lemmas) transfers `OmegaGronwall`'s paired-base bound to the SELECTED family. ASSEMBLE the indexed package → feed `ContinuityPackages`' consumer → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-62_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/IndexedSelection.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.IndexedSelection` and report the actual result. Commit your work.
