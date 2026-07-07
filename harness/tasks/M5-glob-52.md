Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-52: the level-three feed — sourceD is C¹, concretely

Context: `harness/reports/M5-glob-51_blocked.md` (READ FIRST). THE CONSUMER IS THREADED (`TowerCloses.lean` — ContDiffAt 1 fields ⟹ THE F-TRANSITION LAW). THE FEED (the glob-44/45/46 patterns at level three, ALL ingredients proven): (1) the doubly-augmented Grönwall dependence (the field-generic core + `FieldC1/FlowSmoothness.lean`'s Lipschitz data — the `AugmentedDependence.lean` proof replayed); (2) FEED the residual theorem at the doubly-augmented data (its hypotheses: the doubly-augmented ODE facts (the augmented flow + its variation — from `SecondDischarge`'s instantiation pattern applied one level up), the third-variation PL solutions (`ThirdVariation.lean`), the remainders (`FieldC1.lean`), the Lipschitz) ⟹ the second-variation-endpoint field's derivative; (3) continuity of the derivative (the third-variation dependence from (1)) ⟹ 🎯 `ContDiffAt ℝ 1 sourceD v` + `targetD` (the assembly — `contDiffAt_one_iff` or `HasFDerivAt.contDiffAt`-shaped). FEED `TowerCloses` → 🎯🎯 THE F-TRANSITION LAW UNCONDITIONAL. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-52_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/LevelThreeFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.LevelThreeFeed` and report the actual result. Commit your work.
