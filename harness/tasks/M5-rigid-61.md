Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-61: the target packaging — the sphere cascade's interval hypotheses

Context: `harness/reports/M5-rigid-60_blocked.md` (READ FIRST — the verbatim remaining hypotheses). PROVEN: the cascade pinned bridge (`CascadePinned.lean`). REMAINING: the interval/norm hypothesis PACKAGE for the ACTUAL TARGET cascade (the `roundSphereMetric3` side) — the same package the SOURCE side already has (its discharge lives in/around `CartanIsometryTheorem.lean`'s cutoff-one interval work + the hosted PL facts, `CartanHomogeneity/CartanCascade.lean`). THE TASK: mirror the source discharge at the target — the generic machinery (`GeodesicLengthFinal`'s shrunk flow, the zone facts, the oscillator interval discharge, the hosted `(u,T)` construction) instantiated at `roundSphereMetric3` via the witness (`roundSphereMetric3_hasConstantSectionalCurvature_one`, `RoundSphereWitness.lean`) and closed-ball instances already built for the sphere (`ExponentialStrictAtV.lean` had sphere instances; `CartanCascade.lean`'s target derivative exists — its proof fed sphere-side facts: REUSE its feeding steps). Package the exact hypotheses rigid-60's bridge wants → the pinned target formulas → the chain fires (`EqualityChain.lean` + `CascadePinned.lean`) → 🎯 `cartanMap_isLocalIsometry`. If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/TargetPackage.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-61_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.TargetPackage` and report the actual result. Commit your work.
