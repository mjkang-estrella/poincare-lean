Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-61: the continuity packages — both sides, assembled

Context: `harness/reports/M5-glob-60_blocked.md` (READ FIRST). PROVEN: the hosted CLM with the eventual endpoint package (`HostedCLM.lean`); the Grönwall bound (`OmegaGronwall.chartChristoffel_thirdVariation_endpoint_gronwall_bound` — the Lipschitz estimate); the endpoint derivatives (`TransitionLands.lean`); the consumer (`EndpointContinuity.lean`'s exact package shapes). THE ASSEMBLY: (1) `q ↦ D_q` (the hosted CLM field) is CONTINUOUS — the Grönwall bound gives Lipschitz on the ball (`LipschitzOnWith.continuousOn`-shaped conversion); (2) package SOURCE: the canonical endpoint-continuity package (`EndpointContinuity`'s demanded fields: the CLM field, its continuity, the local derivative representation — from `TransitionLands`' derivatives + the identification); (3) TARGET identically (the sphere — the generic route at `roundSphereMetric3`); (4) FEED → `EndpointContinuity → CanonicalC1 → LevelThreeFeed → TowerCloses` → 🎯 THE F-TRANSITION LAW UNCONDITIONAL. If ONE resists, isolate verbatim. Report `harness/reports/M5-glob-61_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/ContinuityPackages.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.ContinuityPackages` and report the actual result. Commit your work.
