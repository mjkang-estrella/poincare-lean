Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-58: the endpoint-pairing feed — the hosted facts into the bridge

Context: `harness/reports/M5-rigid-57_blocked.md` (READ FIRST). PROVEN: the pairing-route bridge (the `cartanMap_isLocalIsometry`-shaped derivative-pairing statement) + the CLM-to-`Ψ.1` pairing conversion (`PairingRoute.lean` — READ its exact remaining hypothesis shapes). THE FEED: connect the hosted facts to those shapes — (1) `Ψ.1`-pairings at the hosted endpoint `(u,T)`: transverse-transverse from `actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique` (`CartanIsometryPackage.lean`) + the norms (`CartanIsometryTheorem.lean`) — their statements are on the actual hosted scalars, CHECK the exact objects and align; radial-radial from constant speed; radial-transverse from integrated Gauss (payload versions, `SmoothDependenceDischarge.lean`); (2) the endpoint conversions `t = T`, `v = T·u` (`CartanHomogeneity.lean`, `CartanDomainShrink.lean`, rigid-47's scale normalization in `CartanFinalComposition.lean`); (3) BOTH SIDES (target via the same generic theorems + the witness `roundSphereMetric3_hasConstantSectionalCurvature_one`). Feed the bridge → 🎯 `cartanMap_isLocalIsometry`. If ONE hypothesis emerges, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/PairingFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-58_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.PairingFeed` and report the actual result. Commit your work.
