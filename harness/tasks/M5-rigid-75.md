Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-75: ALL BLOCKS HAVE THEOREMS — the final discharge

Context: `harness/reports/M5-rigid-74_done.md` + `M5-rigid-73_blocked.md` (READ BOTH). THE COMPLETE BLOCK INVENTORY (every one a gated theorem):
- RADIAL: `RayIdentification.radial_linearized_endpoint_eq_time_smul_velocity_of_uniform_geodesicFlow` + `radial_endpoint_pairing_eq_plainRadialScale` + the radialPart/coeff consequences (`RayIdentification.lean`)
- MIXED: the anchor Gram facts (`BlocksDischarge.lean`) + the transverse orthogonality feed (`OrthogonalityFeed.lean` — the endpoint mixed vanishing)
- TRANSVERSE: the restricted sin-pinned variants (`SpeedGeneric.lean`) + the interval discharges (`CartanIsometryTheorem/TargetPackage.lean`)
- SPEEDS/TIMES: `SpeedPackage.lean` + `TheLocalIsometry.lean`'s instantiations
- THE CONSUMER: `CorrectedRadial.lean`'s corrected-radial chain (plain radial scale — the shapes now match by rigid-74's consequences)
- decomposition/additivity/hosting/alignment: `CartanPullback/LinearizedAdditivity/CartanHomogeneity/CartanMap.lean`
THE TASK: instantiate every hypothesis of `CorrectedRadial.lean`'s final consumer at the hosted data (the same `(v, u, T, Ψs, Ψt)` quantification the pieces share — one radius intersection if needed) and DELIVER: 🎯 `cartanMap_isLocalIsometry` — for every closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors `x₀ p₀`, some alignment `L`: the chart-metric pullback equality on a punctured shrunk normal ball. NOTHING ELSE — this is pure application. If ONE hypothesis genuinely cannot be fed, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/IsometryFinal.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-75_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.IsometryFinal` and report the actual result. Commit your work.
