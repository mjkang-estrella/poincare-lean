Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-49: COMPOSE — hendpoint is proven; nothing is missing

Context: `harness/reports/M5-rigid-48_done.md` + `M5-rigid-47_blocked.md` (READ BOTH). rigid-47 isolated exactly ONE missing hypothesis (`hendpoint`); rigid-48 PROVED it: `hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc` (`CartanEndpointUnique.lean`). THE COMPLETE INVENTORY (rigid-47's task file lists it; every item gated): cascade strict derivatives (`CartanCascade.lean`), action equation + hendpoint feed (`CartanActionEquations.lean` + `CartanEndpointUnique.lean`), equivalence upgrade (`CartanEquivUpgrade.lean`), scale normalization (`CartanFinalComposition.lean`), pairing blocks (`CartanIsometryPackage/CartanIsometryTheorem.lean` + speed + Gauss + the hosted conversions), the witness, the consumer (`CartanScaleGeneric.lean`). RUN THE COMPOSITION rigid-47 mapped: one radius intersection, instantiate, feed. 🎯 `cartanMap_isLocalIsometry`-shaped: for every closed simply-connected constant-curvature-1 `g`, anchors `x₀ p₀`, some alignment `L`: the chart-metric pullback equality on the punctured shrunk normal ball. If ANOTHER single hypothesis emerges, isolate it verbatim (the rigid-47/48 pattern — each round removes exactly one).

Deliverables in a NEW file `Poincare/Global/CartanIsometryDone.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-49_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanIsometryDone` and report the actual result. Commit your work.
