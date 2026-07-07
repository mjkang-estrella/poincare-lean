Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-19: discharge the side conditions — the reanchor law lands

Context: `harness/reports/M5-glob-18_done.md` (READ FIRST). PROVEN: THE TRANSITION LAW (`chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one`, `TransitionLawFires.lean`) — conditional on: (a) chart-transition derivative INVERTIBILITY (the transition is a diffeomorphism on the overlap — its derivative is a linear iso: the `extChartAt` transition is a `PartialHomeomorph` with smooth inverse; the derivative of the composition with its inverse is the identity ⟹ invertible — the `HasFDerivAt.comp` + inverse identity argument, or Mathlab's `PartialHomeomorph`/`ContDiff` iso API); (b) target metric NONDEGENERACY (positive-definite ⟹ nondegenerate — the anchor metric positivity lemmas `CartanMap/CartanPullback.lean`, extended along the zone by the blended-metric positivity — check `VolumeDensity/AntilipschitzBall.lean` positivity exports). DISCHARGE both on the cutoff-one overlap → the transition law UNCONDITIONAL (zone-scoped) → feed the velocity-component form to `ChristoffelTransition.lean`'s bridge → `ReanchorLawFinal.lean` → 🎯 THE REANCHOR LAW → `OffAnchorNaturality/ExpNaturality` fire → `RigidStepCompatibleWith`. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-19_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/SideConditions.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.SideConditions` and report the actual result. Commit your work.
