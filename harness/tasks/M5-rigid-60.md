Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-60: the pinned formulas for the cascade Ψ — the last upstream link

Context: `harness/reports/M5-rigid-59_blocked.md` (READ FIRST — the verbatim missing statement). PROVEN: the equality chain + consumer feed (`EqualityChain.lean`) — the local isometry follows from the two PINNED hosted endpoint formulas for the actual cascade families `Ψs`/`Ψt` (`CartanCascade.lean`'s). THE LINK: the pairing/norm theorems (`actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique`, `CartanIsometryPackage.lean`; `actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`, `CartanIsometryTheorem.lean`) — READ their exact hypothesis shapes: they hold for families satisfying the hosted linearized ODE + initial data + interval conditions. THE CASCADE `Ψ` SATISFIES EXACTLY THESE (its defining properties, `LinearizedRescale/LinearizedAdditivity/CartanCascade.lean` exports). FEED: either apply the theorems directly to the cascade family (hypothesis alignment), or identify the cascade family with the theorems' family by `linearODE_solution_uniqueOn_Icc` (same ODE + same initial data ⟹ same scalars). Do it for SOURCE and TARGET (the generic route + the witness). Then the chain (`EqualityChain.lean`) fires → 🎯 `cartanMap_isLocalIsometry`. If ONE sub-hypothesis resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/CascadePinned.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-60_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CascadePinned` and report the actual result. Commit your work.
