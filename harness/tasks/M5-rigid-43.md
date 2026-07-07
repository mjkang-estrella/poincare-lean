Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-43: rescale the family to all directions — the CLM hypotheses discharge

Context: `harness/reports/M5-rigid-42_blocked.md` (READ FIRST). EXPORTED: `exists_hosted_linearized_solution_family_on_pl_closedBall` (`LinearizedFamilyExport.lean` — the concrete PL fixed-point linearized family with initial value, ODE, ball membership). REMAINING: (1) ALL-DIRECTION EXTENSION by RESCALING: for arbitrary `w ∈ E`, define `Ψ_w := (‖w‖·c)·Ψ_{(w/(‖w‖·c))}`-shaped using the ball family + the linear-system homogeneity (a scalar multiple of a solution solves the same LINEAR system with scaled initial data — `GeodesicLinearized.lean` linearity + `LinearizedCLM.lean`'s homogeneity uniqueness lemmas — this is exactly what those lemmas were built for); conclude the FULL-SPACE family with additivity/smul at the endpoint (the CLM hypotheses of `linearizedEndpointCLM`); (2) the radial-action + rescaled-harmonic instantiations at the hosted data (`CartanHomogeneity.lean` endpoint derivative; the oscillator discharge REUSE from `CartanIsometryTheorem.lean`'s proof); (3) feed `exists_shrunk_..._of_linearized_family` (`CartanIsometryClose.lean`) + the action theorem (`CartanActionEquations.lean`) → the unconditional strict derivatives WITH action equations, source and target → (4) 🎯 THE LOCAL ISOMETRY via the hosted-scale bridge with the source blocks.

Deliverables in a NEW file `Poincare/Global/LinearizedRescale.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial per item; ONE isolated statement max. Report `harness/reports/M5-rigid-43_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.LinearizedRescale` and report the actual result. Commit your work.
