Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-37: the linearized solution map is a ContinuousLinearMap

Context: `harness/reports/M5-rigid-36_blocked.md` (READ FIRST). PREREQUISITE (a) for the strict derivative at nonzero endpoints: package `w ↦ (Ψ_w T).1` (the linearized/Jacobi endpoint position, `GeodesicLinearized.lean`/`GeodesicFlowDerivative.lean`) as a `ContinuousLinearMap E →L[ℝ] E` for the hosted flow data. THE INGREDIENTS EXIST: ADDITIVITY `Ψ_{w+w'} = Ψ_w + Ψ_{w'}` — proven inside `CartanIsometryPackage.lean`'s polarization work (`actual_jacobi_pairing…` proof used linearized additivity via `linearODE_solution_uniqueOn_Icc` — EXTRACT/restate it as a standalone lemma if not exported); SCALAR HOMOGENEITY `Ψ_{c·w} = c·Ψ_w` — same uniqueness argument (the scaled solution solves the linear system); CONTINUITY/BOUNDEDNESS — the linearized system's Grönwall bound (`GeodesicLinearized/GeodesicDerivative.lean` uniform machinery) gives `‖Ψ_w(t)‖ ≤ C·‖w‖` on the interval — or finite-dimensionality: a linear map on `E` (finite-dim) is automatically continuous (`LinearMap.continuous_of_finiteDimensional` / `LinearMap.toContinuousLinearMap`) — so ADDITIVITY + HOMOGENEITY alone suffice!

Deliverables, in a NEW file `Poincare/Global/LinearizedCLM.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. The standalone additivity + homogeneity lemmas (uniqueness route).
2. 🎯 `linearizedEndpointCLM`-shaped: the `E →L[ℝ] E` packaging (via `LinearMap.toContinuousLinearMap` on finite-dim) with the defining lemma `linearizedEndpointCLM w = (Ψ_w T).1`.
3. Report `harness/reports/M5-rigid-37_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.LinearizedCLM` and report the actual result. Commit your work.
