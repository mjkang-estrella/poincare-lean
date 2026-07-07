Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-44: additivity of the rescaled family — the CLM discharge

Context: `harness/reports/M5-rigid-43_blocked.md` (READ FIRST). EXPORTED: `exists_hosted_rescaled_linearized_solution_family` (`LinearizedRescale.lean` — all-direction family, right initial data, solves the hosted linearized ODE). REMAINING: the CLM endpoint hypotheses for THIS family — additivity `Ψ_{w+w'}(T) = Ψ_w(T) + Ψ_{w'}(T)` and smul `Ψ_{c·w}(T) = c·Ψ_w(T)`: BOTH follow from the linearized ODE UNIQUENESS on the interval — `Ψ_w + Ψ_{w'}` solves the same linear system with initial data `(0, w+w')` (linearity of the RHS in the state — the lemmas in `LinearizedCLM.lean` were PROVEN for exactly this: `linearized…add/smul` uniqueness lemmas — APPLY them to the rescaled family's ODE facts; check hypothesis alignment: same interval, same coefficient path, uniqueness anchor). Then: `linearizedEndpointCLM` for the hosted family at each `v` → feed `exists_shrunk_..._of_linearized_family` (`CartanIsometryClose.lean`) → the unconditional strict derivative at each shrunk-ball `v` with the CLM value; the action equations (`CartanActionEquations.lean` + hosted radial derivative + oscillator discharge reuse) → 🎯 as far into THE LOCAL ISOMETRY as closes.

Deliverables in a NEW file `Poincare/Global/LinearizedAdditivity.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial per item; ONE isolated statement max. Report `harness/reports/M5-rigid-44_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.LinearizedAdditivity` and report the actual result. Commit your work.
