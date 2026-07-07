Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-48: hendpoint by uniqueness — then compose to the isometry

Context: `harness/reports/M5-rigid-47_blocked.md` (READ FIRST — the verbatim `hendpoint` statement). THE ONE MISSING HYPOTHESIS: the equality between the cascade-produced hosted linearized endpoint `Ψ` (`CartanCascade/LinearizedAdditivity/LinearizedRescale.lean`) and the rescaled harmonic endpoint `Φ` (the `jacobi_position_eq_sin_smul_on_Icc` object) inside the action-equation theorem. BOTH are solutions of THE SAME hosted linearized ODE on THE SAME interval with THE SAME initial data `(0, w)`-shaped and the same coefficient path — so `hendpoint` IS a `linearODE_solution_uniqueOn_Icc` application (`CoefficientEvolution.lean` / the uniqueness machinery in `GeodesicLinearized.lean`/`LinearizedCLM.lean` — align the ODE spellings: the cascade family's ODE fact vs the oscillator's covariant second-order form converted via the state bridge `chart_linearized_state_feeds_norm_system_at`-adjacent lemmas in `JacobiNormClose.lean`; the second-order-to-first-order conversion is standard — the harmonic Φ paired with its derivative solves the first-order system). PROVE `hendpoint`, then run rigid-47's composition through: action equations fed → equivalence upgrade → blocks → the bridge → 🎯 `cartanMap_isLocalIsometry`-shaped on the punctured shrunk ball.

Deliverables in a NEW file `Poincare/Global/CartanEndpointUnique.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial: `hendpoint` alone is the prize; ONE isolated statement max. Report `harness/reports/M5-rigid-48_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanEndpointUnique` and report the actual result. Commit your work.
