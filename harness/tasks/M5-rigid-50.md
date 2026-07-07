Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-50: hΦderHosted — the harmonic solves the hosted system

Context: `harness/reports/M5-rigid-49_blocked.md` (READ FIRST — the verbatim `hΦderHosted` statement). PROVEN LAST ROUND: the endpoint-feed action composition (`linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique`, `CartanIsometryDone.lean`). THE ONE REMAINING HYPOTHESIS: `hΦderHosted` — the hosted rescaled harmonic `Φ` (the `sin(s·t)`-shaped object) SOLVES the hosted first-order linearized ODE. THE INGREDIENTS: the harmonic's second-order fact is the oscillator identity (`jacobi_position_eq_sin_smul_on_Icc` / `coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`, `JacobiOscillator.lean` — its interval discharge was done inside `CartanIsometryTheorem.lean`'s proof: REUSE); the second-to-first-order conversion is the state bridge (`chart_linearized_state_feeds_norm_system_at`-adjacent machinery, `JacobiNormClose.lean` — the covariant/coordinate bookkeeping `D = K + Γ(z)(V,J)`); the derivative calculus of `t ↦ sin(s·t)·w` is `Real.hasDerivAt_sin`-elementary. ASSEMBLE: `Φ` paired with its honest derivative solves the hosted system on the interval. Then feed rigid-49's composition → the action equations complete → the equivalence upgrade → the blocks → 🎯 `cartanMap_isLocalIsometry`.

Deliverables in a NEW file `Poincare/Global/HarmonicHosted.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial: `hΦderHosted` alone is the prize; ONE isolated statement max. Report `harness/reports/M5-rigid-50_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.HarmonicHosted` and report the actual result. Commit your work.
