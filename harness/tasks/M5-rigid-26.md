Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-26: integrate the system — a = sin²·|w|², the coefficients, the isometry

Context: `harness/reports/M5-rigid-25_done.md` (READ FIRST). CONNECTED: the pointwise bridge `chart_linearized_state_feeds_norm_system_at` (`JacobiNormClose.lean` — chart `(J,K)`, covariant `D = K + Γ(z)(V,J)`, oscillator, norm system inputs). PROVEN: the closed system derivatives + sine/cosine pin + polarization (`JacobiNormSystem.lean`), ODE uniqueness (`CoefficientEvolution.lean`, `GeodesicLinearized.lean`). THE INTEGRATION: on the honest interval (the cutoff-one-shrunk flow, `GeodesicLengthFinal.lean`), the three scalars satisfy the system at every interval point (the pointwise bridge quantified over t — check the bridge's hypotheses hold along the flow: zone membership, oscillator applicability per `JacobiOscillator.lean`'s interval versions), so by uniqueness with initial `(0,0,|w|²)`: `a(t) = sin²t·|w|²_anchor` on the interval. Then: polarize (proven algebra) → the transverse-transverse pairing; radial and cross from constant speed + integrated Gauss → THE EXP-CHART COEFFICIENT FORMULAS; the exp-chart conjugation (`CartanNormalCoords.lean`) → THE PULLBACK → 🎯 THE LOCAL ISOMETRY.

Deliverables in a NEW file `Poincare/Global/JacobiIntegrated.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial per stage; ONE isolated statement max. Report `harness/reports/M5-rigid-26_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.JacobiIntegrated` and report the actual result. Commit your work.
