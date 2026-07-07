Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-51: the acceleration identity — the covariant oscillator in coordinates

Context: `harness/reports/M5-rigid-50_blocked.md` (READ FIRST — the verbatim narrowed acceleration identity). PROVEN: `hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq` (`HarmonicHosted.lean` — hΦderHosted GIVEN the acceleration identity). THE ONE IDENTITY: the harmonic's coordinate second derivative equals the hosted linearized RHS — i.e., the COVARIANT oscillator identity (`coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`, `JacobiOscillator.lean`) UNPACKED into coordinates: covariant second = coordinate second + Γ-correction terms (the state-bridge bookkeeping `chart_linearized_state_feeds_norm_system_at`'s `D = K + Γ(z)(V,J)` conversion, `JacobiNormClose.lean` — its proof DID this bookkeeping pointwise; extract/replay the rearrangement), so coordinate second = −(harmonic) − Γ-terms = the linearized RHS at the harmonic state (the linearized RHS's definition, `GeodesicLinearized.lean`, IS the Γ-structure — match them term by term). The oscillator's interval discharge: REUSE from `CartanIsometryTheorem.lean`. Then: feed rigid-50's theorem → hΦderHosted → rigid-49's composition → the action equations → the equivalence upgrade → the blocks → 🎯 `cartanMap_isLocalIsometry`.

Deliverables in a NEW file `Poincare/Global/AccelerationIdentity.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial: the identity alone is the prize; ONE isolated statement max. Report `harness/reports/M5-rigid-51_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.AccelerationIdentity` and report the actual result. Commit your work.
