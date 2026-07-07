Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-30: second-order smooth dependence — the augmented system opener

Context: `harness/reports/M5-glob-29_blocked.md` (READ FIRST — the VERBATIM differentiability/symmetry demand on `D q = fderiv F q`). THE HONEST CORE: F's C² = the SECOND-ORDER smooth dependence of the geodesic flow on initial conditions. THE PATTERN EXISTS (the first-order chain: `GeodesicLinearized.lean` the linearized system → `GeodesicDerivative.lean` uniform remainders → `GeodesicDerivativeFinal.lean` Grönwall residuals → `GeodesicFlowDerivative.lean` the flow derivative): REPLAY AT SECOND ORDER — (1) THE AUGMENTED SYSTEM: the pair (state, first-variation) `(γ, Ψ)` solves an ODE (the geodesic + linearized equations combined — its RHS is built from Γ and DΓ, smooth); its OWN linearization (the second-variation system: `(J₂, K₂)` driven by DΓ/D²Γ terms) — DEFINE it and prove the PL package (the coefficients bounded on the compact tube — Γ is C^∞ via `LocalConnectionRegularity.lean`); (2) the second-variation existence/uniqueness (the `linearODE` machinery is generic — instantiate); (3) state the DELIVERABLE INTERFACE for the follow-on: the flow derivative map `w ↦ Ψ_w(T)` is differentiable in the base data with derivative the second variation. Strict-partial: (1) alone is the prize; ONE isolated statement max. Report `harness/reports/M5-glob-30_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/SecondVariation.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.SecondVariation` and report the actual result. Commit your work.
