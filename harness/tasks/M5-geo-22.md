Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-22: GOAL 10 — the integrated transverse Gauss lemma

Context: all three ingredients are now PROVEN. (a) The pointwise transverse variation identity `chart_geodesic_transverse_pairing_hasDerivAt` (`Poincare/Global/GaussLemmaTransverse.lean`: pairing derivative = (1/2)·speed s-derivative shape). (b) THE FLOW DERIVATIVE `chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow` (`Poincare/Global/GeodesicFlowDerivative.lean`: `s ↦ α(z₀, v + s•w) t` has derivative `Ψ t` at `0` — supplies the Jacobi field J = Ψ.fst and its t-derivative K = Ψ.snd via the linearized system, `GeodesicLinearized.lean`). (c) Constant speed (`GeodesicSpeed.lean`). Read `harness/reports/M5-geo-21_done.md` + `M5-geo-16_done.md` for the exact glue boundary each side expects.

Deliverables, in a NEW file `Poincare/Global/GaussLemmaIntegrated.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE s-DERIVATIVE OF SPEED: differentiate `s ↦ G(α_s t)(α_s' t, α_s' t)` at `s = 0` via the flow derivative + chain rule (the metric pairing is smooth in its base/slots); relate to the pairing identity's RHS.
2. THE GAUSS PAIRING CONSERVATION: `t ↦ G(γ t)(J t, γ' t)` has derivative `(1/2)·(d/ds speed)(t)`; with (1) constant in `s` at the radial family (speed of the `v + s•w` geodesic at fixed `t` — from constant speed per geodesic, the s-derivative reduces to the INITIAL speed s-derivative `2·G(anchor)(v, w)`-shaped) — conclude the pairing law `G(γ t)(J t, γ' t) = G(anchor)(w, v) + t·G(anchor)(v, w)`-shaped (derive the exact form; document).
3. THE ORTHOGONAL CASE: `G(anchor)(v, w) = 0 ⟹ G(γ t)(J t, γ' t) = 0` on the interval — THE GAUSS LEMMA in chart form.
4. Report `harness/reports/M5-geo-22_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GaussLemmaIntegrated` and report the actual result. Commit your work.
