Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-6: SANCTIONED correction (option 1) → the improved evolution inequality

Read `harness/reports/M4-ivey-5_blocked.md`. ORCHESTRATOR RULING: adopt its correction option 1 — the predicate should NOT carry the full completed-square damping on the RHS; Hamilton's argument only needs `∂ₜq ≤ Δq + drift + reaction/R^p-shape` (no explicit negative gradient term), with the ENTIRE gradient contribution proven ≤ 0 and absorbed. The worker's own analysis confirms this weaker total-sign is provable via the reserve route.

Deliverables (each its own commit):
1. **Correct the predicate**: deprecate-with-comment `SatisfiesTracelessPinchingImprovementEvolutionAt`'s full-damping form; state the corrected form: `∂ₜ(tracelessPinchingAt δ) ≤ Δ(...) + (2−δ)/R·⟨∇R, ∇(...)⟩-drift + tracelessPinchingReactionTermAt/normalization` (drift + reaction ONLY). PIN on the pure-trace pattern (the ivey-5 refutation datum — must now pass) + a mixed pattern.
2. **The Cauchy–Schwarz layer** (fiber lemmas, commit separately): `scalarGradNormSqAt ≤ 3·covRicciNormSqAt` (∇R = trace ∇Ric + C-S over the 3D fiber; the trace-commute lemma is on main from the pinch campaign) and the mixed-pairing bound `|pinchingMixedGradientPairingAt|² ≤ covRicciNormSqAt·scalarGradNormSqAt·N`-shape (or the direct form the absorption needs — derive the minimal sufficient bound).
3. **The total gradient sign**: [reserve −2·covRicciNormSqAt·(normalization)] + [defect δ·(...)·S] + [assembled gradient groups] ≤ 0 under ε-pinching + δ in an explicit (possibly shrunk) admissible range — the ivey-5 report's own consistency analysis is the blueprint. State the final δ(ε) range honestly.
4. **Land** `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow` (corrected predicate, honest hypotheses). Done-report + max-principle outlook.

Standing protocols. No sorry/axiom. BUILD NOTE: patience with builds. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
