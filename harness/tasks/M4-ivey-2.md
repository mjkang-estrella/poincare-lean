Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-2: the eigenvalue improvement lemma (RicciNorm.lean ONLY)

SCOPE: work ONLY in `Poincare/Global/RicciNorm.lean` (+ report). Do NOT touch ScalarVariation.lean / ScalarEvolution.lean — a parallel worker owns them.

Read `harness/reports/M4-ivey-1_done.md`. On main: the unproven `TracelessPinchingEigenvalueImprovementLemma3` Prop, `diagonalTracelessPinchingReactionNumerator3` with its four pins ((1,1,1)=0; (1,1,2)=−16+8δ; (1,2,3)=−64+56δ; near-degenerate saturation), and the admissible range `0 ≤ δ ≤ 6ε²/(1−2ε+3ε²)`; plus the goal-5 Schur-form suite (`diagonalPinchingReactionSignNumerator3_eq_schur` etc.) as the algebraic playbook.

Deliverable — PROVE the eigenvalue lemma: for eigenvalues with the ε-pinching hypothesis (each λᵢ ≥ ε·(λ₁+λ₂+λ₃) > 0) and δ in the admissible range, `diagonalTracelessPinchingReactionNumerator3 δ λ₁ λ₂ λ₃ ≤ 0`.

Route: decompose the numerator as [the proven goal-5 Schur nonpositive part] + δ·[the positive correction], then bound the correction by the Schur part under the pinching hypothesis — the saturation computation in the ivey-1 report shows the bound is TIGHT at the admissible boundary, so expect a factored/SOS form with equality at the degenerate pattern; `nlinarith`/`polyrith` with well-chosen auxiliary square terms (products of eigenvalue differences and the pinching slack (λᵢ − εR)). If the full range stalls, prove a CONCRETE smaller range first (e.g. δ ≤ 3ε²) — an explicit δ(ε) > 0 is all the downstream argument needs; note the gap honestly.

Commit granularity: decomposition lemma / correction bound / the final lemma. Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm`, report names.
