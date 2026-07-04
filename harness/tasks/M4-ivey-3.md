Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-3: general-exponent quotient calculus (ScalarEvolution/ScalarVariation ONLY)

SCOPE: do NOT touch `Poincare/Global/RicciNorm.lean` — a parallel worker owns it. Work in ScalarEvolution.lean (preferred; smaller) and ScalarVariation.lean only where unavoidable.

Read `harness/reports/M4-ivey-1_done.md` (roadmap items 1+4). On main: the exponent-2 quotient calculus (pinch-18 `laplacianAt`/`gradientAt` quotient lemmas, the pinch-21 spatial expansion + Gram bridges, the completed-square machinery) and the ivey-1 evolution-target vocabulary.

Deliverables (each its own commit) — generalize the quotient calculus from R² to R^(2−δ) at points with scalarAt > 0:
1. **Real-power composition lemmas**: `gradientAt`/`laplacianAt` of `fun y => (scalarAt y)^p` for real p at R > 0 (chain rule through `Real.rpow` — Mathlib has `Real.hasDerivAt_rpow_const`; compose with the scalar's differentiability; deliver `gradientAt_scalar_rpow`, `laplacianAt_scalar_rpow` with the p·R^(p−1)-shape and p(p−1)·R^(p−2)|∇R|² terms).
2. **The general quotient lemmas**: d/dt, ∇, Δ of `u/R^p` (u = the traceless norm or |Ric|²) via the (u/R^p)·R^p product-rule trick — mirror the pinch-18 proofs with the rpow lemmas replacing the square lemmas.
3. **The completed-square exponent coefficient** (roadmap item 4): the gradient-damping completed square generalizes with a p-dependent coefficient — state and prove the p-version of the pinch-21 spatial expansion OR the honest reduction lemma to it (whichever is achievable; commit partials).
4. Report: exactly what the evolution assembly (roadmap item 3) still needs.

BUILD NOTE: be patient with builds; `lake env lean` per-file. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`, report names.
