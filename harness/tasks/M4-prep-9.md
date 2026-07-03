Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-9: the closed (0,2) tensor Ricci identity (discharge slice 1)

Read `harness/reports/M4-prep-8_done.md` — its "Remaining slice plan" item 1 is this task:

Prove the closed tensor Ricci identity: `covTensor2SecondDerivAt` ANTISYMMETRIZED in its first two (derivative-direction) slots = `covTensor2SecondDerivCurvatureActionAt` (the curvature action on the 2-tensor — definition on main from M4-prep-8).

Routes (the report names both; pick after a quick probe):
(a) Reproduce the model's `covTensor2SndDeriv_ricci_identity` proof natively using `extDerivFun_covTensor2DerivAt_extend_eq_secondDerivExpansion` + the closed curvature/Koszul entry lemmas (`closedCurvature_koszul`, `closedCurvatureCovDerivAt_inner_koszul_expansion` — on main) — the covDeltaGamma_koszul-style "differentiate the definition, cancel by Schwarz, recognize curvature" replay; the antisymmetrization makes the Schwarz-symmetric blocks CANCEL, leaving exactly the curvature terms (the mirror image of the second-Bianchi cancellations already proven).
(b) Chart transport of the model identity (historically stalls at derivative level — prefer (a)).

Then (if budget): slice 2 — specialize to `ricciVariationField g` (mostly instantiation; the canonical Ricci regularity instances supply hypotheses).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
