Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-20: roadmap step 5 — the 3D reaction-sign lemma (fiberwise algebra, RicciNorm.lean ONLY)

SCOPE: work ONLY in `Poincare/Global/RicciNorm.lean` (+ report). Do NOT touch ScalarVariation.lean or ScalarEvolution.lean — a parallel worker owns them.

On main: `pinchingReactionRemainderAt` (ScalarVariation.lean, from pinch-18 — READ its definition for the exact normalization; it is the combination `N_react/R² − 2N·R_react/R³`-shape built from the pinned 3D reaction/motion traces) and the diagonal pin lemmas (`diagonal...RicciNorm...` family in RicciNorm.lean: on (1,1,2) the remainder = −1/4; on space forms = 0).

Deliverable — Hamilton's 3D reaction-sign lemma, AS FIBERWISE ALGEBRA in RicciNorm.lean:
1. **State the pointwise algebraic core** over eigenvalue triples: for λ₁,λ₂,λ₃ ≥ 0 (the Ricci eigenvalues, 3D) with R = λ₁+λ₂+λ₃ > 0 and N = λ₁²+λ₂²+λ₃², the reaction combination [write it out from the pinned traces: N_react = 2·⟨reaction,Ric⟩-trace + 4tr(Ric³)-motion = the polynomial in λᵢ the pinned diagonal lemmas encode — DERIVE the polynomial from those pins, verify against (1,1,2) → −1/4·R²... careful with normalizations] satisfies `R·N_react − 4N·N... ≤ 0`-shape (the exact inequality that makes `pinchingReactionRemainderAt ≤ 0`). VALIDATE the polynomial identity on (1,1,2), (1,2,3), (1,1,1), (1,0,0) BEFORE proving. NOTE: Hamilton's lemma may need the STRONGER hypothesis (e.g. it holds for λᵢ ≥ 0 in 3D — check (1,0,0): if it FAILS there, identify the correct hypothesis domain, e.g. pinched eigenvalues, and report; do not force).
2. **Prove the polynomial inequality** (nlinarith/polyrith territory — SOS decompositions help; commit the eigenvalue-level lemma even if the manifold-level transport is left for the next task).
3. **Report**: the manifold-level transport plan (eigenvalue decomposition of the symmetric Ricci endomorphism — spectral theorem over the 3D fiber; what vocabulary is missing).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm`, report names.
