Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-3: CORRECT the Lichnerowicz curvature contraction + redo trace validation

Read `harness/reports/M4-prep-2_blocked.md` — `lichnerowiczCurvatureAt` (defined in M4-prep-1) traces the ANTISYMMETRIC first curvature pair and is identically-zero-traced (proven wrong). This is a sanctioned DEFINITION CORRECTION (the ledger records it; this is not a frozen-statement violation — the definition was refuted before any consumer proof existed):

1. **Correct the definition**: replace with the mixed Riemann/Ricci contraction the report suggests (`curvatureOp ... (extend E (b i)) (extend E u) (extend E w)` paired against `sharp i` — the standard Lichnerowicz curvature action `2·Σ R(eᵢ, u, w, eⱼ)·h(♯eⁱ,♯eʲ)`-shape; check the MODEL's `lichnerowiczLaplacian` definition in ModelLaplacian.lean for the authoritative slot convention and mirror it EXACTLY). Rename or version the def as needed; update `SatisfiesRicciEvolutionAt` to consume the corrected operator, and mark the old definition deprecated-with-comment (do not silently delete — the correction history matters).
2. **Immediate sanity gates** (before anything else): (a) constant-sectional-curvature informal check in the report — the corrected trace must NOT vanish; (b) flat/static: everything 0.
3. **Redo M4-prep-2's subtasks with the corrected operator**: the metric-trace identities (tr of rough Laplacian, curvature action, ricciQuadraticAt → the |Ric|²/ΔR shapes) + the regularity packaging + the TRACE CONSISTENCY lemma (trace of the corrected RicciEvolution RHS = the proven ΔR + 2|Ric|²).
4. Notes update: the corrected roadmap.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
