Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-5: absorb the gradient defect — the |∇Ric|² reserve route

Read `harness/reports/M4-ivey-4_progress.md` — the literal remaining goal is the sign/control of the gradient defect `δ·((N + R²/3)·S − 2R·B)` with S = |∇R|², B = the mixed pairing, N = |Ric|².

ORCHESTRATOR GUIDANCE — the classical resolution (Hamilton 1982 §11) uses the GRADIENT RESERVE, not the reaction lemma:
1. **The trace-gradient Cauchy–Schwarz**: `∇R = trace of ∇Ric` pointwise (metric compatibility: the covariant derivative of the trace = trace of the covariant derivative — the trace-commute machinery on main proves `extDerivFun scalarAt = trace of covRicci`-shape; check the pinch-9..12 layer for the exact lemma). Hence pointwise `S = |∇R|² ≤ 3·covRicciNormSqAt` (Cauchy–Schwarz on the g-trace over the 3D fiber — Gram algebra) and `|B| ≤ √S·√(N-related)·...` — more directly, B is a contraction of ∇Ric against ∇R⊗Ric, so `|B|² ≤ covRicciNormSqAt·S·N`-shape (Cauchy–Schwarz twice).
2. **The reserve**: the traceless parabolic form came from the Bochner EQUALITY `Δ|Ric|² = 2⟨ΔRic,Ric⟩ + 2·covRicciNormSqAt` — the assembly so far DISCARDED the `−2·covRicciNormSqAt`-strength when it passed to ≤. REDO the item-5 assembly keeping the explicit `−(2−c(δ,ε))·covRicciNormSqAt` reserve, and absorb the defect: defect ≤ δ·C(ε)·covRicciNormSqAt via step 1's bounds + ε-pinching (N ≤ C·R² etc.), so for δ small (shrink the admissible range if needed — any explicit δ(ε) > 0 suffices) the total gradient contribution stays ≤ 0. PIN the absorption constants on gradient test data (flat + a linear-scalar pattern) informally in the report BEFORE proving.
3. **Land the improved evolution inequality** `satisfiesTracelessPinchingEvolutionAt_of_ricciFlow` (possibly with a smaller explicit admissible δ — honesty over sharpness). Done-report + the max-principle/blow-up outlook.

If the Cauchy–Schwarz layer needs new fiber lemmas, commit them separately. Standing protocols. No sorry/axiom. BUILD NOTE: patience with builds. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
