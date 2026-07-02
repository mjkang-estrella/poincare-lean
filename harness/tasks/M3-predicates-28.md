Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-28: CORRECTED route — evaluate the divergence trace directly via covDeltaGamma_koszul

CONTEXT CORRECTION (read `harness/reports/M3-predicates-27_blocked.md`): the cyclic identity frozen in the predicates-24/25 reduction is FALSE (counterexample on the flat torus). The two ∇δΓ trace orders differ by exactly the δRic trace — that difference IS the Lichnerowicz identity. So do NOT equate them. The correct route: evaluate the divergence-order trace DIRECTLY.

Mathematical target (matches the single-chart model's proven decomposition — memory/RIEMANNIAN_FOUNDATION: sub-identities (a) ½ΣΣ(T1+T2) = div div h and (b) ½ΣΣT3 = ½Δ(tr h)): the trace `Σᵢ g((∇_{eᵢ} δΓ)(·slots·), ♯eⁱ)`-shapes evaluate, via `covDeltaGamma_koszul` (on main: 2·g(∇δΓ, z) = 3 covTensor2SecondDerivExpansionAt terms − δΓ·Γ corrections), to combinations of:
- `tensorDoubleDivergenceAt h` (from the T1/T2-pattern double contractions of ∇²h) and
- `laplacianAt (traceMetricVariationAt h)` (from the T3-pattern: the H-slot trace of ∇²h = Hessian of tr h — the trace-commute; note `TraceMetricVariationDerivAt` (discharged!) is its first-order version; its once-differentiated form may be needed — derive from the C² classes).

Deliverables (each its own commit):
1. Substitute `covDeltaGamma_koszul` into the inner-trace-field covariant-derivative target (`DeltaGammaInnerTraceFieldCovariantDerivativeAt`'s frozen statement — re-read it; given the false-identity episode, FIRST sanity-check the frozen statement against the flat-torus counterexample pattern: compute both sides for the static/flat case and for the model h₁₁ = cos y torus INFORMALLY in the report; if the frozen statement is also false, file the correction analysis instead of proving — do NOT prove false things, do NOT silently alter frozen statements).
2. Assuming the statement is true (or after documenting its corrected form): evaluate the three ∇²h double-trace groups: (T1/T2) → double divergence; (T3) → Laplacian-of-trace; corrections → cancel/absorb via the slot-cancellation lemmas.
3. Close `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` (or file its corrected form + the corrected adapter chain).
4. Notes with the verified remaining predicate list.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
