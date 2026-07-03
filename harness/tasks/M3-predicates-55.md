Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-55: hMiddle + THE FINAL ASSEMBLY — the Hamilton theorem

The cyclic second Bianchi is PROVEN on main (`eventually_closed_cyclic_second_bianchi`, unconditional). ONE lemma + assembly remain for the entire two-day Hamilton campaign:

1. **hMiddle** (the sole remaining mathematical lemma): the hypothesis of `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` (ScalarVariation.lean ~6423) —
   `∀ᶠ y, ∀ w, Σᵢ closedCurvatureDivergenceAt g y w (♯bⁱ) (bᵢ) = closedRicciDivergenceTraceAt g y w`
   (read the exact statement). This is Gram-contraction bookkeeping: both sides are basis-contracted curvature-derivative traces — unfold the two definitions (predicates-36 scaffold), match via the raw contraction lemmas + `sum_metricDualVectorAt_contraction_swap` + Ricci-derivative slot symmetry (all on main). If a mismatch survives, paste it exactly.
2. **THE CHAIN** (all consumers on main, verified waiting):
   `eventually_closed_cyclic_second_bianchi` + hMiddle → `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` → `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` (its two scalar side hypotheses: `ContMDiffAt 2 (scalarAt)` and the extDerivFun-field differentiability — discharge from g's ∞-smoothness via the ContMDiff/canonical-instance machinery; the scalarAt smoothness should follow from the C² curvature instances + the Gram trace form) → **`ClosedContractedBianchiAt g x` for every x — DISCHARGED**.
3. **THE THEOREM**: state and prove the final `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` — `IsClosedRicciFlowSolutionAt` + honest regularity classes → `SatisfiesHamiltonScalarEvolutionAt` — by feeding the discharged Bianchi predicate into the existing `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail`/`..._of_traceDerivativePredicates` wrappers (read which wrapper shape is cleanest). Plus the final `hamiltonScalarEvolutionProgram_of_...` form.
4. **HISTORIC DONE-REPORT**: `harness/reports/HAMILTON_THEOREM_DONE.md` — the theorem names, the honest hypothesis list (regularity classes with their witnesses), and the axiom closure.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
