Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-45: the cyclic cancellation — finish the closed second Bianchi

Read `harness/reports/M3-predicates-44_blocked.md` (exact goal + missing atoms). On main: `closedCurvatureEntryDerivAt`, `closedCurvatureCovDerivAtCorrectionAt`, the cyclic scalar-paired expansion theorem (predicates-44), the canonical curvature entry bridge, all Schwarz/slot machinery.

Remaining per the report: expose the CONNECTION-DERIVATIVE terms inside the cyclic expansion — the closed analogue of the model's route: `fderiv_coordCurvatureOp_family` + unfolding `coordCurvatureOp` + Christoffel symmetry + mixed-second-derivative symmetry + `abel`.

Closed steps (each its own commit):
1. **Unfold the closed curvature**: the closed curvature values (whatever `ricciAt`/the scaffold use — `CovariantDerivative.curvatureOp` of `g.leviCivita` presumably; READ the definition) = ∇∇ − ∇∇ − ∇_[,] combinations of connection values. Prove the closed `curvatureOp`-unfolding lemma expressing `closedCurvatureEntryDerivAt` in second-connection-derivative + Γ·Γ terms (the model's `fderiv_coordCurvatureOp_family` analogue — differentiate the curvature's defining formula through the entry machinery; the `covDeltaGamma_koszul` proof did this exact move for the Koszul identity).
2. **The cancellation**: in the cyclic sum, apply (i) Christoffel symmetry (`leviCivita_torsionFreeAt` / the connection's symmetric slots), (ii) the closed Schwarz lemmas for the ∂∂Γ mixed terms, (iii) `abel`/`ring` for the final bookkeeping — the model's `coord_second_bianchi` endgame verbatim.
3. **Conclude** the cyclic identity in the exact hypothesis shape of `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` (on main).
4. If budget: attack last-atom #2 (the middle curvature-divergence trace identification, hMiddle — a Gram-contraction bookkeeping lemma) → if BOTH land, the consumer chain fires through `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` → **THE HAMILTON THEOREM COMPLETES**. State the final wrappers + historic done-report.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
