Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-1: consolidation audit of the goal-4/5/6 theorem chain

Six goals are gate-verified on main. Before opening the next front (Hamilton §11-17 convergence or the M2 short-time wall), run a CONSOLIDATION AUDIT of the M4 chain — the fastest-built stretch, hence the most worth auditing:

1. **Statement-strength audit**: for each headline theorem — `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`, `hamilton_pinching_preserved`, `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow`, `hamilton_pinching_improvement`, `hamilton_eigenvalue_pinching_floor_preserved` — print the FULL statement (`#check`/source read) and list in the report: (a) every hypothesis, flagging any that is vacuous-prone (e.g. an instance/class that might be unsatisfiable, a Track structure that might have no inhabitants) or stronger than the informal theorem needs; (b) whether the conclusion actually says what the docstring claims (no hidden trivialization: e.g. a ≤ that holds because both sides are the same term, a max over an empty set).
2. **Inhabitation spot-checks**: for the 2-3 most suspicious hypothesis-bundles (e.g. the regularity class combos on the flow, the Track structures), verify non-vacuity: construct or point to an instance (the static Ricci-flat/space-form flows from the earlier campaigns are the natural witnesses — `isClosedRicciFlowSolutionAt` static instances exist on main). If a bundle has NO possible inhabitant, that's a critical finding — report immediately.
3. **Axiom re-audit**: `#print axioms` on all five (should be exactly propext, Classical.choice, Quot.sound — the gate checked each, re-confirm the set on the current main).
4. **Report**: an honest-strength assessment — what is genuinely proven vs. what is conditional on plausible-but-uninstantiated regularity classes; the exact gap list for turning conditional statements into instantiated ones.

NO new theorems required; this is a read+report task (small lemmas to witness inhabitation are welcome). Standing protocols. `lake build Poincare` if touched, report names.
