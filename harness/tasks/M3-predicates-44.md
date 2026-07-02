Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-44: the closed cyclic second Bianchi (last atom #1)

Read `harness/reports/` latest (predicates-43 done/blocked notes). On main: `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` proves the Hamilton theorem's final identity from TWO hypotheses. This task: the FIRST — the cyclic second Bianchi:

`∀ᶠ y in 𝓝 x, ∀ u v w z : TM y, closedCurvatureCovDerivAt g y v u w z + closedCurvatureCovDerivAt g y u w v z + closedCurvatureCovDerivAt g y w v u z = 0`

Model template: `coord_second_bianchi` (ModelLaplacian.lean — READ ITS PROOF COMPLETELY; replay it). Closed route:
1. Expand `closedCurvatureCovDerivAt` (predicates-36 scaffold definition) via the CANONICAL curvature entry bridge (on main, hypothesis-free): each term = flat derivative of curvature entries − Christoffel slot corrections.
2. The curvature entries themselves = connection-derivative combinations; their flat derivatives are second connection derivatives. In the cyclic sum: the ∂∂Γ terms cancel pairwise by the closed Schwarz lemmas (flat mixed-derivative symmetry — the model proof shows exactly which pairs), and the Γ·∂Γ terms cancel by the slot bookkeeping (model proof's second cancellation group).
3. The Christoffel corrections from step 1 cancel cyclically (the classical torsion-free cancellation — `leviCivita_torsionFreeAt` + the slot-cancellation lemmas).
4. Conclude at each y near x (the canonical instances give the regularity at every point — state ∀ᶠ via the ContMDiff vocabulary or plain ∀ y if the proof is pointwise-uniform).

Multi-session acceptable; land the expansion + first cancellation group minimum. NOTE: this is a FIXED metric, all-orders-smooth — no regularity walls expected, pure computation. Standing sanity checks (flat: all terms 0). Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
