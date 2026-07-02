Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-34: div Ric = ½ dR on closed manifolds — the final identity

Read `harness/reports/M3-predicates-33_blocked.md`. The Hamilton theorem's last mathematical content: the closed contracted Bianchi ONE-FORM identity — `tensorDivergenceOneFormAt g (ricci-field) x w = ½ · extDerivFun (scalarAt) x w` (locally/near x per the frozen consumer `ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near`, on main).

Model template (proven, self-contained from G C³): `fderiv_coordScalar_eq_two_ricciDivergenceForm_of_contDiff` (ModelLaplacian.lean; its route: `coord_second_bianchi` → double contraction; also `coord_twice_contracted_bianchi` ~6767). The classical proof: second Bianchi ∇R(X,Y,Z,·) cyclic sum = 0, contract twice with the metric.

Closed route (survey the exact closed curvature definitions first — `curvatureOp`/`ricciBilinearAt` in CurvatureTensoriality.lean and how `g.ricciAt` wires them):
1. **Closed second Bianchi**: the differentiated curvature identity. The curvature is built from the connection; its covariant derivative expands via the extend-calculus (the merged toolkit: extend-section derivatives, entry bridges, Schwarz lemmas). The model's `coord_second_bianchi` proof is the computational template — replay it in the extend frame at x (all objects anchored; the flat-derivative Schwarz + Jacobi-type cancellations close it — the FIRST Bianchi at manifold level (BianchiIdentity.lean) shows the repo's pattern for such cyclic identities).
2. **Double contraction**: contract with the Gram/dual-basis machinery (two traces — `sum_metricDualVectorAt_contraction_swap` et al.) → `div Ric = ½ dR` in exactly the frozen shape.
3. **Fire the consumer** → `ClosedContractedBianchiAt` DISCHARGED → state the FINAL theorems: `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` + program form, honest regularity classes only. Done-report worthy of the milestone.

This may need 2-3 sessions — decompose aggressively, land the second-Bianchi skeleton first. Standing sanity checks (flat/static: both sides 0). Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
