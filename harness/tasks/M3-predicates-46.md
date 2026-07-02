Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-46: curvature_koszul — differentiate the curvature's defining identity (three-commit replay)

SCOPE: one lemma family, by STRICT structural replay of a proof already on main. The atom (per `harness/reports/M3-predicates-45_blocked.md`): expand `closedCurvatureEntryDerivAt` into second-connection-derivative + connection-product terms.

THE TEMPLATE — `deltaGamma_koszul` → `covDeltaGamma_koszul` (predicates-26, on main; READ its three commits' worth of code first: `deltaGamma_koszul_eventually` [field identity], `deltaGamma_koszul_extDerivFun` [differentiate], `covDeltaGamma_koszul` [solve]). Your task is the IDENTICAL three-step move with the curvature's defining identity in place of the Koszul identity:

1. **Field identity** (`curvature_def_eventually`): near x, the curvature entries `g.inner y (curvatureOp-values on extend sections) (extend z)` = the defining combination [∇∇ − ∇∇ − ∇_bracket] of connection values paired with g — this is close to definitional (unfold `CovariantDerivative.curvatureOp` / whatever `ricciAt` uses; state it as an honest field equation over y with the extend sections).
2. **Differentiate** (`curvature_def_extDerivFun`): apply extDerivFun to both sides at x — LHS: `closedCurvatureEntryDerivAt` + metric product-rule corrections (the canonical entry-bridge machinery); RHS: term-by-term — the ∇∇ terms give second connection derivatives (the `DeltaGammaEntryDerivativeBridgeAt`-proof product rule, with connection values in the h-slot — the connection's own entries are differentiable by the C² instance), bracket terms via the mlieBracket lemmas already used in the transport chain.
3. **Solve** (`closedCurvature_koszul`): rearrange to the expansion of `closedCurvatureEntryDerivAt` — the closed `fderiv_coordCurvatureOp_family` analogue. Static/flat sanity check.

Do NOT attempt the cyclic cancellation in this task (next task) — land the expansion only. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
