Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-38: ONE atom — the moving-point Ricci derivative expansion

SCOPE: one theorem family. Read `harness/reports/M3-predicates-37_blocked.md`. The Bianchi endgame needs:

`covTensor2DerivAt g (ricciVariationField g) x v u w = closedCovRicciDerivAt g x v u w`

i.e. the covariant derivative of the closed Ricci FIELD (LHS: the generic covTensor2DerivAt applied to the Ricci bilinear entries) equals the curvature-level covariant Ricci derivative (RHS: `closedCovRicciDerivAt`, defined in the predicates-36 scaffold from `closedCurvatureCovDerivAt` traces — read both definitions FIRST). Model analogue: `covRicciDeriv_eq_tensor_deriv` (ModelLaplacian — read its proof; it is the computation to replay).

Route (the proven pattern): the LHS unfolds to `extDerivFun` of the Ricci entries `y ↦ g.ricciAt y (ext u)(ext w)` minus Christoffel slot corrections. The Ricci entries are curvature traces (`ricciBilinearAt` of the canonical connection) — differentiate the trace via the Gram/dual-basis machinery (the trace-derivative pattern, discharged many times: the derivative of a g-contracted trace = trace of the covariant derivative + cancelling corrections). The inner object is the curvature values, whose derivative gives `closedCurvatureCovDerivAt` + corrections (the connection-value entry bridges — `DeltaGammaEntryDerivativeBridgeAt`'s proof differentiated connection-value pairings; here it's second-level: curvature = derivative-of-connection combinations, so the C²/C³ classes and the closed Schwarz lemmas carry it). Honest new regularity fields fine (+ static witnesses).

If it lands with budget: chain into bridges (1)/(2) of the predicates-37 list (they were reduced to exactly this), and note the remaining bridge-(3) state.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
