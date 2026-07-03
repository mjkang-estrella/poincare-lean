Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-15: differentiate the Bianchi one-form → the last atom → THE RICCI EVOLUTION EQUATION

Read `harness/reports/M4-prep-14_blocked.md`. ONE bridge remains before the assembled chain fires:
`∀ u w : TM x, ∇_u((div Ric)(w)) = ½ · g.hessianAt (scalarAt) x u w` (the free-slot differentiated contracted Bianchi — read the exact frozen shape in the report).

KEY: the UNDIFFERENTIATED identity is PROVEN on main — `ClosedContractedBianchiOneFormAt g y` holds ∀ᶠ y near x (via the Bianchi campaign: the `of_closed_trace_contraction_canonical` chain provides it — check the exact exported form; if only the traced consequence was exported, the one-form identity near x is `tensorDivergenceOneFormAt g (ricciVariationField g) y w' = ½ extDerivFun scalarAt y w'` — grep for its ∀ᶠ export or re-derive from the proven ingredients, it was the M3-predicates-33..42 payload).

Route: differentiate the ∀ᶠ one-form identity in the direction u at x (both sides are differentiable — LHS by the canonical Ricci/divergence regularity instances, RHS by scalar C³): `extDerivFun` of LHS = ∇ᵤ(div Ric)(w) + corrections (the covTensor1-style expansion — the entry machinery); `extDerivFun` of RHS = ½·[second derivative of scalarAt] = ½·hessianAt + the SAME-shape corrections (the `extDerivFun_extDerivFun_extend_eq_hessianAt_add` identity); the corrections cancel (both sides' Christoffel terms match since the identity holds on a NEIGHBORHOOD — differentiating an equality of fields gives equality of derivatives, corrections included). Conclude the frozen bridge.

Then: feed it into the blocked cancellation → `RicciSecondDerivCurvatureCommutationAt` DISCHARGED → `satisfiesRicciEvolutionAt_of_ricciFlow_curvatureCommutation` fires → **THE RICCI TENSOR EVOLUTION EQUATION**. Historic done-report.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
