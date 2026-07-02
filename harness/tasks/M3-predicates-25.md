Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-25: the cyclic ∇δΓ trace identity (the keystone swap, closed version)

Read `harness/reports/M3-predicates-24_blocked.md`. ONE identity remains for the divergence-side assembly:
`Σᵢ g((∇_u δΓ)(eᵢ, ♯eⁱ), w) = Σᵢ g((∇_{eᵢ} δΓ)(w, u), ♯eⁱ)`-shape (read the exact frozen form in the report/file — the swap of differentiation direction with a contraction slot for `covDeltaGammaDerivAt`).

MATHEMATICAL CONTEXT (important): this is the closed analogue of THE KEYSTONE step of the single-chart scalar-evolution proof, and it is CURVATURE-FREE — the model file proved it (see `deltaGammaDivergence_symm` ~line 11032, `sum_raised_contraction_swap`, and the ∇²h route in ModelLaplacian.lean; the repo memory records the winning route: express δΓ via the differentiated Koszul form so ∇δΓ becomes ∇²h + corrections, then the direction-slot swap is Schwarz symmetry of ∇²h under the SYMMETRIC double trace + the raised-contraction swap lemma).

Closed route:
1. `deltaGamma_koszul` (on main) expresses 2·g(δΓ(p,q),z) in ∇h 3-term form. Differentiate it once more (the C² classes + closed Schwarz lemmas on main): 2·g((∇_v δΓ)(p,q),z) = [∇²h terms] + [first-order corrections] — commit as the `covDeltaGamma_koszul` lemma.
2. Contract BOTH sides of the target identity through step 1: each becomes a combination of double-traced ∇²h terms + corrections. The ∇²h double traces match under Schwarz (`extDerivFun` Schwarz lemmas on main; antisymmetric parts vanish under the symmetric trace) + `sum_metricDualVectorAt_contraction_swap`; the corrections match by the slot-cancellation lemmas.
3. Discharge `DeltaGammaInnerTraceFieldCovariantDerivativeAt` via the cascade (`deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge` on main + this identity) → `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` discharged → BOTH assemblies closed. Consolidated Hamilton wrapper + notes with the final predicate list (should be: regularity classes + ClosedContractedBianchiAt + 3 substitution predicates).

This is the deepest remaining identity — partial ∇²h-form progress + exact goal state is success. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
