Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-27: the cyclic trace identity via covDeltaGamma_koszul → close the divergence assembly

On main (all gate-verified): `covDeltaGamma_koszul` — `2·g(covDeltaGammaDerivAt u v w, z)` = three `covTensor2SecondDerivExpansionAt` terms (∇²h shapes in slot patterns (v,z | w,z | z,v w)) minus 2·[three δΓ·Γ correction pairings]. Plus: the closed Schwarz lemmas, `sum_metricDualVectorAt_contraction_swap`, the slot-cancellation lemmas, `deltaGammaDivergenceAt_eq_inner_sum`, `deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge`, and the frozen cyclic identity in `harness/reports/M3-predicates-24/25_blocked.md`.

Deliverable: prove the frozen cyclic identity
`Σᵢ g((∇_u δΓ)(eᵢ, ♯eⁱ), w) = Σᵢ g((∇_{eᵢ} δΓ)(w, u), ♯eⁱ)`-form (exact statement per the report), by:
1. Substituting `covDeltaGamma_koszul` into BOTH sides (per-summand; each side becomes 3 double-traced ∇²h expansion terms − corrections).
2. Matching the ∇²h double traces pairwise: the direction/slot swaps under the (eᵢ, ♯eⁱ) symmetric trace are Schwarz (`extDerivFun` symmetry lemmas) + the raised-contraction swap (`sum_metricDualVectorAt_contraction_swap`) — six terms each side; work them term-by-term, one commit per matched pair if needed.
3. Matching the δΓ·Γ corrections: same swap machinery (first-order, no Schwarz needed).
4. Cascade: cyclic identity → `DeltaGammaInnerTraceFieldCovariantDerivativeAt` → `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` → BOTH HESSIAN ASSEMBLIES CLOSED. Consolidated Hamilton wrapper (remaining: regularity classes + ClosedContractedBianchiAt + substitution predicates); notes with final list.

Heavy bookkeeping, zero new mathematics — everything reduces to lemmas on main. One matched pair per commit is acceptable granularity. Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
