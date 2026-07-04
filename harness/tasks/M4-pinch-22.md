Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-22: manifold-level reaction sign (spectral transport of the eigenvalue lemmas)

Read `harness/reports/M4-pinch-21_done.md` (step-6 outlook). On main: the UNCONDITIONAL quotient evolution (`satisfiesPinchingQuotientEvolutionAt_of_ricciFlow`, with `pinchingReactionRemainderAt` the reaction term and the gradient damping ≤ 0 already structural), and the eigenvalue reaction-sign suite in RicciNorm.lean (`diagonalPinchingReactionSignNumerator3_nonpos` — the Schur form, nonpos for ALL triples; `diagonalPinchingReactionRemainder3_nonpos_of_scalar_pos`; the four verification pins).

Deliverable — transport the sign to the manifold: `pinchingReactionRemainderAt g x ≤ 0` at points with `scalarAt x > 0` in dimension 3 (check whether Ric ≥ 0 is even needed — the eigenvalue lemma held unconditionally; the only hypotheses should be n = 3 and R > 0):
1. **Spectral decomposition of the Ricci endomorphism** over the 3D fiber: `g.ricciEndoAt x` is symmetric w.r.t. the inner product (on main: `ricciAt_symm`) — apply/derive the finite-dimensional spectral theorem (Mathlib: `LinearMap.IsSymmetric.eigenvectorBasis` over a real inner-product space; the fiber needs its InnerProductSpace structure w.r.t. g-inner — the Gram-orthonormalization machinery from the pinch campaign (`metricOrthogonalBasisAt`) may serve as the frame). Deliver: an orthonormal-in-g eigenbasis with eigenvalues λ₁,λ₂,λ₃.
2. **Rewrite the invariants**: `scalarAt = λ₁+λ₂+λ₃`, `ricciNormSqAt = Σλᵢ²`, `tr(Ric³) = Σλᵢ³` in the eigenbasis (trace-basis-invariance — the merged trace machinery).
3. **Rewrite `pinchingReactionRemainderAt` through the diagonal expression** = `diagonalPinchingReactionRemainder3 λ₁ λ₂ λ₃`-shape (definition match after step 2) → apply `diagonalPinchingReactionRemainder3_nonpos_of_scalar_pos` → **`pinchingReactionRemainderAt_nonpos_of_scalar_pos`** (n = 3).
4. Done-report + the final step-6 outlook: the maximum principle on Q (the closed parabolic max-principle machinery from goal 3 — `scalarMinimumAt/Track` patterns — applied to the quotient with the now-nonpositive reaction).

If the spectral-theorem instantiation stalls, commit the invariant-rewrite layer + paste the literal goal. Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
