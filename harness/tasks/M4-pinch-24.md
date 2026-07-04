Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-24: roadmap step 6 — the maximum principle on Q → HAMILTON PINCHING PRESERVATION

Read `harness/reports/M4-pinch-23_done.md` (max-principle outlook). ALL analytic inputs are UNCONDITIONAL on main:
1. `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` — the quotient evolution (equality/inequality with gradient damping + reaction remainder).
2. The gradient-square damping term ≤ 0 (structural nonnegativity of the completed square).
3. `pinchingReactionRemainderAt_nonpos_of_scalar_pos` — reaction ≤ 0 at R > 0 in 3D.
4. The closed parabolic MINIMUM-principle machinery from goal 3 (ScalarEvolution.lean: `exists_scalarAt_isMinOn`, `laplacianAt_nonneg_of_isLocalMin`, `scalarMinimumAt/Track`, `hamilton_scalar_lower_bound` — READ these as the template; a MAXIMUM of Q needs the mirrored lemma `laplacianAt_nonpos_of_isLocalMax` — derive from the min version applied to −Q or prove directly the same way).

Deliverables (each its own commit):
1. **Compactness witness**: `exists_pinchingQuotientAt_isMaxOn` — at each time, Q attains a maximum on the closed manifold (mirror `exists_scalarAt_isMinOn`; Q is continuous where R > 0 — carry the positive-scalar hypothesis as the flow preserves it: `hamilton_scalar_nonneg_preserved`/the R_min lower bound from goal 3 give R ≥ R_min(0) > 0 under positive initial scalar).
2. **At a spatial max of Q**: ΔQ ≤ 0 and ∇Q = 0 (the local-max lemmas) → from the quotient evolution, `d/dt Q(max) ≤ reaction ≤ 0`-shape pointwise.
3. **THE PRESERVATION THEOREM**: `hamilton_pinching_preserved` — along a closed 3D Ricci flow with R > 0, the maximum of `pinchingQuotientAt` is nonincreasing (state in the same style as `hamilton_scalar_lower_bound`: a Track/monotonicity statement with honest regularity + the time-derivative-of-max machinery from goal 3 — reuse its Dini-derivative/track pattern verbatim). Equivalently: if `|Ric|² ≤ C·R²` at t=0 then it holds for all later t. Historic done-report.

If the max-track machinery needs a mirrored lemma not on main, prove it (the goal-3 proofs are the literal template with inequalities flipped). Standing protocols. No sorry/axiom. BUILD NOTE: be patient with builds, use `lake env lean` per-file. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`, report names.
