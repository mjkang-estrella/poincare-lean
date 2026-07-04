Read harness/worker_contract.md first and obey it strictly.

# Task M4-ivey-7: the max principle on the improved quantity → THE PINCHING-IMPROVEMENT THEOREM

ALL inputs UNCONDITIONAL on main:
1. `satisfiesTracelessPinchingImprovementEvolutionAt_of_ricciFlow` — the improved evolution (Δ + drift + reaction RHS; gradient absorption valid for the full predicate range).
2. `TracelessPinchingEigenvalueImprovementLemma3_holds` + the spectral transport machinery (pinch-22/23 pattern) — reaction ≤ 0 under ε-pinching + admissible δ ≤ 6ε²/(1−2ε+3ε²).
3. `hamilton_pinching_preserved` + the max-principle machinery (pinch-24: `exists_pinchingQuotientAt_isMaxOn`, `laplacianAt_nonpos_of_isLocalMax`, the C−Q trick with drift operator).
4. Goal 3's R_min machinery (`hamilton_scalar_lower_bound` — R grows under the Riccati bound; ε-pinching preservation is what keeps the reaction sign valid along the flow).

Deliverables (each its own commit):
1. **Spectral transport of the improved reaction sign** to the manifold: `tracelessPinchingReactionTermAt ... ≤ 0` at ε-pinched points with R > 0 and admissible δ (the pinch-23 eigenbasis-witness playbook verbatim, now feeding the ivey-2 lemma).
2. **ε-pinching preservation along the flow**: from `hamilton_pinching_preserved` (the quotient bound gives eigenvalue pinching in 3D — the eigenvalue algebra: |Ric|²/R² ≤ 1/3 + c ⟺ pinching; derive the needed implication `initial ε-pinching ⟹ ε'-pinching for all t` with explicit ε' — the RicciNorm eigenvalue toolkit; if this needs its own campaign, commit the statement + the algebra pins and report).
3. **The max principle on `tracelessPinchingAt δ`**: mirror pinch-24 (C − q trick, drift operator Δ + ((2−δ)/R)⟨∇R, ∇·⟩) → **`hamilton_pinching_improvement`**: the max of `|Ric°|²/R^(2−δ)` is nonincreasing along ε-pinched positive-scalar closed 3D flow, hence `|Ric°|²/R² ≤ C·R^(−δ)` — Hamilton's roundness estimate. Historic done-report.

Commit partials; paste literal goals on stalls. Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
