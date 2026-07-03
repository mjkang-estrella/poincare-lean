Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-2: pinching roadmap steps 1-2 (the 3D curvature decomposition + evolution specialization)

Read the roadmap in `Poincare/Global/ScalarVariation.lean` (~M4-pinch-1 landing) and its report. Execute steps 1-2 (each its own commit):

1. **Step 1 — `riemannFromRicci3At` = the actual curvature in 3D**: prove that in dimension 3 (n = 3 hypothesis), the closed curvature values (`curvatureOp` of `g.leviCivita` on extend sections, g-paired) equal the `riemannFromRicci3At` decomposition (Ric∧g-terms − (R/2)·g∧g-shape — the definition on main, coefficient-pinned). Route: both sides are tensorial with the same symmetries; in 3D the Weyl tensor vanishes — but do NOT build Weyl theory: the direct route is dimension-specific linear algebra (a (0,4) tensor with Riemann symmetries in 3D is determined by its Ricci trace — prove the pointwise fiber statement over a 3-dim inner-product space as an abstract lemma, then apply; the fiber is E = EuclideanSpace ℝ (Fin 3)). PIN with the space-form check (both sides = k(g∧g)-shape).
2. **Step 2 — specialize the Ricci evolution through the decomposition**: rewrite the `2·lichnerowiczCurvatureAt` term of the PROVEN Ricci evolution RHS via step 1 into pure Ricci-quadratic vocabulary (in 3D, Rm(Ric,·) = the pinned combination of Ric², R·Ric, |Ric|²·g, R²·g terms — derive the exact 3D coefficients from step 1's decomposition and VALIDATE on both test patterns before proving).

Standing protocols (coefficient-pin everything). No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
