Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-5: pinching roadmap step 2 — the 3D Ricci reaction specialization

On main: `RiemannDeterminedByRicci3At_closedCurvature` (3D curvature = Ricci decomposition, PROVEN), the PINNED 3D reaction coefficients (`2Rm(Ric,·) = 3R·Ric − 4Ric² + (2|Ric|² − R²)g`, validated on two test patterns — M4-pinch-2's landing in RicciNorm.lean), and the proven Ricci evolution equation with its `2·lichnerowiczCurvatureAt` term.

Deliverable (roadmap step 2): under n = 3, rewrite `2·lichnerowiczCurvatureAt g (ricciVariationField g) x u w` via the decomposition theorem into the pinned reaction form — i.e. prove the pinned identity as a THEOREM (not just a coefficient validation): substitute `RiemannDeterminedByRicci3At_closedCurvature` into `lichnerowiczCurvatureAt`'s definition (the mixed curvature contraction — the decomposition replaces the Rm entries by the Ric/g Kulkarni-Nomizu combination), contract (the Gram/trace machinery + the KN-contraction algebra), and land:
`ricciEvolution3ReactionAt`: in 3D, the Ricci evolution RHS = `roughTensorLaplacianAt + 3R·Ric − 6Ric² + (2|Ric|² − R²)g`-shape (per the pinned `reaction` combination — read the exact pinned statement in RicciNorm.lean and match it literally).

Then (if budget): roadmap step 3 — expand `d/dt |Ric|²` via the reaction form + the metric-motion terms (the |Ric|² derivative vocabulary from M4-pinch-1).

Standing protocols (space-form + diagonal checks on every landed identity). No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
