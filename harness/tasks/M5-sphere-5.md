Read harness/worker_contract.md first and obey it strictly.

# Task M5-sphere-5: GOAL 8 opener — scope + begin discharging the Killing–Hopf interface

GOAL 8: shrink `PositiveConstantCurvatureSpaceForm3` (SphereTheorem.lean) — the more tractable of the two remaining interfaces. This is a SCOPE + FIRST-REDUCTIONS task:

1. **Decompose the interface** (report): Killing–Hopf for k > 0 factors as (a) a complete simply-connected 3-manifold of constant curvature k is isometric to the round S³(1/√k) — the universal-cover model theorem; (b) closed ⟹ complete (Hopf–Rinow side); (c) the repo already assumes simply connected, so no quotient step is needed. For (a), the classical proof: exponential-map comparison / Cartan's theorem on determination by curvature. INVENTORY Mathlib: geodesics (`Mathlib.Geometry.Manifold`... search for exponential map, complete Riemannian, Hopf–Rinow, Cartan–Hadamard, constant curvature model spaces, `EuclideanSpace` sphere geometry), and the repo's quotient-covering/deck machinery (survey said it exists — locate it). Honest difficulty per piece.
2. **Statement-layer reductions** (Lean commits): restate the interface as the conjunction of SMALLER named interfaces reflecting the decomposition (e.g. `CompleteOfClosed3`, `CartanConstantCurvatureRigidity3`, wire `PositiveConstantCurvatureSpaceForm3` as their consequence via a proven composition theorem) — each smaller interface should be independently attackable and independently citable. The composition theorem IS the deliverable (proven; the pieces stay hypotheses).
3. **Discharge the cheapest piece** if any is within reach (e.g. if Mathlib has closed ⟹ complete for the repo's metric-space structure — `hamilton`... the `MetricSpace` instance from goal 1's chain + compactness gives completeness OUTRIGHT: `CompactSpace ⟹ CompleteSpace` is Mathlib-trivial — check the interface shape actually needs Riemannian completeness vs metric completeness and discharge if trivial).
4. Report + roadmap for the remaining pieces.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.SphereTheorem`, report names.
