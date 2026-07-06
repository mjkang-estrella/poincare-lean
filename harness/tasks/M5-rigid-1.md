Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-1: THE RIGIDITY CAMPAIGN OPENER — the candidate Cartan map

Context: the endgame interface `UnitConstantCurvatureSphereRecognition3` (`SphereTheorem.lean`) demands: closed simply connected `g` with constant sectional curvature 1 ⟹ `M ≃ₜ S³`. The classical Cartan/Killing–Hopf route: pick `x₀ : M` and `p₀ : RoundSphere3`; both metrics have constant curvature 1 (`roundSphereMetric3_hasConstantSectionalCurvature_one`, `RoundSphereWitness.lean`); the candidate local map `Φ := expAt_{p₀} ∘ L ∘ (expAt_{x₀})⁻¹` (with `L : E ≃ₗᵢ E` a chart-level linear isometry aligning the tangent metrics — at chart level both are `E = EuclideanSpace ℝ (Fin 3)` with the metrics `chartMetric g.inner` and `chartMetric roundSphereMetric3.inner` at the anchors; a Gram–Schmidt/`LinearIsometryEquiv` between two inner products on E) is a local homeomorphism matching the metrics up to Jacobi comparison. Available: complete exp local theory for BOTH metrics (all `GeodesicTransport` machinery is metric-generic), `expAtChartOpenPartialHomeomorph` (`ExponentialLocalHomeo.lean`), distance realization both sides, Jacobi/linearized machinery (`GeodesicLinearized.lean`, `GeodesicFlowDerivative.lean`).

OPENER SCOPE (statement + first genuine lemmas; the metric-preservation Jacobi comparison is the NEXT tasks):
1. In a NEW file `Poincare/Global/CartanMap.lean` (do NOT edit existing files, incl. `Poincare.lean`): construct the tangent-aligning `L` (a `LinearIsometryEquiv` between `E` with the two anchor chart metrics — via Mathlib's inner-product-space classification `LinearIsometryEquiv.ofInnerProductSpace`-style API or an explicit Gram–Schmidt; both metrics are positive-definite bilinear forms on E, dimension 3 — assess Mathlib's `BilinForm`/orthonormal-basis tooling).
2. Define `cartanMap g x₀ p₀ L : M → RoundSphere3`-shaped on the normal ball (junk outside; document) as the composition through the two exp partial homeomorphisms.
3. Prove: `cartanMap` is a homeomorphism from a small normal ball onto its (open) image, `cartanMap x₀ = p₀` (composition of the two local homeos + L; use the PartialHomeomorph API).
4. Report `harness/reports/M5-rigid-1_{done|blocked}.md`: signatures + the Jacobi-comparison roadmap (metric preservation via constant-curvature Jacobi fields — the sin-comparison both sides).

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanMap` and report the actual result. Commit your work.
