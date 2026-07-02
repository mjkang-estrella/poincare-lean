Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-12: the Gram-matrix route — trace derivative via extend-frame scalars

Read `harness/reports/M3-predicates-11_blocked.md`: raw constant tangent sections are NOT differentiable objects (varying preferred chart) — abandon them entirely. The differentiable frame is the CANONICAL EXTENSION frame, and the orchestrator-worked-out reformulation makes everything scalar:

**Master reformulation**: for y in a neighborhood of x, `{extend E (bᵢ) y}` is a basis of TM y (at y = x it IS the finBasis; invertibility of the Gram matrix is an open condition). By the basis-invariance lemma (predicates-3, on main):
`traceMetricVariationAt g h y = Σᵢⱼ (Gram g y)⁻¹ᵢⱼ · h y (extend E bᵢ y) (extend E bⱼ y)`
where `Gram g y : Matrix (Fin n) (Fin n) ℝ := fun i j => g.inner y (extend E bᵢ y) (extend E bⱼ y)`.

Deliverables (each its own commit):
1. `gramMatrix` def + `gramMatrix_at_base` (at y = x it's the finBasis metric matrix, invertible via nondegeneracy/pos-def) + differentiability of entries (`metric_pairing_extend_mdiffAt`, on main).
2. Invertibility on a neighborhood (`IsUnit (gramMatrix g y)` eventually near x — continuity of det via entry differentiability, `Matrix.isUnit_iff_isUnit_det`, `ContinuousAt.eventually_ne`-style) + differentiability of `y ↦ (gramMatrix g y)⁻¹` entries at x (Mathlib: `Matrix.inv` smoothness via `Matrix.inverse` = adjugate/det — `ContDiffAt.matrix_inv`-family or via `Ring.inverse` differentiability; entries are polynomial/det quotients of differentiable scalars).
3. **The trace identity**: `traceMetricVariationAt g h y = Σᵢⱼ (gramMatrix g y)⁻¹ᵢⱼ · h y (ext bᵢ y) (ext bⱼ y)` for y in the invertibility neighborhood — via the basis-invariance lemma applied to the extend basis + standard raised-dual-coframe-in-terms-of-Gram-inverse linear algebra.
4. **Differentiate**: the RHS is a finite sum of products of differentiable scalars (step 2 entries × the extend-form h entries — use the extend-form regularity hypothesis; `metric_pairing_extend_mdiffAt`'s statement shape shows the honest class; `VariationSpatiallyDifferentiableAt` may need an extend-form variant — add it honestly with witnesses). `extDerivFun` of the trace at x = the product-rule expansion. **This closes the differentiability half of `TraceMetricVariationDerivAt`.**
5. **Covariant form**: at y = x, extend sections have covTensor2DerivAt-compatible derivatives (that's their defining property — the deltaGammaAt machinery differentiates them constantly); identify the product-rule expansion with the contracted `covTensor2DerivAt` + the Gram-inverse derivative term, which the metric-compatibility lemmas on main (`spatialMetricDerivAt_eq_leviCivita` etc.) cancel. **Discharge `TraceMetricVariationDerivAt`.**
6. Cascade: hSummand/hFrame/ProductRule wrappers as they simplify; notes update.

Steps 1-4 are mechanical scalar calculus — push through all four minimum. Exact-goal-state rule on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
