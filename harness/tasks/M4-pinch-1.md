Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-1: open the 3D pinching front — scalar-normalized Ricci pinching evolution (statement layer)

GOAL 5 opener: toward Hamilton 1982 (closed 3-manifold, positive Ricci ⟹ round). The engine: the evolution of the pinching quantity under the flow. On main: the Ricci evolution equation, the scalar evolution + R_min preservation, the pinching suite (`ricciNormSqAt`, `scalarAt_sq_le_nat_mul_ricciNormSqAt`, equality-iff-Einstein — RicciNorm.lean), the trace-variation machinery.

This is a STATEMENT + GROUNDWORK task (standing discipline — trace-validate and test-metric-pin everything before proof campaigns):

1. **The pinching quantity**: `def pinchingQuotientAt g x := ricciNormSqAt / scalarAt²` (or the traceless form `|Ric − (R/n)g|²/R²` — check the MODEL's Hamilton-pinching formulation in ModelLaplacian (`pinching_gap_*`, `tracelessNormSq`) and mirror the shape that made its algebra work). Definitional lemmas + positivity domain (R > 0).
2. **Time-derivative vocabulary**: `d/dt ricciNormSqAt` under the flow — from the PROVEN Ricci evolution + the metric-motion terms (|Ric|² involves g⁻¹ twice — the raise-derivative machinery gives the motion terms; state the honest decomposition lemma with the pieces from the merged toolkit).
3. **The target statement** (unproven Prop, test-metric-pinned): the evolution inequality for the pinching quantity (Hamilton's `d/dt(|Ric|²/R²) ≤ ...` shape in 3D, where the quadratic terms have a sign — 3D-specific: the Riemann tensor is determined by Ricci; state the 3D Rm-from-Ric decomposition as a def + its test-metric validation FIRST, since every 3D argument routes through it).
4. Roadmap notes (≤6 subtasks).

PIN ALL COEFFICIENTS with the space-form + non-Einstein diagonal patterns (standing lesson 3). No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
