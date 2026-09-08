import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Exact slices of an anchor-preserving product chart

A product partial homeomorphism preserving the first coordinate on its source
restricts to a partial homeomorphism at each anchor. Its inverse preserves the
first coordinate on the target as a consequence of the inverse law.
-/

namespace Poincare.FixedChartEndpointSlices

open Set

variable {E : Type*} [TopologicalSpace E]
variable (P : OpenPartialHomeomorph (E × E) (E × E))
variable (hfst : ∀ q ∈ P.source, (P q).1 = q.1)

include hfst in
/-- The inverse preserves anchors on the exact product target. -/
theorem symm_fst {q : E × E} (hq : q ∈ P.target) :
    (P.symm q).1 = q.1 := by
  have h := hfst (P.symm q) (P.map_target hq)
  rw [P.right_inv hq] at h
  exact h.symm

end Poincare.FixedChartEndpointSlices
