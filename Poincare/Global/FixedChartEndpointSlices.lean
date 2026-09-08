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

/-- Restriction to an anchor, retaining the exact vertical source and target. -/
def slice (z : E) : OpenPartialHomeomorph E E where
  toFun v := (P (z, v)).2
  invFun y := (P.symm (z, y)).2
  source := {v | (z, v) ∈ P.source}
  target := {y | (z, y) ∈ P.target}
  map_source' := by
    intro v hv
    have heq : (z, (P (z, v)).2) = P (z, v) :=
      Prod.ext (hfst (z, v) hv).symm rfl
    change (z, (P (z, v)).2) ∈ P.target
    rw [heq]
    exact P.map_source hv
  map_target' := by
    intro y hy
    have heq : (z, (P.symm (z, y)).2) = P.symm (z, y) :=
      Prod.ext (symm_fst P hfst hy).symm rfl
    change (z, (P.symm (z, y)).2) ∈ P.source
    rw [heq]
    exact P.map_target hy
  left_inv' := by
    intro v hv
    have heq : (z, (P (z, v)).2) = P (z, v) :=
      Prod.ext (hfst (z, v) hv).symm rfl
    change (P.symm (z, (P (z, v)).2)).2 = v
    rw [heq, P.left_inv hv]
  right_inv' := by
    intro y hy
    have heq : (z, (P.symm (z, y)).2) = P.symm (z, y) :=
      Prod.ext (symm_fst P hfst hy).symm rfl
    change (P (z, (P.symm (z, y)).2)).2 = y
    rw [heq, P.right_inv hy]
  open_source := P.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := P.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun :=
    (P.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => hv)).snd
  continuousOn_invFun :=
    (P.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => hy)).snd

/-- The stationary product zero section gives the slice's anchor value. -/
theorem slice_zero [Zero E] {A : Set E}
    (hstationary : ∀ z ∈ A, P (z, 0) = (z, z)) :
    ∀ z ∈ A, slice P hfst z 0 = z := by
  intro z hz
  exact congrArg Prod.snd (hstationary z hz)

/-- The supplied zero section lies in the exact slice source. -/
theorem slice_zero_mem_source [Zero E] {A : Set E}
    (hzero : ∀ z ∈ A, (z, (0 : E)) ∈ P.source) :
    ∀ z ∈ A, 0 ∈ (slice P hfst z).source := by
  exact hzero

/-- The joint source over an open anchor set is open. -/
theorem isOpen_slice_sourceLocus {A : Set E} (hA : IsOpen A) :
    IsOpen {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).source} := by
  change IsOpen (Prod.fst ⁻¹' A ∩ P.source)
  exact (hA.preimage continuous_fst).inter P.open_source

/-- The joint target over an open anchor set is open. -/
theorem isOpen_slice_targetLocus {A : Set E} (hA : IsOpen A) :
    IsOpen {q : E × E | q.1 ∈ A ∧ q.2 ∈ (slice P hfst q.1).target} := by
  change IsOpen (Prod.fst ⁻¹' A ∩ P.target)
  exact (hA.preimage continuous_fst).inter P.open_target

end Poincare.FixedChartEndpointSlices
