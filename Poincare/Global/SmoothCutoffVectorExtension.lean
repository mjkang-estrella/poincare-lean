import Poincare.Global.RiemannianContext
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# Smooth compact extension of a local vector map

A compactly supported smooth scalar cutoff contained in an open domain
extends a vector map smooth on that domain. The product is locally zero
outside the domain, regardless of the original map's off-domain values.
This supplies the actual gated chart maps for bounded tensor transport
toward Hamilton flow input existence.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.SmoothCutoffVectorExtension

/-- A local smooth vector map becomes globally smooth and compactly supported
after multiplication by a smooth compact cutoff inside its domain. -/
theorem contDiff_hasCompactSupport_cutoff_smul
    (U : Set (ClosedSmoothModel 3)) (hU : IsOpen U)
    (f : ClosedSmoothModel 3 → ClosedSmoothModel 3) (hf : ContDiffOn ℝ ∞ f U)
    (η : ClosedSmoothModel 3 → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ContDiff ℝ ∞ (fun z ↦ η z • f z) ∧
      HasCompactSupport (fun z ↦ η z • f z) := by
  refine ⟨?_, hcη.smul_right⟩
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hη.contDiffAt.smul ((hf z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hηU h))
    apply (contDiffAt_const (c := (0 : ClosedSmoothModel 3))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]

end Poincare.SmoothCutoffVectorExtension
