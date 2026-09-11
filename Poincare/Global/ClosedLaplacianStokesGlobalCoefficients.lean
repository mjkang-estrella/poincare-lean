import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

end Poincare.ClosedLaplacianStokesGlobalCoefficients
