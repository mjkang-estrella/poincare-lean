import Poincare.Global.DeTurckChartLiftCoordinates
import Poincare.Global.DeTurckChartLiftSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckChartLift

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]

/-- The actual lift is a smooth bilinear bundle section on the preferred source. -/
theorem chartLift_contMDiffOn_source (anchor : M) (F : E → Bilin)
    (hF : ContDiff ℝ ∞ F) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (chartLift anchor F x))
      (extChartAt I anchor).source := by
  let e := trivializationAt E (TangentSpace I) anchor
  let eR := trivializationAt ℝ (fun _ : M => ℝ) anchor
  let eBil := e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) eR)
  have hbase : eBil.baseSet = (extChartAt I anchor).source := by
    simp [eBil, eR, e, TangentBundle.trivializationAt_baseSet]
  rw [← hbase, eBil.contMDiffOn_section_baseSet_iff]
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I anchor) eBil.baseSet := by
    simpa only [hbase, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := anchor))
  refine (hF.contMDiff.comp_contMDiffOn hchart).congr ?_
  intro x hx
  exact chartLift_coordinates anchor F x (hbase ▸ hx)

/-- Compact coefficient support allows the actual tangent tensor to extend
smoothly by zero across the preferred chart boundary. -/
theorem chartLift_contMDiff
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (anchor : M) (F : E → Bilin)
    (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F)
    (htarget : tsupport F ⊆ (extChartAt I anchor).target) :
    ContMDiff I (I.prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (chartLift anchor F x)) := by
  obtain ⟨hK, hsource, hzero, _⟩ := compact_source_support M anchor F hcompact htarget
  apply contMDiff_of_contMDiffOn_union_of_isOpen
    (chartLift_contMDiffOn_source anchor F hF)
    (t := (sourceSupport anchor F)ᶜ) ?_ ?_
    (isOpen_extChartAt_source anchor) hK.isClosed.isOpen_compl
  · apply ((Bundle.contMDiff_zeroSection ℝ
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)).contMDiffOn
        (s := (sourceSupport anchor F)ᶜ)).congr
    intro x hx
    simp only [hzero x hx, Bundle.zeroSection]
  · exact Set.compl_subset_iff_union.mp (Set.compl_subset_compl.mpr hsource)

end Poincare.DeTurckChartLift
