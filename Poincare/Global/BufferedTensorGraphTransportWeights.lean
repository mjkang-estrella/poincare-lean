import Poincare.Global.BufferedTensorGraphTransportDefinitions
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Poincare.BufferedTensorGraphTransport
open FiniteAtlasParabolicTensorSpace
universe u

/-- The actual destination tensor coefficient is smooth and compactly supported.
The inverse chart is only used on its genuine target, where the gate is supported. -/
theorem contDiff_hasCompactSupport_weight
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (i : Fin A.cover.chartCount)
    (θ ξ : ClosedSmoothModel 3 → ℝ)
    (F : ClosedSmoothModel 3 → ClosedSmoothModel 3) (a b c d : Fin 3)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ)
    (hθtarget : tsupport θ ⊆ (chart A i).target)
    (hξ : ContDiff ℝ ∞ ξ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (weight A i θ ξ F a b c d) ∧
      HasCompactSupport (weight A i θ ξ F a b c d) := by
  have hpartition : ContDiffOn ℝ ∞
      (fun z ↦ (A.partition i) ((chart A i).symm z)) (chart A i).target := by
    exact ((A.partition i).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (I := closedSmoothModelWithCorners 3)
        (n := ∞) (A.cover.anchor i))).contDiffOn
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hentry (r s : Fin 3) : ContDiff ℝ ∞
      (fun z ↦ (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) s)) r) :=
    (EuclideanSpace.proj r).contDiff.comp
      (hDF.clm_apply (contDiff_const (c := EuclideanSpace.basisFun (Fin 3) ℝ s)))
  refine ⟨?_, ?_⟩
  · exact ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul
      (isOpen_extChartAt_target (A.cover.anchor i)) hθ hθtarget
      (((hpartition.mul (hξ.comp hF).contDiffOn).mul
        (hentry a c).contDiffOn).mul (hentry b d).contDiffOn)
  · exact hcθ.mul_right

end Poincare.BufferedTensorGraphTransport
