import Poincare.Global.RiemannianContext
import Poincare.Global.ParabolicSolutionGraph
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff Topology

namespace Poincare.ParabolicSpatialPullbackChainRule

/-- Pulling back the spatial covector differentiates both the graph jet and the chart Jacobian. -/
theorem hasFDerivAt_graph_covector_pullback
    (F : ClosedSmoothModel 3 → ClosedSmoothModel 3) (hF : ContDiff ℝ ∞ F)
    (α T : ℝ) (G : ParabolicSolutionGraph.Graph (E := ClosedSmoothModel 3) α T)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : ClosedSmoothModel 3) :
    HasFDerivAt (fun z ↦ (G.du (t, F z)).comp (fderiv ℝ F z))
      (((ContinuousLinearMap.compL ℝ (ClosedSmoothModel 3) (ClosedSmoothModel 3) ℝ).flip
        (fderiv ℝ F x)).comp ((G.ddu (t, F x)).comp (fderiv ℝ F x)) +
       ((ContinuousLinearMap.compL ℝ (ClosedSmoothModel 3) (ClosedSmoothModel 3) ℝ)
         (G.du (t, F x))).comp (fderiv ℝ (fderiv ℝ F) x)) x := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hFx := (hF.differentiable (by simp) x).hasFDerivAt
  have hcovector := (G.hasFDeriv_du t ht (F x)).comp x hFx
  have hJacobian := (hDF.differentiable (by simp) x).hasFDerivAt
  simpa only [Function.comp_def, add_comm] using hcovector.clm_comp hJacobian

end Poincare.ParabolicSpatialPullbackChainRule
