import Poincare.Global.DeTurckPrincipalIdentity
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.DeTurckInverseEntrySmoothness
open DeTurckPrincipalSecondJet

/-- Actual inverse-metric coefficients are smooth at every invertible metric jet.
The coordinate identity holds on the open set of invertible operators, so
smoothness of operator inversion gives spatial coefficient regularity. -/
theorem contDiffAt_inverseEntry (G0 : Bilin) (i j : Fin 3)
    (hG0 : G0.IsInvertible) :
    ContDiffAt ℝ ∞ (fun G : Bilin => inverseEntries G i j) G0 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let q : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let c : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord j)
  have hs : ContDiffAt ℝ ∞ (fun G : Bilin => c (G.inverse q)) G0 :=
    c.contDiff.contDiffAt.comp G0
      (hG0.contDiffAt_map_inverse.clm_apply contDiffAt_const)
  have hinv : ∀ᶠ G : Bilin in nhds G0, G.IsInvertible := by
    rcases hG0 with ⟨e, he⟩
    rw [← he]
    filter_upwards [ContinuousLinearEquiv.nhds e] with G hG
    rcases hG with ⟨d, hd⟩
    exact ⟨d, hd⟩
  apply hs.congr_of_eventuallyEq
  filter_upwards [hinv] with G hG
  rw [DeTurckPrincipalIdentity.inverseEntries_eq_coordinates G hG]
  rfl

end Poincare.DeTurckInverseEntrySmoothness
