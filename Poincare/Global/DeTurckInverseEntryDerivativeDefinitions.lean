import Poincare.Global.DeTurckPrincipalIdentity

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckInverseEntryDerivative
open DeTurckPrincipalSecondJet

/-- Actual metric-coordinate evaluation as a bounded real linear map. -/
def entryCLM (k l : Fin 3) : Bilin →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (basis3 l)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (basis3 k))

/-- The inverse-metric variation coefficient, retaining both inverse factors. -/
def inverseEntryDerivative (G0 : Bilin) (i j : Fin 3) : Bilin →L[ℝ] ℝ :=
  -(∑ k : Fin 3, ∑ l : Fin 3,
    (inverseEntries G0 i k * inverseEntries G0 l j) • entryCLM k l)

end Poincare.DeTurckInverseEntryDerivative
