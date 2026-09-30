import Poincare.Global.DeTurckInverseEntryDerivativeDefinitions

noncomputable section
set_option autoImplicit false

namespace Poincare.DeTurckTensorBasis
open DeTurckPrincipalSecondJet
local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

def coordinate (a : Fin 3) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.coord a)

/-- All nine tensor components are retained, without off-diagonal conventions. -/
def tensor (a b : Fin 3) : Bilin := (coordinate a).smulRight (coordinate b)

/-- The first spatial jet uses all three direction slots and nine tensor slots. -/
def firstJet (p a b : Fin 3) : Jet1 := (coordinate p).smulRight (tensor a b)

end Poincare.DeTurckTensorBasis
