import Poincare.Global.DeTurckCoefficientDefinitions

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckSpatialCoefficients
open DeTurckPrincipalSecondJet
open DeTurckJetLinearization

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : AddCommMonoid (Bilin × Jet1) := Prod.instAddCommMonoid

/-- The actual zero-order coefficient includes inverse variation against H0. -/
def zeroOrder (B : DeTurckCoefficients.Background)
    (DB : DeTurckCoefficients.BackgroundDerivative)
    (G0 : Bilin) (J0 : Jet1) (H0 : Jet2) : Bilin →L[ℝ] Bilin :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    (DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j).smulRight
      (H0 (basis3 i) (basis3 j))) +
  (lowerDifferential B DB G0 J0).comp (ContinuousLinearMap.inl ℝ Bilin Jet1)

/-- The actual first-order coefficient differentiates lowerTerm in the first jet. -/
def firstOrder (B : DeTurckCoefficients.Background)
    (DB : DeTurckCoefficients.BackgroundDerivative)
    (G0 : Bilin) (J0 : Jet1) : Jet1 →L[ℝ] Bilin :=
  (lowerDifferential B DB G0 J0).comp (ContinuousLinearMap.inr ℝ Bilin Jet1)

end Poincare.DeTurckSpatialCoefficients
