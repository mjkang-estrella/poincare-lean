import Poincare.Global.DeTurckInverseEntryDerivativeDefinitions

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckJetLinearization
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

abbrev Jet2 := E →L[ℝ] Jet1
local instance : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
abbrev Variables := (Bilin × Jet1) × Jet2

/-- The actual two-index inverse-metric principal contraction. -/
def principal (G : Bilin) (H : Jet2) : Bilin :=
  ∑ i : Fin 3, ∑ j : Fin 3, inverseEntries G i j • H (basis3 i) (basis3 j)

/-- The genuine finite-jet expression, keeping the explicit full lower term. -/
def evolution (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (p : Variables) : Bilin :=
  principal p.1.1 p.2 + DeTurckPrincipalIdentity.lowerTerm B DB p.1.1 p.1.2

def metricProjection : Variables →L[ℝ] Bilin :=
  ContinuousLinearMap.fst ℝ Bilin Jet1 |>.comp
    (ContinuousLinearMap.fst ℝ (Bilin × Jet1) Jet2)

def secondJetEvaluation (i j : Fin 3) : Variables →L[ℝ] Bilin :=
  ((ContinuousLinearMap.apply ℝ Bilin (basis3 j)).comp
    (ContinuousLinearMap.apply ℝ Jet1 (basis3 i))).comp
      (ContinuousLinearMap.snd ℝ (Bilin × Jet1) Jet2)

/-- Actual lower differentiation; its derivative certificate is a proof obligation. -/
def lowerDifferential (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (G0 : Bilin) (J0 : Jet1) :
    (Bilin × Jet1) →L[ℝ] Bilin :=
  fderiv ℝ (fun p : Bilin × Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB p.1 p.2)
    (G0, J0)

/-- The full finite-jet differential includes the inverse variation against H0. -/
def differential (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (G0 : Bilin) (J0 : Jet1) (H0 : Jet2) : Variables →L[ℝ] Bilin :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    ((DeTurckInverseEntryDerivative.inverseEntryDerivative G0 i j).smulRight
      (H0 (basis3 i) (basis3 j))).comp metricProjection) +
  (∑ i : Fin 3, ∑ j : Fin 3, inverseEntries G0 i j • secondJetEvaluation i j) +
  (lowerDifferential B DB G0 J0).comp
    (ContinuousLinearMap.fst ℝ (Bilin × Jet1) Jet2)

end Poincare.DeTurckJetLinearization
