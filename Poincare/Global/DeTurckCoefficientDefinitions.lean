import Poincare.Global.DeTurckJetLinearizationDefinitions

noncomputable section
set_option autoImplicit false

namespace Poincare.DeTurckCoefficients
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
abbrev Background := E →L[ℝ] E →L[ℝ] E
abbrev BackgroundDerivative := E →L[ℝ] Background
local instance : NormedAddCommGroup Background :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Background :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] E)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup BackgroundDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Background) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ BackgroundDerivative :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Background)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
abbrev BackgroundPair := Background × BackgroundDerivative
abbrev MetricJet := Bilin × Jet1
abbrev Joint := BackgroundPair × MetricJet
local instance : AddCommMonoid MetricJet := Prod.instAddCommMonoid

/-- The actual lower term with its background and metric jets varying jointly. -/
def jointLower (p : Joint) : Bilin :=
  DeTurckPrincipalIdentity.lowerTerm p.1.1 p.1.2 p.2.1 p.2.2

/-- Metric variations keep the background jets fixed. -/
def metricInclusion : MetricJet →L[ℝ] Joint :=
  ContinuousLinearMap.inr ℝ BackgroundPair MetricJet

/-- Partial derivative data already used by the actual finite-jet differential. -/
def partialLower (p : Joint) : MetricJet →L[ℝ] Bilin :=
  DeTurckJetLinearization.lowerDifferential p.1.1 p.1.2 p.2.1 p.2.2

end Poincare.DeTurckCoefficients
