import Poincare.Global.DeTurckCoefficientDefinitions
import Poincare.Global.DeTurckLowerJointSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open scoped ContDiff

namespace Poincare.DeTurckPartialDerivativeBridge
open DeTurckPrincipalSecondJet DeTurckCoefficients

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
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
local instance : NormedAddCommGroup MetricJet := Prod.normedAddCommGroup
local instance : NormedSpace ℝ MetricJet := Prod.normedSpace
local instance : NormedAddCommGroup BackgroundPair := Prod.normedAddCommGroup
local instance : NormedSpace ℝ BackgroundPair := Prod.normedSpace
local instance : NormedAddCommGroup Joint := Prod.normedAddCommGroup
local instance : NormedSpace ℝ Joint := Prod.normedSpace
local instance : AddCommGroup MetricJet := Prod.instAddCommGroup
local instance : AddCommGroup BackgroundPair := Prod.instAddCommGroup
local instance : AddCommGroup Joint := Prod.instAddCommGroup
local instance : AddCommMonoid MetricJet := Prod.instAddCommMonoid
local instance : AddCommMonoid BackgroundPair := Prod.instAddCommMonoid
local instance : AddCommMonoid Joint := Prod.instAddCommMonoid


/-- The actual metric-jet derivative is the joint derivative restricted to
metric directions, with both background directions fixed. -/
theorem partialLower_eq_joint_derivative :
letI : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
letI : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
letI : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid;
∀ (B : Poincare.DeTurckCoefficients.Background) (DB : Poincare.DeTurckCoefficients.BackgroundDerivative) (G0 : Poincare.DeTurckPrincipalSecondJet.Bilin) (J0 : Poincare.DeTurckPrincipalSecondJet.Jet1),
G0.IsInvertible → Poincare.DeTurckCoefficients.partialLower ((B,DB),(G0,J0)) =
 (fderiv ℝ Poincare.DeTurckCoefficients.jointLower ((B,DB),(G0,J0))).comp Poincare.DeTurckCoefficients.metricInclusion := by
  intro B DB G0 J0 hG
  have hjoint : HasFDerivAt jointLower
      (fderiv ℝ jointLower ((B, DB), (G0, J0))) ((B, DB), (G0, J0)) :=
    ((DeTurckLowerJointSmoothness.contDiffAt_lowerTerm_joint B DB G0 J0 hG).differentiableAt
      (by simp)).hasFDerivAt
  have hpartial := hjoint.comp (G0, J0)
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (B, DB) (G0, J0))
  simpa only [partialLower, DeTurckJetLinearization.lowerDifferential,
    jointLower, metricInclusion, Function.comp_def] using hpartial.fderiv

end Poincare.DeTurckPartialDerivativeBridge
