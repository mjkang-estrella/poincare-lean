import Poincare.Global.DeTurckLocalizationDefinitions
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open scoped BigOperators
namespace Poincare.DeTurckJetRealization
open DeTurckPrincipalSecondJet DeTurckJetLinearization
local instance jetRealizationDefsBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance jetRealizationDefsJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance jetRealizationDefsJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance jetRealizationDefsJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance jetRealizationDefsJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- Full bilinear-valued quadratic Taylor polynomial with the original ordered jets. -/
def polynomial (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2) (y : E) : Bilin :=
  h0 + J0 (y - z) + (1 / 2 : ℝ) • H0 (y - z) (y - z)

/-- A constructed smooth cutoff localizes the actual two-jet of a C2 germ. -/
def realized (η : E → ℝ) (h : E → Bilin) (z y : E) : Bilin :=
  η y • polynomial z (h z) (fderiv ℝ h z)
    (fderiv ℝ (fderiv ℝ h) z) y
end Poincare.DeTurckJetRealization
