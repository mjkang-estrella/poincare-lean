import Poincare.Global.DeTurckSpatialCoefficientDefinitions
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open scoped BigOperators
namespace Poincare.DeTurckLocalization
open DeTurckPrincipalSecondJet DeTurckJetLinearization
local instance localizationDefsBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance localizationDefsJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance localizationDefsJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance localizationDefsJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance localizationDefsJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- Actual first product jet, including the scalar cutoff gradient. -/
def cutoffFirst (c : ℝ) (dc : E →L[ℝ] ℝ) (h : Bilin) (J : Jet1) : Jet1 :=
  c • J + dc.smulRight h

/-- Both ordered mixed terms and the actual cutoff Hessian contribution. -/
def cutoffSecond (c : ℝ) (dc : E →L[ℝ] ℝ) (ddc : Bilin)
    (h : Bilin) (J : Jet1) (H : Jet2) : Jet2 :=
  (c • H + dc.smulRight J) +
    ((ContinuousLinearMap.smulRightL ℝ E Bilin).precompR E dc J +
     (ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E ddc h)

def cutoffVariables (c : ℝ) (dc : E →L[ℝ] ℝ) (ddc : Bilin)
    (p : Variables) : Variables :=
  ((c • p.1.1, cutoffFirst c dc p.1.1 p.1.2),
    cutoffSecond c dc ddc p.1.1 p.1.2 p.2)

end Poincare.DeTurckLocalization
