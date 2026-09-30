import Poincare.Global.DeTurckTensorGraphJet
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open scoped BigOperators
namespace Poincare.DeTurckTensorSecondJet
open DeTurckPrincipalSecondJet DeTurckJetLinearization
local instance tensorSecondDefsBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance tensorSecondDefsJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance tensorSecondDefsJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance tensorSecondDefsJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance tensorSecondDefsJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The whole tensor second jet comes from the genuine scalar Graph Hessians. -/
def tensorHessian {α T : ℝ} (W : DeTurckCoupledForcing.Inputs α T)
    (q : ℝ × E) : Jet2 :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E
      ((W (a,b)).ddu q) (DeTurckTensorBasis.tensor a b)
end Poincare.DeTurckTensorSecondJet
