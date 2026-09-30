import Poincare.Global.DeTurckCoupledForcingDefinitions

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckCoupledForcing
open DeTurckPrincipalSecondJet

local instance : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The reconstructed tensor jet is the spatial derivative of the same Graph values. -/
theorem tensorJet_hasFDerivAt : ∀ (α T : ℝ) (W : Inputs α T) (t : ℝ)
    (z : E), t ∈ Set.Icc 0 T →
    HasFDerivAt (fun y : E => tensorValue W (t,y)) (tensorJet W (t,z)) z := by
  intro α T W t z ht
  unfold tensorValue tensorJet
  exact HasFDerivAt.fun_sum (fun a _ => HasFDerivAt.fun_sum (fun b _ =>
    ((W (a,b)).hasFDeriv t ht z).smul_const (DeTurckTensorBasis.tensor a b)))

end Poincare.DeTurckCoupledForcing
