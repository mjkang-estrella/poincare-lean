import Poincare.Global.DeTurckTensorSecondJetDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open scoped BigOperators

namespace Poincare.DeTurckTensorSecondJet
open DeTurckPrincipalSecondJet DeTurckJetLinearization

local instance tensorSecondJetBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance tensorSecondJetJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance tensorSecondJetJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance tensorSecondJetJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance tensorSecondJetJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The reconstructed second jet differentiates the same tensor first jet. -/
theorem tensorHessian_hasFDerivAt : ∀ (α T : ℝ)
    (W : DeTurckCoupledForcing.Inputs α T) (t : ℝ) (z : E),
    t ∈ Set.Icc 0 T →
    HasFDerivAt (fun y => DeTurckCoupledForcing.tensorJet W (t,y))
      (tensorHessian W (t,z)) z := by
  intro α T W t z ht
  unfold DeTurckCoupledForcing.tensorJet tensorHessian
  exact HasFDerivAt.fun_sum (fun a _ => HasFDerivAt.fun_sum (fun b _ =>
    (((ContinuousLinearMap.smulRightL ℝ E Bilin).flip
      (DeTurckTensorBasis.tensor a b)).hasFDerivAt.comp z
        ((W (a,b)).hasFDeriv_du t ht z))))

/-- Positive Hölder exponent gives continuity of each original fixed-time carrier. -/
private theorem holder_slice_continuous {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α T t : ℝ}
    (f : ParabolicHolder.Y (E := E) α T F) (hα : 0 < α)
    (ht : t ∈ Set.Icc 0 T) : Continuous (fun y : E => f (t,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound (y : E) :
      ‖f (t,y) - f (t,x)‖ ≤ ‖f‖ * ‖y - x‖ ^ α := by
    simpa only [ParabolicHolder.parabolicDist, sub_self, abs_zero,
      Real.sqrt_zero, add_zero] using
      ParabolicHolder.holder_le f
        (show (t,y) ∈ ParabolicHolder.cylinder T from ⟨ht, Set.mem_univ y⟩)
        (show (t,x) ∈ ParabolicHolder.cylinder T from ⟨ht, Set.mem_univ x⟩)
  apply squeeze_zero (fun y => norm_nonneg _) hbound
  have hc : Continuous (fun y : E => ‖f‖ * ‖y - x‖ ^ α) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
      (fun _ => Or.inr hα.le))
  simpa only [sub_self, norm_zero, Real.zero_rpow (ne_of_gt hα), mul_zero]
    using hc.tendsto x

/-- The genuine second jet is continuous on every spatial slice of the cylinder. -/
private theorem tensorHessian_continuous {α T : ℝ}
    (W : DeTurckCoupledForcing.Inputs α T) (t : ℝ)
    (hα : 0 < α) (ht : t ∈ Set.Icc 0 T) :
    Continuous (fun y : E => tensorHessian W (t,y)) := by
  unfold tensorHessian
  exact continuous_finsetSum _ (fun a _ => continuous_finsetSum _ (fun b _ =>
    ((((ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E).flip
      (DeTurckTensorBasis.tensor a b)).continuous.comp
        (holder_slice_continuous (W (a,b)).ddu hα ht))))

/-- Each fixed-time tensor value is globally spatially C² for positive exponent. -/
theorem tensorValue_contDiff_two : ∀ (α T : ℝ)
    (W : DeTurckCoupledForcing.Inputs α T) (t : ℝ),
    0 < α → t ∈ Set.Icc 0 T →
    ContDiff ℝ (2 : WithTop ENat)
      (fun y : E => DeTurckCoupledForcing.tensorValue W (t,y)) := by
  intro α T W t hα ht
  have hjet : ContDiff ℝ 1 (fun y : E => DeTurckCoupledForcing.tensorJet W (t,y)) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨_, tensorHessian_continuous W t hα ht,
      fun z => tensorHessian_hasFDerivAt α T W t z ht⟩
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr ⟨_, hjet,
    fun z => DeTurckCoupledForcing.tensorJet_hasFDerivAt α T W t z ht⟩

end Poincare.DeTurckTensorSecondJet
