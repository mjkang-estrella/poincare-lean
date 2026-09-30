import Poincare.Global.DeTurckLocalizationDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100

namespace Poincare.DeTurckLocalization
open DeTurckPrincipalSecondJet DeTurckJetLinearization

local instance localizationProductBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance localizationProductJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance localizationProductJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance localizationProductJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance localizationProductJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- Identify the first product derivative everywhere before differentiating
that actual derivative field at the point of the second-jet certificate. -/
theorem cutoff_hasFDerivAt_two
    (χ : E → ℝ) (f : E → Bilin) (J : E → Jet1) (H : Jet2) (z : E)
    (hχ : ContDiff ℝ (2 : WithTop ENat) χ)
    (hf : ∀ y : E, HasFDerivAt f (J y) y) (hJ : HasFDerivAt J H z) :
    HasFDerivAt (fun y => χ y • f y)
      (cutoffFirst (χ z) (fderiv ℝ χ z) (f z) (J z)) z ∧
    HasFDerivAt (fun y => fderiv ℝ (fun x => χ x • f x) y)
      (cutoffSecond (χ z) (fderiv ℝ χ z) (fderiv ℝ (fderiv ℝ χ) z)
        (f z) (J z) H) z := by
  have hχderiv (y : E) : HasFDerivAt χ (fderiv ℝ χ y) y :=
    (hχ.differentiable (by norm_num) y).hasFDerivAt
  have hfirst (y : E) : HasFDerivAt (fun x => χ x • f x)
      (cutoffFirst (χ y) (fderiv ℝ χ y) (f y) (J y)) y := by
    simpa only [cutoffFirst] using (hχderiv y).smul (hf y)
  have hχfirst : ContDiff ℝ (1 : WithTop ENat) (fderiv ℝ χ) :=
    hχ.fderiv_right (by norm_num)
  have hχsecond : HasFDerivAt (fderiv ℝ χ)
      (fderiv ℝ (fderiv ℝ χ) z) z :=
    (hχfirst.differentiable (by norm_num) z).hasFDerivAt
  have hproductFirst : HasFDerivAt
      (fun y => cutoffFirst (χ y) (fderiv ℝ χ y) (f y) (J y))
      (cutoffSecond (χ z) (fderiv ℝ χ z) (fderiv ℝ (fderiv ℝ χ) z)
        (f z) (J z) H) z := by
    simpa only [cutoffFirst, cutoffSecond] using
      ((hχderiv z).smul hJ).add
        ((ContinuousLinearMap.smulRightL ℝ E Bilin).hasFDerivAt_of_bilinear
          hχsecond (hf z))
  have hnear : (fun y => fderiv ℝ (fun x => χ x • f x) y) =ᶠ[nhds z]
      (fun y => cutoffFirst (χ y) (fderiv ℝ χ y) (f y) (J y)) :=
    Filter.Eventually.of_forall (fun y => (hfirst y).fderiv)
  exact ⟨hfirst z, hproductFirst.congr_of_eventuallyEq hnear⟩

end Poincare.DeTurckLocalization
