import Poincare.Global.DeTurckPartialDerivativeBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open scoped ContDiff Topology
open Filter Set

namespace Poincare.DeTurckPartialCoefficientSmoothness
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


local instance : NormedAddCommGroup (MetricJet →L[ℝ] Bilin) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := MetricJet) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (MetricJet →L[ℝ] Bilin) :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := MetricJet) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- Smoothness of the actual metric-jet partial differential while all
basepoint jets vary. This supplies the real spatial lower-order coefficients. -/
theorem contDiffAt_partialLower :
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
letI : NormedAddCommGroup (Poincare.DeTurckCoefficients.MetricJet →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckCoefficients.MetricJet) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ (Poincare.DeTurckCoefficients.MetricJet →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckCoefficients.MetricJet) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
∀ (B : Poincare.DeTurckCoefficients.Background) (DB : Poincare.DeTurckCoefficients.BackgroundDerivative) (G0 : Poincare.DeTurckPrincipalSecondJet.Bilin) (J0 : Poincare.DeTurckPrincipalSecondJet.Jet1),
G0.IsInvertible → ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
 Poincare.DeTurckCoefficients.partialLower ((B,DB),(G0,J0)) := by
  intro B DB G0 J0 hInv
  let p0 : Joint := ((B, DB), (G0, J0))
  have hjoint : ContDiffAt ℝ ∞ jointLower p0 :=
    DeTurckLowerJointSmoothness.contDiffAt_lowerTerm_joint B DB G0 J0 hInv
  have hrestricted : ContDiffAt ℝ ∞
      (fun p : Joint => (fderiv ℝ jointLower p).comp metricInclusion) p0 :=
    (hjoint.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const
  have hmetric : ContinuousAt (fun p : Joint => p.2.1) p0 :=
    continuous_fst.continuousAt.comp continuous_snd.continuousAt
  rcases hInv with ⟨e, he⟩
  have hnear : ∀ᶠ p : Joint in 𝓝 p0, p.2.1.IsInvertible := by
    have h := hmetric.preimage_mem_nhds (by simpa only [he] using e.nhds)
    filter_upwards [h] with p hp
    exact hp
  apply hrestricted.congr_of_eventuallyEq
  filter_upwards [hnear] with p hp
  exact DeTurckPartialDerivativeBridge.partialLower_eq_joint_derivative
    p.1.1 p.1.2 p.2.1 p.2.2 hp

end Poincare.DeTurckPartialCoefficientSmoothness
