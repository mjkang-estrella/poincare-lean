import Poincare.Global.DeTurckLocalizationDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open scoped BigOperators

namespace Poincare.DeTurckLocalization
open DeTurckPrincipalSecondJet DeTurckJetLinearization

local instance localizationProofBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance localizationProofJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance localizationProofJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance localizationProofJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance localizationProofJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The full differential localizes with both ordered principal mixed terms,
the cutoff Hessian, and the actual lower first-order correction. -/
theorem differential_cutoff :
letI : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 := ContinuousLinearMap.toNormedAddCommGroup
  (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 := ContinuousLinearMap.toNormedSpace
  (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
letI : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
  (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ);
letI : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
  (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ);
∀ (B : Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)
(DB : Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)
(G0 : Poincare.DeTurckPrincipalSecondJet.Bilin) (J0 : Poincare.DeTurckPrincipalSecondJet.Jet1) (H0 : Poincare.DeTurckJetLinearization.Jet2)
(c : ℝ) (dc : Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] ℝ) (ddc : Poincare.DeTurckPrincipalSecondJet.Bilin) (p : Poincare.DeTurckJetLinearization.Variables),
Poincare.DeTurckJetLinearization.differential B DB G0 J0 H0 (Poincare.DeTurckLocalization.cutoffVariables c dc ddc p) =
c • Poincare.DeTurckJetLinearization.differential B DB G0 J0 H0 p +
(∑ i : Fin 3, ∑ j : Fin 3, Poincare.DeTurckPrincipalSecondJet.inverseEntries G0 i j •
 (dc (Poincare.DeTurckPrincipalSecondJet.basis3 i) • p.1.2 (Poincare.DeTurckPrincipalSecondJet.basis3 j) + dc (Poincare.DeTurckPrincipalSecondJet.basis3 j) • p.1.2 (Poincare.DeTurckPrincipalSecondJet.basis3 i) + ddc (Poincare.DeTurckPrincipalSecondJet.basis3 i) (Poincare.DeTurckPrincipalSecondJet.basis3 j) • p.1.1)) +
Poincare.DeTurckSpatialCoefficients.firstOrder B DB G0 J0 (dc.smulRight p.1.1) := by
  intro B DB G0 J0 H0 c dc ddc p
  let r : Jet2 := dc.smulRight p.1.2 +
    ((ContinuousLinearMap.smulRightL ℝ E Bilin).precompR E dc p.1.2 +
      (ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E ddc p.1.1)
  let q : Variables := ((0, dc.smulRight p.1.1), r)
  have hcut : cutoffVariables c dc ddc p = c • p + q := by
    apply Prod.ext
    · apply Prod.ext
      · change c • p.1.1 = c • p.1.1 + 0
        exact (add_zero _).symm
      · rfl
    · change (c • p.2 + dc.smulRight p.1.2) +
          ((ContinuousLinearMap.smulRightL ℝ E Bilin).precompR E dc p.1.2 +
            (ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E ddc p.1.1) =
        c • p.2 + (dc.smulRight p.1.2 +
          ((ContinuousLinearMap.smulRightL ℝ E Bilin).precompR E dc p.1.2 +
            (ContinuousLinearMap.smulRightL ℝ E Bilin).precompL E ddc p.1.1))
      exact add_assoc _ _ _
  have hq : differential B DB G0 J0 H0 q =
      (∑ i : Fin 3, ∑ j : Fin 3, inverseEntries G0 i j •
        (dc (basis3 i) • p.1.2 (basis3 j) +
          dc (basis3 j) • p.1.2 (basis3 i) +
          ddc (basis3 i) (basis3 j) • p.1.1)) +
      DeTurckSpatialCoefficients.firstOrder B DB G0 J0 (dc.smulRight p.1.1) := by
    simp [differential, q, r, metricProjection, secondJetEvaluation,
      DeTurckSpatialCoefficients.firstOrder, add_assoc]
  rw [hcut, map_add, map_smul, hq]
  exact (add_assoc _ _ _).symm

end Poincare.DeTurckLocalization
