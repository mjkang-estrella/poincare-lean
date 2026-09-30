import Poincare.Global.DeTurckJetRealizationDefinitions
import Poincare.Global.BufferedFrozenParabolicSolver
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Set Filter
open scoped ContDiff Topology

namespace Poincare.DeTurckJetRealization
open DeTurckPrincipalSecondJet DeTurckJetLinearization

local instance compactJetRealizationBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
local instance compactJetRealizationJet1Group : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance compactJetRealizationJet1Space : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance compactJetRealizationJet2Group : NormedAddCommGroup Jet2 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1) (σ₁₂ := RingHom.id ℝ)
local instance compactJetRealizationJet2Space : NormedSpace ℝ Jet2 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Jet1)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- The full quadratic field is smooth in the original tensor operator norm. -/
theorem polynomial_contDiff (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2) :
    ContDiff ℝ ∞ (polynomial z h0 J0 H0) := by
  have hd : ContDiff ℝ ∞ (fun y : E => y - z) := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (J0.contDiff.comp hd)).add
    (((contDiff_const.clm_apply hd).clm_apply hd).const_smul (1 / 2 : ℝ))

/-- Multiplying the polynomial by a cutoff confines its whole tensor support. -/
theorem realized_tsupport_subset (η : E → ℝ) (h : E → Bilin) (z : E) :
    tsupport (realized η h z) ⊆ tsupport η :=
  tsupport_smul_subset_left η _

/-- Fiber symmetry of every Taylor coefficient makes the polynomial symmetric. -/
theorem polynomial_symmetric (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2)
    (hh : ∀ v w : E, h0 v w = h0 w v)
    (hJ : ∀ p v w : E, J0 p v w = J0 p w v)
    (hH : ∀ p q v w : E, H0 p q v w = H0 p q w v)
    (y v w : E) : polynomial z h0 J0 H0 y v w = polynomial z h0 J0 H0 y w v := by
  simp only [polynomial, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hh v w, hJ (y - z) v w, hH (y - z) (y - z) v w]

/-- At the center the Taylor polynomial has the supplied value. -/
theorem polynomial_center (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2) :
    polynomial z h0 J0 H0 z = h0 := by
  simp [polynomial]

/-- The smooth cutoff equals one on a neighborhood of the chosen center. -/
theorem exists_centered_cutoff (z : E) (U : Set E) (hU : IsOpen U) (hz : z ∈ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      ∀ᶠ y in 𝓝 z, η y = 1 := by
  obtain ⟨η, hη, hcη, hηU, hone, _⟩ :=
    BufferedFrozenParabolicSolver.exists_buffered_cutoff (isCompact_singleton (x := z)) hU
      (singleton_subset_iff.mpr hz)
  exact ⟨η, hη, hcη, hηU, hone z (mem_singleton z)⟩

abbrev realizationTensorFlip : Bilin ≃L[ℝ] Bilin :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv
abbrev realizationJetFlip : Jet1 ≃L[ℝ] Jet1 :=
  (ContinuousLinearEquiv.refl ℝ E).arrowCongr realizationTensorFlip

/-- The first derivative retains the simultaneous tensor-slot symmetry germ. -/
theorem germ_first_fiber_symmetric (h : E → Bilin) (z : E)
    (hs : ∀ᶠ y in 𝓝 z, ∀ v w : E, h y v w = h y w v) :
    ∀ p v w : E, fderiv ℝ h z p v w = fderiv ℝ h z p w v := by
  have heq : h =ᶠ[𝓝 z] (realizationTensorFlip ∘ h) := by
    filter_upwards [hs] with y hy
    ext v w
    exact hy v w
  have hd : fderiv ℝ h z =
      (realizationTensorFlip : Bilin →L[ℝ] Bilin).comp (fderiv ℝ h z) :=
    heq.fderiv_eq.trans realizationTensorFlip.comp_fderiv
  intro p v w
  exact congrArg (fun J : Jet1 => J p v w) hd

/-- The second derivative retains tensor symmetry in every ordered direction slot. -/
theorem germ_second_fiber_symmetric (h : E → Bilin) (z : E)
    (hs : ∀ᶠ y in 𝓝 z, ∀ v w : E, h y v w = h y w v) :
    ∀ p q v w : E, fderiv ℝ (fderiv ℝ h) z p q v w =
      fderiv ℝ (fderiv ℝ h) z p q w v := by
  have heq : h =ᶠ[𝓝 z] (realizationTensorFlip ∘ h) := by
    filter_upwards [hs] with y hy
    ext v w
    exact hy v w
  have heq1 : fderiv ℝ h =ᶠ[𝓝 z] (realizationJetFlip ∘ fderiv ℝ h) := by
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
    exact hy.trans realizationTensorFlip.comp_fderiv
  have hd : fderiv ℝ (fderiv ℝ h) z =
      (realizationJetFlip : Jet1 →L[ℝ] Jet1).comp (fderiv ℝ (fderiv ℝ h) z) :=
    heq1.fderiv_eq.trans realizationJetFlip.comp_fderiv
  intro p q v w
  exact congrArg (fun H : Jet2 => H p q v w) hd

/-- Derivative of the full ordered quadratic polynomial at every point. -/
theorem polynomial_hasFDerivAt (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2) (y : E) :
    HasFDerivAt (polynomial z h0 J0 H0)
      (J0 + (1 / 2 : ℝ) • (H0 (y-z) + H0.flip (y-z))) y := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const z
  have hJ := J0.hasFDerivAt.comp y hd
  have hH := (H0.hasFDerivAt.comp y hd).clm_apply hd
  simpa only [ContinuousLinearMap.comp_id] using
    (hJ.const_add h0).add (hH.const_smul (1 / 2 : ℝ))

/-- The polynomial recovers the full first jet at its center. -/
theorem polynomial_first (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2) :
    fderiv ℝ (polynomial z h0 J0 H0) z = J0 := by
  simpa using (polynomial_hasFDerivAt z h0 J0 H0 z).fderiv

/-- Direction symmetry makes the ordered second derivative exactly the supplied jet. -/
theorem polynomial_second (z : E) (h0 : Bilin) (J0 : Jet1) (H0 : Jet2)
    (hH : ∀ v w : E, H0 v w = H0 w v) :
    fderiv ℝ (fderiv ℝ (polynomial z h0 J0 H0)) z = H0 := by
  have hflip : H0.flip = H0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact hH w v
  have hderiv : fderiv ℝ (polynomial z h0 J0 H0) = fun y => J0 + H0 (y-z) := by
    funext y
    rw [(polynomial_hasFDerivAt z h0 J0 H0 y).fderiv, hflip]
    rw [← two_smul ℝ (H0 (y-z)), smul_smul]
    norm_num
  rw [hderiv]
  have hd := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const z
  simpa using ((H0.hasFDerivAt.comp z hd).const_add J0).fderiv

/-- A symmetric C2 germ has an explicit compact smooth realization of its full two-jet. -/
theorem exists_compact_symmetric_realization (h : E → Bilin) (z : E) (U : Set E)
    (hU : IsOpen U) (hz : z ∈ U) (hc : ContDiffAt ℝ (2 : WithTop ENat) h z)
    (hs : ∀ᶠ y in 𝓝 z, ∀ v w : E, h y v w = h y w v) :
    ∃ η : E → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ᶠ y in 𝓝 z, η y = 1) ∧
      ContDiff ℝ ∞ (realized η h z) ∧ HasCompactSupport (realized η h z) ∧
      tsupport (realized η h z) ⊆ U ∧
      (∀ y v w : E, realized η h z y v w = realized η h z y w v) ∧
      realized η h z z = h z ∧
      fderiv ℝ (realized η h z) z = fderiv ℝ h z ∧
      fderiv ℝ (fderiv ℝ (realized η h z)) z = fderiv ℝ (fderiv ℝ h) z := by
  obtain ⟨η, hη, hcη, hηU, hone⟩ := exists_centered_cutoff z U hU hz
  have heq : realized η h z =ᶠ[𝓝 z]
      polynomial z (h z) (fderiv ℝ h z) (fderiv ℝ (fderiv ℝ h) z) := by
    filter_upwards [hone] with y hy
    simp only [realized, hy, one_smul]
  refine ⟨η, hη, hcη, hηU, hone,
    hη.smul (polynomial_contDiff z (h z) (fderiv ℝ h z)
      (fderiv ℝ (fderiv ℝ h) z)), hcη.smul_right,
    (realized_tsupport_subset η h z).trans hηU, ?_, ?_, ?_, ?_⟩
  · intro y v w
    simp only [realized, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [polynomial_symmetric z (h z) (fderiv ℝ h z) (fderiv ℝ (fderiv ℝ h) z)
      hs.self_of_nhds (germ_first_fiber_symmetric h z hs)
      (germ_second_fiber_symmetric h z hs) y v w]
  · exact heq.self_of_nhds.trans (polynomial_center z (h z) (fderiv ℝ h z)
      (fderiv ℝ (fderiv ℝ h) z))
  · exact heq.fderiv_eq.trans (polynomial_first z (h z) (fderiv ℝ h z)
      (fderiv ℝ (fderiv ℝ h) z))
  · exact (heq.fderiv (𝕜 := ℝ)).fderiv_eq.trans
      (polynomial_second z (h z) (fderiv ℝ h z) (fderiv ℝ (fderiv ℝ h) z)
        (hc.isSymmSndFDerivAt (by simp)))

end Poincare.DeTurckJetRealization
