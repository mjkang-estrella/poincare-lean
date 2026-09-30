import Poincare.Global.ParabolicSpatialHolderPullback
import Poincare.Global.ParabolicSpatialPullbackChainRule
import Poincare.Global.ParabolicHessianCarrierPullback

/-!
# Nonlinear spatial pullback of genuine derivative graphs

The two chain-rule terms of the Hessian are assembled in the original
four-carrier norm. Time remains unchanged, including its within-interval
derivative certificate.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff NNReal

namespace Poincare.ParabolicSpatialGraphPullback

open ParabolicHolder ParabolicSolutionGraph ParabolicCutoffCommutator
open ParabolicSpatialHolderPullback
local notation "E" => ClosedSmoothModel 3
local notation "End" => E →L[ℝ] E
local notation "Cov" => E →L[ℝ] ℝ
local notation "Hess" => E →L[ℝ] Cov
local notation "DDF" => E →L[ℝ] End

local instance endNormedGroup : NormedAddCommGroup End := inferInstance
local instance endNormedSpace : NormedSpace ℝ End := inferInstance
local instance secondDerivativeNormedGroup : NormedAddCommGroup DDF := inferInstance
local instance secondDerivativeNormedSpace : NormedSpace ℝ DDF := inferInstance

local instance covectorNormedGroup : NormedAddCommGroup Cov := inferInstance
local instance covectorNormedSpace : NormedSpace ℝ Cov := inferInstance
local instance hessianNormedGroup : NormedAddCommGroup Hess := inferInstance
local instance hessianNormedSpace : NormedSpace ℝ Hess :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }

/-- Composition of a covector with the second derivative of the spatial map. -/
def secondDerivativeComposition : Cov →L[ℝ] DDF →L[ℝ] Hess :=
  (ContinuousLinearMap.compL ℝ E End Cov).comp
    (ContinuousLinearMap.compL ℝ E E ℝ)

variable {α T : ℝ}

/-- Assemble the actual pulled-back jets and their derivative certificates. -/
def graphOfCarriers
    (F : E → E) (hF : ContDiff ℝ ∞ F) (hα : 0 ≤ α)
    {L : ℝ≥0} (hL : LipschitzWith L F)
    (dF : Y («E» := E) α T End) (ddF : Y («E» := E) α T DDF)
    (hdF : ∀ p ∈ cylinder T, dF p = fderiv ℝ F p.2)
    (hddF : ∀ p ∈ cylinder T, ddF p = fderiv ℝ (fderiv ℝ F) p.2)
    (P : Y («E» := E) α T Hess →L[ℝ] Y («E» := E) α T Hess)
    (hP : ∀ B p (v w : E), P B p v w = B p (dF p v) (dF p w))
    (G : Graph («E» := E) α T) : Graph («E» := E) α T where
  u := pullback hα F hL G.u
  ut := pullback hα F hL G.ut
  du := bilinearY (ContinuousLinearMap.compL ℝ E E ℝ)
    (pullback hα F hL G.du) dF
  ddu := P (pullback hα F hL G.ddu) +
    bilinearY secondDerivativeComposition (pullback hα F hL G.du) ddF
  zero_trace := by
    intro x
    exact G.zero_trace (F x)
  hasFDeriv := by
    intro t ht x
    have hx : (t, x) ∈ cylinder T := ⟨ht, mem_univ x⟩
    convert (G.hasFDeriv t ht (F x)).comp x
      (hF.differentiable (by simp) x).hasFDerivAt using 1
    simp only [bilinearY, ofFunction_apply, hdF (t, x) hx]
    rfl
  hasFDeriv_du := by
    intro t ht x
    have hmem (z : E) : (t, z) ∈ cylinder T := ⟨ht, mem_univ z⟩
    convert ParabolicSpatialPullbackChainRule.hasFDerivAt_graph_covector_pullback
      F hF α T G t ht x using 1
    · funext z
      simp only [bilinearY, ofFunction_apply, hdF (t, z) (hmem z)]
      rfl
    · ext v w
      simp only [add_apply, ContinuousLinearMap.add_apply, bilinearY, ofFunction_apply,
        hP, hdF (t, x) (hmem x), hddF (t, x) (hmem x)]
      rfl
  hasDeriv_time := by
    intro t ht x
    exact G.hasDeriv_time t ht (F x)

/-- The two spatial chain-rule terms retain the actual ambient-point formulas. -/
theorem graphOfCarriers_jets
    (F : E → E) (hF : ContDiff ℝ ∞ F) (hα : 0 ≤ α)
    {L : ℝ≥0} (hL : LipschitzWith L F)
    (dF : Y («E» := E) α T End) (ddF : Y («E» := E) α T DDF)
    (hdF : ∀ p ∈ cylinder T, dF p = fderiv ℝ F p.2)
    (hddF : ∀ p ∈ cylinder T, ddF p = fderiv ℝ (fderiv ℝ F) p.2)
    (P : Y («E» := E) α T Hess →L[ℝ] Y («E» := E) α T Hess)
    (hP : ∀ B p (v w : E), P B p v w = B p (dF p v) (dF p w))
    (G : Graph («E» := E) α T) (p : ℝ × E) :
    (graphOfCarriers F hF hα hL dF ddF hdF hddF P hP G).u p =
        G.u (p.1, F p.2) ∧
    (graphOfCarriers F hF hα hL dF ddF hdF hddF P hP G).ut p =
        G.ut (p.1, F p.2) ∧
    (∀ v : E, (graphOfCarriers F hF hα hL dF ddF hdF hddF P hP G).du p v =
      G.du (p.1, F p.2) (fderiv ℝ F p.2 v)) ∧
    (∀ v w : E,
      (graphOfCarriers F hF hα hL dF ddF hdF hddF P hP G).ddu p v w =
        G.ddu (p.1, F p.2) (fderiv ℝ F p.2 v) (fderiv ℝ F p.2 w) +
        G.du (p.1, F p.2) (fderiv ℝ (fderiv ℝ F) p.2 v w)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro v
    change G.du (p.1, F p.2) (dF p v) = _
    by_cases hp : p ∈ cylinder T
    · rw [hdF p hp]
    · have hmap : (p.1, F p.2) ∉ cylinder T :=
        fun h ↦ hp ⟨h.1, mem_univ _⟩
      simp only [zero_off G.du hmap, ContinuousLinearMap.zero_apply]
  · intro v w
    change (P (pullback hα F hL G.ddu) p +
      secondDerivativeComposition (G.du (p.1, F p.2)) (ddF p)) v w = _
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, hP]
    change G.ddu (p.1, F p.2) (dF p v) (dF p w) +
      G.du (p.1, F p.2) (ddF p v w) = _
    by_cases hp : p ∈ cylinder T
    · rw [hdF p hp, hddF p hp]
    · have hmap : (p.1, F p.2) ∉ cylinder T :=
        fun h ↦ hp ⟨h.1, mem_univ _⟩
      simp only [zero_off G.du hmap, zero_off G.ddu hmap,
        ContinuousLinearMap.zero_apply]

/-- A full jet estimate uses the original sum of all four carrier norms. -/
theorem norm_graphOfCarriers_le
    (F : E → E) (hF : ContDiff ℝ ∞ F) (hα : 0 ≤ α)
    {L : ℝ≥0} (hL : LipschitzWith L F)
    (dF : Y («E» := E) α T End) (ddF : Y («E» := E) α T DDF)
    (hdF : ∀ p ∈ cylinder T, dF p = fderiv ℝ F p.2)
    (hddF : ∀ p ∈ cylinder T, ddF p = fderiv ℝ (fderiv ℝ F) p.2)
    (P : Y («E» := E) α T Hess →L[ℝ] Y («E» := E) α T Hess)
    (hP : ∀ B p (v w : E), P B p v w = B p (dF p v) (dF p w))
    {K1 K2 KP : ℝ} (hKP : 0 ≤ KP)
    (h1 : ‖dF‖ ≤ K1) (h2 : ‖ddF‖ ≤ K2) (hPN : ‖P‖ ≤ KP)
    (G : Graph («E» := E) α T) :
    ‖graphOfCarriers F hF hα hL dF ddF hdF hddF P hP G‖ ≤
      (2 + 3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ * K1 + KP +
        3 * ‖secondDerivativeComposition‖ * K2) * max 1 ((L : ℝ) ^ α) * ‖G‖ := by
  let S : ℝ := max 1 ((L : ℝ) ^ α)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hu : ‖pullback hα F hL G.u‖ ≤ S * ‖G‖ :=
    (norm_pullback_le hα F hL G.u).trans
      (mul_le_mul_of_nonneg_left (norm_u_le G) hS)
  have hut : ‖pullback hα F hL G.ut‖ ≤ S * ‖G‖ :=
    (norm_pullback_le hα F hL G.ut).trans
      (mul_le_mul_of_nonneg_left (norm_ut_le G) hS)
  have hc : ‖pullback hα F hL G.du‖ ≤ S * ‖G‖ :=
    (norm_pullback_le hα F hL G.du).trans
      (mul_le_mul_of_nonneg_left (norm_du_le G) hS)
  have hh : ‖pullback hα F hL G.ddu‖ ≤ S * ‖G‖ :=
    (norm_pullback_le hα F hL G.ddu).trans
      (mul_le_mul_of_nonneg_left (norm_ddu_le G) hS)
  have hd : ‖bilinearY (ContinuousLinearMap.compL ℝ E E ℝ)
      (pullback hα F hL G.du) dF‖ ≤
      3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ * K1 * S * ‖G‖ := by
    calc
      _ ≤ 3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ *
          ‖pullback hα F hL G.du‖ * ‖dF‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ * (S * ‖G‖) * K1 := by
        gcongr
      _ = _ := by ring
  have hp : ‖P (pullback hα F hL G.ddu)‖ ≤ KP * S * ‖G‖ := by
    calc
      _ ≤ ‖P‖ * ‖pullback hα F hL G.ddu‖ := P.le_opNorm _
      _ ≤ KP * (S * ‖G‖) := by gcongr
      _ = _ := by ring
  have hdd : ‖bilinearY secondDerivativeComposition (pullback hα F hL G.du) ddF‖ ≤
      3 * ‖secondDerivativeComposition‖ * K2 * S * ‖G‖ := by
    calc
      _ ≤ 3 * ‖secondDerivativeComposition‖ *
          ‖pullback hα F hL G.du‖ * ‖ddF‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * ‖secondDerivativeComposition‖ * (S * ‖G‖) * K2 := by gcongr
      _ = _ := by ring
  rw [ParabolicSolutionGraph.norm_eq]
  change ‖pullback hα F hL G.u‖ + ‖pullback hα F hL G.ut‖ +
    ‖bilinearY (ContinuousLinearMap.compL ℝ E E ℝ) (pullback hα F hL G.du) dF‖ +
    ‖P (pullback hα F hL G.ddu) +
      bilinearY secondDerivativeComposition (pullback hα F hL G.du) ddF‖ ≤ _
  have hsum := norm_add_le (P (pullback hα F hL G.ddu))
    (bilinearY secondDerivativeComposition (pullback hα F hL G.du) ddF)
  change _ ≤ (2 + 3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ * K1 + KP +
    3 * ‖secondDerivativeComposition‖ * K2) * S * ‖G‖
  nlinarith only [hu, hut, hd, hp, hdd, hsum]

/-- Compact smooth spatial substitution acts boundedly on the genuine
derivative graph, with one constant before the time interval is selected. -/
theorem exists_spatial_Graph_pullback
    (F : E → E) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Ioc (0 : ℝ) 1,
      ∃ Q : Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T,
        ‖Q‖ ≤ C ∧ ∀ G p,
          (Q G).u p = G.u (p.1, F p.2) ∧
          (Q G).ut p = G.ut (p.1, F p.2) ∧
          (∀ v : E, (Q G).du p v = G.du (p.1, F p.2) (fderiv ℝ F p.2 v)) ∧
          (∀ v w : E, (Q G).ddu p v w =
            G.ddu (p.1, F p.2) (fderiv ℝ F p.2 v) (fderiv ℝ F p.2 w) +
            G.du (p.1, F p.2) (fderiv ℝ (fderiv ℝ F) p.2 v w)) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcF hF (by simp)
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hDDF : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) := hDF.fderiv_right (by simp)
  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hDF (hcF.fderiv ℝ) hα hα1
  obtain ⟨K2, hK2, h2⟩ :=
    exists_cutoff_carrier hDDF ((hcF.fderiv ℝ).fderiv ℝ) hα hα1
  obtain ⟨CH, hCH, hH⟩ := ParabolicHessianCarrierPullback.exists_hessian_carrier_pullback
  let KP : ℝ := CH * K1 ^ 2
  have hKP : 0 ≤ KP := mul_nonneg hCH (sq_nonneg K1)
  let C : ℝ := (2 + 3 * ‖ContinuousLinearMap.compL ℝ E E ℝ‖ * K1 + KP +
    3 * ‖secondDerivativeComposition‖ * K2) * max 1 ((L : ℝ) ^ α)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨dF, hdF, hdFN⟩ := h1 T
  obtain ⟨ddF, hddF, hddFN⟩ := h2 T
  obtain ⟨P, hPN, hP⟩ := hH α T dF
  have hPN' : ‖P‖ ≤ KP := hPN.trans (by
    dsimp only [KP]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg dF) hdFN 2) hCH)
  let Qlin : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T := {
    toFun := graphOfCarriers F hF hα.le hL dF ddF hdF hddF P hP
    map_add' := by
      intro G H
      apply Graph.ext_of_u hT.1
      apply ParabolicHolder.ext
      intro p _
      rfl
    map_smul' := by
      intro c G
      apply Graph.ext_of_u hT.1
      apply ParabolicHolder.ext
      intro p _
      rfl }
  have hbound : ∀ G, ‖Qlin G‖ ≤ C * ‖G‖ :=
    fun G ↦ norm_graphOfCarriers_le F hF hα.le hL dF ddF hdF hddF P hP
      hKP hdFN hddFN hPN' G
  refine ⟨Qlin.mkContinuous C hbound, Qlin.mkContinuous_norm_le hC hbound, ?_⟩
  intro G p
  exact graphOfCarriers_jets F hF hα.le hL dF ddF hdF hddF P hP G p

end Poincare.ParabolicSpatialGraphPullback
