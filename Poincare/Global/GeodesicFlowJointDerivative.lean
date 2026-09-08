import Poincare.Global.ParameterizedFlowDerivative
import Poincare.Global.LinearEndpointGronwall
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Joint initial-state variations of a fixed-chart geodesic flow

The variational unknown is a continuous linear endomorphism of the entire
position-velocity state space. Its initial value is the identity.
-/

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Asymptotics Filter Function Metric Set
open scoped Topology NNReal ContDiff Manifold

namespace Poincare
namespace GeodesicFlowJointDerivative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bounded continuous coefficient admits an operator-valued fundamental
solution on a prescribed short interval. Every initial direction, including
both position and velocity, is evaluated from the same operator solution. -/
theorem exists_fundamentalSolution_on_prescribed_Icc [CompleteSpace X]
    {A : ℝ → X →L[ℝ] X} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc (-T) T)) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ (K : ℝ))
    (hKT : (K : ℝ) * T ≤ 1 / 4) :
    ∃ Φ : ℝ → X →L[ℝ] X,
      Φ 0 = ContinuousLinearMap.id ℝ X ∧
      (∀ t ∈ Icc (-T) T, HasDerivWithinAt Φ ((A t).comp (Φ t))
        (Icc (-T) T) t) ∧
      ∀ h : X, ∀ t ∈ Icc (-T) T,
        HasDerivWithinAt (fun s => Φ s h) (A t (Φ t h)) (Icc (-T) T) t := by
  let B : ℝ → (X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
    fun t => ContinuousLinearMap.compL ℝ X X X (A t)
  have hB : ∀ t ∈ Icc (-T) T, ‖B t‖ ≤ (K : ℝ) := by
    intro t ht
    calc
      ‖B t‖ ≤ (1 : ℝ) * ‖A t‖ :=
        by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ X X X)
              (norm_nonneg _))
      _ ≤ 1 * (K : ℝ) := mul_le_mul_of_nonneg_left (hK t ht) zero_le_one
      _ = (K : ℝ) := one_mul _
  have hpl : IsPicardLindelof (fun t Y => B t Y)
      (tmin := -T) (tmax := T) ⟨0, by constructor <;> linarith⟩
      (ContinuousLinearMap.id ℝ X) 1 (1 / 2) (2 * K) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hB t ht)).lipschitzOnWith
    · intro Y _
      exact ((ContinuousLinearMap.compL ℝ X X X).continuous.comp_continuousOn hA).clm_apply
        continuousOn_const
    · intro t ht Y hY
      have hYnorm : ‖Y‖ ≤ 2 := by
        have hd : ‖Y - ContinuousLinearMap.id ℝ X‖ ≤ 1 := by
          simpa [mem_closedBall, dist_eq_norm] using hY
        exact (norm_le_norm_sub_add Y (ContinuousLinearMap.id ℝ X)).trans
          (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := X)])
      calc
        ‖B t Y‖ ≤ ‖B t‖ * ‖Y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K : ℝ) * 2 := mul_le_mul (hB t ht) hYnorm (norm_nonneg _) K.2
        _ = ((2 * K : ℝ≥0) : ℝ) := by simp; ring
    · simp only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_mul,
        NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_div]
      nlinarith
  obtain ⟨Φ, hΦ0, hΦ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (mem_closedBall_self (by positivity))
  refine ⟨Φ, hΦ0, hΦ, ?_⟩
  intro h t ht
  simpa [B] using (hΦ t ht).clm_apply (hasDerivWithinAt_const t (Icc (-T) T) h)

/-- The Gronwall residual theorem with the identity initial-state injection.
The perturbation ranges over the whole state space. -/
theorem initialState_residual_isLittleO [ProperSpace X]
    {F : X → X} (hF : ContDiff ℝ 1 F)
    {α : X → ℝ → X} {Φ : ℝ → X →L[ℝ] X}
    {p q : X} {r a T t : ℝ} (hT : 0 < T) (hq : q ∈ ball p r)
    (hα : ∀ y ∈ ball p r, α y 0 = y ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (α y) (F (α y s)) (Icc 0 T) s) ∧
      ∀ s ∈ Icc 0 T, α y s ∈ closedBall p a)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ X)
    (hΦ : ∀ s ∈ Icc 0 T, HasDerivWithinAt Φ
      ((fderiv ℝ F (α q s)).comp (Φ s)) (Icc 0 T) s)
    (ht : t ∈ Icc 0 T) :
    (fun h : X => α (q + h) t - α q t - Φ t h) =o[𝓝 (0 : X)] (fun h => h) := by
  obtain ⟨K, hLip⟩ := hF.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall p (a + 1)) (isCompact_closedBall p (a + 1))
  have hpert : ∀ᶠ h in 𝓝 (0 : X),
      α (q + h) 0 = α q 0 + (ContinuousLinearMap.id ℝ X) h ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (α (q + h)) (F (α (q + h) s))
        (Icc 0 T) s) ∧ ∀ s ∈ Icc 0 T, α (q + h) s ∈ closedBall p a := by
    have hnear : ∀ᶠ h in 𝓝 (0 : X), q + h ∈ ball p r :=
      (continuousAt_const.add continuousAt_id).preimage_mem_nhds
        (by simpa using isOpen_ball.mem_nhds hq)
    filter_upwards [hnear] with h hh
    exact ⟨by simp [(hα (q + h) hh).1, (hα q hq).1], (hα (q + h) hh).2⟩
  have hlin : ∀ᶠ h in 𝓝 (0 : X),
      Φ 0 h = (ContinuousLinearMap.id ℝ X) h ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => Φ s h)
        (fderiv ℝ F (α q s) (Φ s h)) (Icc 0 T) s) ∧ Φ t h = Φ t h := by
    apply Filter.Eventually.of_forall
    intro h
    refine ⟨by rw [hΦ0], ?_, rfl⟩
    intro s hs
    simpa using (hΦ s hs).clm_apply (hasDerivWithinAt_const s (Icc 0 T) h)
  have hd := parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
    (J := ContinuousLinearMap.id ℝ X) (Ψ := fun h s => Φ s h)
    hT hLip
    (uniform_taylor_remainder_norm_le_on_compact_convex hF
      (isCompact_closedBall p (a + 1)) (convex_closedBall p (a + 1)))
    (hα q hq).2.1 (hα q hq).2.2 hpert hlin ht
  exact hasFDerivAt_iff_isLittleO_nhds_zero.mp hd

/-- Reflection of a symmetric-interval solution onto its positive half. -/
theorem hasDerivWithinAt_reflect {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ → Y} {f' : Y} {T s : ℝ}
    (hf : HasDerivWithinAt f f' (Icc (-T) T) (-s)) :
    HasDerivWithinAt (fun u => f (-u)) (-f') (Icc 0 T) s := by
  have hm : MapsTo (fun u : ℝ => -u) (Icc 0 T) (Icc (-T) T) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  simpa [Function.comp_def] using hf.scomp s (hasDerivAt_neg s).hasDerivWithinAt hm

/-- Full-state Frechet differentiability on both halves of the PL interval. -/
theorem flow_hasFDerivAt_initialState [ProperSpace X]
    {F : X → X} (hF : ContDiff ℝ 1 F)
    {α : X → ℝ → X} {Φ : ℝ → X →L[ℝ] X}
    {p q : X} {r a T t : ℝ} (hT : 0 < T) (hq : q ∈ ball p r)
    (hα : ∀ y ∈ ball p r, α y 0 = y ∧
      (∀ s ∈ Icc (-T) T, HasDerivWithinAt (α y) (F (α y s)) (Icc (-T) T) s) ∧
      ∀ s ∈ Icc (-T) T, α y s ∈ closedBall p a)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ X)
    (hΦ : ∀ s ∈ Icc (-T) T, HasDerivWithinAt Φ
      ((fderiv ℝ F (α q s)).comp (Φ s)) (Icc (-T) T) s)
    (ht : t ∈ Icc (-T) T) :
    HasFDerivAt (fun y => α y t) (Φ t) q := by
  have hsub : Icc (0 : ℝ) T ⊆ Icc (-T) T := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  by_cases ht0 : 0 ≤ t
  · apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
    apply initialState_residual_isLittleO (a := a) hF hT hq ?_ hΦ0 ?_ ⟨ht0, ht.2⟩
    · intro y hy
      exact ⟨(hα y hy).1, fun s hs => ((hα y hy).2.1 s (hsub hs)).mono hsub,
        fun s hs => (hα y hy).2.2 s (hsub hs)⟩
    · intro s hs
      exact (hΦ s (hsub hs)).mono hsub
  · have hn : -t ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.1]⟩
    have hnegmem : ∀ s ∈ Icc (0 : ℝ) T, -s ∈ Icc (-T) T := by
      intro s hs
      constructor <;> linarith [hs.1, hs.2]
    have hαn : ∀ y ∈ ball p r, α y (-0) = y ∧
        (∀ s ∈ Icc 0 T, HasDerivWithinAt (fun u => α y (-u))
          (-F (α y (-s))) (Icc 0 T) s) ∧
        ∀ s ∈ Icc 0 T, α y (-s) ∈ closedBall p a := by
      intro y hy
      exact ⟨by simpa using (hα y hy).1,
        fun s hs => hasDerivWithinAt_reflect ((hα y hy).2.1 (-s) (hnegmem s hs)),
        fun s hs => (hα y hy).2.2 (-s) (hnegmem s hs)⟩
    have hΦn : ∀ s ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt (fun u => Φ (-u))
          ((fderiv ℝ (-F) (α q (-s))).comp (Φ (-s))) (Icc 0 T) s := by
      intro s hs
      simpa only [fderiv_neg, ContinuousLinearMap.neg_comp] using
        hasDerivWithinAt_reflect (hΦ (-s) (hnegmem s hs))
    have hnres := initialState_residual_isLittleO
      (α := fun y s => α y (-s)) (Φ := fun s => Φ (-s))
      hF.neg hT hq hαn
      (by simpa using hΦ0) hΦn hn
    apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
    simpa only [neg_neg] using hnres

/-- Uniform dependence of the fundamental solution on its initial state,
proved by comparing the two coefficient curves with Gronwall. -/
theorem exists_fundamentalSolution_lipschitzOn_initialState [ProperSpace X]
    {F : X → X} (hF : ContDiff ℝ 2 F)
    {α : X → ℝ → X} {Φ : X → ℝ → X →L[ℝ] X}
    {p : X} {r a T : ℝ} (hT : 0 ≤ T)
    (hα : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (α q) (F (α q s)) (Icc 0 T) s) ∧
      ∀ s ∈ Icc 0 T, α q s ∈ closedBall p a)
    (hΦ0 : ∀ q ∈ ball p r, Φ q 0 = ContinuousLinearMap.id ℝ X)
    (hΦ : ∀ q ∈ ball p r, ∀ s ∈ Icc 0 T, HasDerivWithinAt (Φ q)
      ((fderiv ℝ F (α q s)).comp (Φ q s)) (Icc 0 T) s) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc 0 T, LipschitzOnWith C (fun q => Φ q t) (ball p r) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  obtain ⟨K, hLip⟩ := hF1.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall p (a + 1)) (isCompact_closedBall p (a + 1))
  obtain ⟨L, hcoeff⟩ := (hF.fderiv_right (m := 1) (by norm_num)).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall p a) (isCompact_closedBall p a)
  let J := ContinuousLinearMap.id ℝ X
  let B : ℝ≥0 := ⟨‖J‖ * Real.exp ((K : ℝ) * T), by positivity⟩
  let C : ℝ := ‖J‖ * ‖J‖ * ((L : ℝ) * (B : ℝ)) *
    Real.exp ((K : ℝ) * T) * gronwallBound 0 K 1 T
  refine ⟨C.toNNReal, ?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro q₂ hq₂ q₁ hq₁
  have hbound : ∀ q ∈ ball p r, ∀ s ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ F (α q s)‖ ≤ (K : ℝ) := by
    intro q hq s hs
    exact norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ)
      (closedBall_radius_add_one_mem_nhds ((hα q hq).2.2 s (Ico_subset_Icc_self hs))) hLip
  have hlin : ∀ q ∈ ball p r, ∀ h : X, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => Φ q u h) (fderiv ℝ F (α q s) (Φ q s h))
        (Icc 0 T) s := by
    intro q hq h s hs
    simpa using (hΦ q hq s hs).clm_apply (hasDerivWithinAt_const s (Icc 0 T) h)
  have hdiff : ∀ s ∈ Ico (0 : ℝ) T,
      ‖α q₂ s - α q₁ s‖ ≤ (B : ℝ) * ‖q₂ - q₁‖ := by
    intro s hs
    exact parameterizedFlow_sub_norm_le_of_initial_clm J hLip
      (by simp [J, (hα q₂ hq₂).1, (hα q₁ hq₁).1])
      (hα q₁ hq₁).2.1 (hα q₂ hq₂).2.1
      (hα q₁ hq₁).2.2 (hα q₂ hq₂).2.2 (Ico_subset_Icc_self hs)
  have hb := projected_linearODE_endpoint_clm_lipschitz_of_base_curves
    (F := F) (γ₁ := α q₁) (γ₂ := α q₂)
    (Ω₁ := fun h s => Φ q₁ s h) (Ω₂ := fun h s => Φ q₂ s h)
    (D₁ := Φ q₁ t) (D₂ := Φ q₂ t) J J hT K.2 (norm_nonneg (q₂ - q₁)) hcoeff
    (fun s hs => (hα q₁ hq₁).2.2 s (Ico_subset_Icc_self hs))
    (fun s hs => (hα q₂ hq₂).2.2 s (Ico_subset_Icc_self hs)) hdiff
    (hbound q₁ hq₁) (hbound q₂ hq₂)
    (fun h => by simp [hΦ0 q₁ hq₁, J]) (fun h => by simp [hΦ0 q₂ hq₂, J])
    (hlin q₁ hq₁) (hlin q₂ hq₂) (fun _ => rfl) (fun _ => rfl) ht
  rw [dist_eq_norm, dist_eq_norm]
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _))

/-- The fundamental solution is jointly continuous in initial state and time. -/
theorem continuousOn_fundamentalSolution [ProperSpace X]
    {F : X → X} (hF : ContDiff ℝ 2 F)
    {α : X → ℝ → X} {Φ : X → ℝ → X →L[ℝ] X}
    {p : X} {r a T : ℝ} (hT : 0 ≤ T)
    (hα : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc (-T) T, HasDerivWithinAt (α q) (F (α q s)) (Icc (-T) T) s) ∧
      ∀ s ∈ Icc (-T) T, α q s ∈ closedBall p a)
    (hΦ0 : ∀ q ∈ ball p r, Φ q 0 = ContinuousLinearMap.id ℝ X)
    (hΦ : ∀ q ∈ ball p r, ∀ s ∈ Icc (-T) T, HasDerivWithinAt (Φ q)
      ((fderiv ℝ F (α q s)).comp (Φ q s)) (Icc (-T) T) s) :
    ContinuousOn (fun qt : X × ℝ => Φ qt.1 qt.2) (ball p r ×ˢ Icc (-T) T) := by
  have hsub : Icc (0 : ℝ) T ⊆ Icc (-T) T := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hnegmem : ∀ s ∈ Icc (0 : ℝ) T, -s ∈ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨Cpos, hplus⟩ := exists_fundamentalSolution_lipschitzOn_initialState
    (a := a) hF hT
    (fun q hq => ⟨(hα q hq).1,
      fun s hs => ((hα q hq).2.1 s (hsub hs)).mono hsub,
      fun s hs => (hα q hq).2.2 s (hsub hs)⟩)
    hΦ0 (fun q hq s hs => (hΦ q hq s (hsub hs)).mono hsub)
  have hαn : ∀ q ∈ ball p r, α q (-0) = q ∧
      (∀ s ∈ Icc 0 T, HasDerivWithinAt (fun u => α q (-u))
        (-F (α q (-s))) (Icc 0 T) s) ∧
      ∀ s ∈ Icc 0 T, α q (-s) ∈ closedBall p a := by
    intro q hq
    exact ⟨by simpa using (hα q hq).1,
      fun s hs => hasDerivWithinAt_reflect ((hα q hq).2.1 (-s) (hnegmem s hs)),
      fun s hs => (hα q hq).2.2 (-s) (hnegmem s hs)⟩
  have hΦn : ∀ q ∈ ball p r, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => Φ q (-u))
        ((fderiv ℝ (-F) (α q (-s))).comp (Φ q (-s))) (Icc 0 T) s := by
    intro q hq s hs
    simpa only [fderiv_neg, ContinuousLinearMap.neg_comp] using
      hasDerivWithinAt_reflect (hΦ q hq (-s) (hnegmem s hs))
  obtain ⟨Cneg, hminus⟩ := exists_fundamentalSolution_lipschitzOn_initialState
    (α := fun q s => α q (-s)) (Φ := fun q s => Φ q (-s)) hF.neg hT hαn
    (by simpa using hΦ0) hΦn
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ (max Cpos Cneg)
  · intro q hq
    exact HasDerivWithinAt.continuousOn (hΦ q hq)
  · intro t ht
    by_cases ht0 : 0 ≤ t
    · exact (hplus t ⟨ht0, ht.2⟩).weaken (le_max_left _ _)
    · have hn : -t ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.1]⟩
      simpa only [neg_neg] using (hminus (-t) hn).weaken (le_max_right Cpos Cneg)

/-- A uniform flow in a compact state tube has a jointly continuous
fundamental solution on one smaller common interval, and its endpoints are C1
in the full initial state. The flow itself is the supplied PL selector. -/
theorem exists_flow_initialState_C1 [ProperSpace X] [CompleteSpace X]
    {F : X → X} (hF : ContDiff ℝ 2 F)
    {α : X → ℝ → X} {p : X} {r a ε : ℝ} (hε : 0 < ε)
    (hα : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (α q) (F (α q s)) (Icc (-ε) ε) s) ∧
      ∀ s ∈ Icc (-ε) ε, α q s ∈ closedBall p a) :
    ∃ T > (0 : ℝ), T ≤ ε ∧ ∃ Φ : X → ℝ → X →L[ℝ] X,
      (∀ q ∈ ball p r, Φ q 0 = ContinuousLinearMap.id ℝ X) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T, HasDerivWithinAt (Φ q)
        ((fderiv ℝ F (α q t)).comp (Φ q t)) (Icc (-T) T) t) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T,
        HasFDerivAt (fun y => α y t) (Φ q t) q) ∧
      ContinuousOn (fun qt : X × ℝ => Φ qt.1 qt.2) (ball p r ×ˢ Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T, ContDiffOn ℝ 1 (fun q => α q t) (ball p r) := by
  classical
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  obtain ⟨K, hLip⟩ := hF1.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall p (a + 1)) (isCompact_closedBall p (a + 1))
  let T : ℝ := min ε (1 / (4 * ((K : ℝ) + 1)))
  have hT : 0 < T := lt_min hε (by positivity)
  have hTε : T ≤ ε := min_le_left _ _
  have hKT : (K : ℝ) * T ≤ 1 / 4 := by
    have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
    calc
      (K : ℝ) * T ≤ (K : ℝ) * (1 / (4 * ((K : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) K.2
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
        nlinarith
  have hsub : Icc (-T) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2.trans hTε⟩
  have hαT : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc (-T) T, HasDerivWithinAt (α q) (F (α q s)) (Icc (-T) T) s) ∧
      ∀ s ∈ Icc (-T) T, α q s ∈ closedBall p a := by
    intro q hq
    exact ⟨(hα q hq).1, fun s hs => ((hα q hq).2.1 s (hsub hs)).mono hsub,
      fun s hs => (hα q hq).2.2 s (hsub hs)⟩
  have hex : ∀ q : X, ∃ Φ : ℝ → X →L[ℝ] X, q ∈ ball p r →
      Φ 0 = ContinuousLinearMap.id ℝ X ∧
      ∀ s ∈ Icc (-T) T, HasDerivWithinAt Φ
        ((fderiv ℝ F (α q s)).comp (Φ s)) (Icc (-T) T) s := by
    intro q
    by_cases hq : q ∈ ball p r
    · have hc : ContinuousOn (fun s => fderiv ℝ F (α q s)) (Icc (-T) T) :=
        (hF1.continuous_fderiv (by norm_num)).comp_continuousOn
          (HasDerivWithinAt.continuousOn (hαT q hq).2.1)
      obtain ⟨Φ, h0, hd, _⟩ := exists_fundamentalSolution_on_prescribed_Icc hT.le hc K
        (fun s hs => norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ)
          (closedBall_radius_add_one_mem_nhds ((hαT q hq).2.2 s hs)) hLip) hKT
      exact ⟨Φ, fun _ => ⟨h0, hd⟩⟩
    · exact ⟨fun _ => ContinuousLinearMap.id ℝ X, fun h => (hq h).elim⟩
  choose Φ hΦ using hex
  have h0 := fun q hq => (hΦ q hq).1
  have hd := fun q hq => (hΦ q hq).2
  have hder : ∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T,
      HasFDerivAt (fun y => α y t) (Φ q t) q :=
    fun q hq t ht => flow_hasFDerivAt_initialState hF1 hT hq hαT (h0 q hq) (hd q hq) ht
  have hc := continuousOn_fundamentalSolution hF hT.le hαT h0 hd
  refine ⟨T, hT, hTε, Φ, h0, hd, hder, hc, ?_⟩
  intro t ht q hq
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_one_iff.mpr
  refine ⟨fun y => Φ y t, ball p r, isOpen_ball.mem_nhds hq, ?_, fun y hy => hder y hy t ht⟩
  exact hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy, ht⟩)

/-- Local C2 regularity near a compact set can be used in the global Gronwall
lemmas. The extension agrees as a germ at every point of the compact set. -/
theorem exists_contDiff_extension_near_compact [FiniteDimensional ℝ X]
    {F : X → X} {U K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hF : ∀ x ∈ U, ContDiffAt ℝ 2 F x) :
    ∃ G : X → X, ContDiff ℝ 2 G ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] F := by
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (I := 𝓘(ℝ, X)) (n := 2) hU.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr (fun x hx hk => hx (hKU hk)))
  have hχ : ContDiff ℝ 2 (χ : X → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  let G : X → X := fun x => χ x • F x
  refine ⟨G, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hF x hx)
    · have heq : G =ᶠ[𝓝 x] (fun _ => (0 : X)) := by
        filter_upwards [eventually_nhdsSet_iff_forall.mp hzero x hx] with y hy
        simp [G, hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro x hx
    filter_upwards [eventually_nhdsSet_iff_forall.mp hone x hx] with y hy
    simp [G, hy]

/-- Extend the vector field around the compact image of the given uniform
flow. This changes neither the selected flow nor its linearization there. -/
theorem exists_smoothField_near_uniformFlow [FiniteDimensional ℝ X]
    {F : X → X} {U : Set X} (hU : IsOpen U)
    (hF : ∀ x ∈ U, ContDiffAt ℝ 2 F x)
    {α : X → ℝ → X} {p : X} {r ε : ℝ}
    (hcont : ContinuousOn (Function.uncurry α) (closedBall p r ×ˢ Icc (-ε) ε))
    (hmem : ∀ q ∈ closedBall p r, ∀ t ∈ Icc (-ε) ε, α q t ∈ U) :
    ∃ G : X → X, ContDiff ℝ 2 G ∧ ∃ a : ℝ,
      ∀ q ∈ closedBall p r, ∀ t ∈ Icc (-ε) ε,
        α q t ∈ closedBall p a ∧ G =ᶠ[𝓝 (α q t)] F := by
  let K := (Function.uncurry α) '' (closedBall p r ×ˢ Icc (-ε) ε)
  have hK : IsCompact K :=
    ((isCompact_closedBall p r).prod isCompact_Icc).image_of_continuousOn hcont
  obtain ⟨G, hG, heq⟩ := exists_contDiff_extension_near_compact hU hK
    (by rintro _ ⟨⟨q, t⟩, hqt, rfl⟩; exact hmem q hqt.1 t hqt.2) hF
  obtain ⟨a, ha⟩ := hK.isBounded.subset_closedBall p
  refine ⟨G, hG, a, ?_⟩
  intro q hq t ht
  have hk : α q t ∈ K := ⟨(q, t), ⟨hq, ht⟩, rfl⟩
  exact ⟨ha hk, heq _ hk⟩

/-- Joint C1 dependence under local C2 regularity on an open set containing
all the trajectories in the supplied continuous PL package. -/
theorem exists_flow_initialState_C1_of_contDiffAt [FiniteDimensional ℝ X]
    {F : X → X} {U : Set X} (hU : IsOpen U)
    (hF : ∀ x ∈ U, ContDiffAt ℝ 2 F x)
    {α : X → ℝ → X} {p : X} {r ε : ℝ} (hε : 0 < ε)
    (hcont : ContinuousOn (Function.uncurry α) (closedBall p r ×ˢ Icc (-ε) ε))
    (hmem : ∀ q ∈ closedBall p r, ∀ t ∈ Icc (-ε) ε, α q t ∈ U)
    (hα : ∀ q ∈ closedBall p r, α q 0 = q ∧
      ∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (α q) (F (α q s)) (Icc (-ε) ε) s) :
    ∃ T > (0 : ℝ), T ≤ ε ∧ ∃ Φ : X → ℝ → X →L[ℝ] X,
      (∀ q ∈ ball p r, Φ q 0 = ContinuousLinearMap.id ℝ X) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T, HasDerivWithinAt (Φ q)
        ((fderiv ℝ F (α q t)).comp (Φ q t)) (Icc (-T) T) t) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T,
        HasFDerivAt (fun y => α y t) (Φ q t) q) ∧
      ContinuousOn (fun qt : X × ℝ => Φ qt.1 qt.2) (ball p r ×ˢ Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T, ContDiffOn ℝ 1 (fun q => α q t) (ball p r) := by
  obtain ⟨G, hG, a, hGa⟩ := exists_smoothField_near_uniformFlow hU hF hcont hmem
  have hαG : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (α q) (G (α q s)) (Icc (-ε) ε) s) ∧
      ∀ s ∈ Icc (-ε) ε, α q s ∈ closedBall p a := by
    intro q hq
    have hqc := ball_subset_closedBall hq
    refine ⟨(hα q hqc).1, ?_, fun s hs => (hGa q hqc s hs).1⟩
    intro s hs
    rw [(hGa q hqc s hs).2.eq_of_nhds]
    exact (hα q hqc).2 s hs
  obtain ⟨T, hT, hTε, Φ, h0, hd, hf, hc, hC1⟩ := exists_flow_initialState_C1 hG hε hαG
  refine ⟨T, hT, hTε, Φ, h0, ?_, hf, hc, hC1⟩
  intro q hq t ht
  have htε : t ∈ Icc (-ε) ε := ⟨by linarith [ht.1], ht.2.trans hTε⟩
  simpa only [(hGa q (ball_subset_closedBall hq) t htε).2.fderiv_eq] using hd q hq t ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- C2 Christoffel regularity gives C2 regularity of the full state field. -/
theorem contDiffAt_geodesicFlowField_two
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p : E × E}
    (hΓ : ContDiffAt ℝ 2 Γ p.1) : ContDiffAt ℝ 2 (geodesicFlowField Γ) p := by
  have hΓp := hΓ.comp p (contDiffAt_fst : ContDiffAt ℝ 2 (fun p : E × E => p.1) p)
  have hv : ContDiffAt ℝ 2 (fun p : E × E => p.2) p := contDiffAt_snd
  exact hv.prodMk ((hΓp.clm_apply hv).clm_apply hv).neg

/-- The joint initial-position/initial-velocity C1 package for a Christoffel
field that is C2 only on the open chart region occupied by the trajectories. -/
theorem exists_geodesic_flow_initialState_C1 [FiniteDimensional ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {U : Set E} (hU : IsOpen U)
    (hΓ : ∀ z ∈ U, ContDiffAt ℝ 2 Γ z)
    {α : (E × E) → ℝ → E × E} {z₀ : E} {r ε : ℝ} (hε : 0 < ε)
    (hcont : ContinuousOn (Function.uncurry α)
      (closedBall (z₀, (0 : E)) r ×ˢ Icc (-ε) ε))
    (hmem : ∀ q ∈ closedBall (z₀, (0 : E)) r,
      ∀ t ∈ Icc (-ε) ε, (α q t).1 ∈ U)
    (hα : ∀ q ∈ closedBall (z₀, (0 : E)) r, α q 0 = q ∧
      ∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (α q)
        (geodesicFlowField Γ (α q t)) (Icc (-ε) ε) t) :
    ∃ T > (0 : ℝ), T ≤ ε ∧ ∃ Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E),
      (∀ q ∈ ball (z₀, (0 : E)) r, Φ q 0 = ContinuousLinearMap.id ℝ (E × E)) ∧
      (∀ q ∈ ball (z₀, (0 : E)) r, ∀ t ∈ Icc (-T) T, HasDerivWithinAt (Φ q)
        ((linearizedGeodesicFlowOperator Γ (α q t)).comp (Φ q t)) (Icc (-T) T) t) ∧
      (∀ q ∈ ball (z₀, (0 : E)) r, ∀ t ∈ Icc (-T) T,
        HasFDerivAt (fun y => α y t) (Φ q t) q) ∧
      ContinuousOn (fun qt : (E × E) × ℝ => Φ qt.1 qt.2)
        (ball (z₀, (0 : E)) r ×ˢ Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T, ContDiffOn ℝ 1 (fun q => α q t) (ball (z₀, (0 : E)) r) := by
  exact exists_flow_initialState_C1_of_contDiffAt (hU.preimage continuous_fst)
    (fun q hq => contDiffAt_geodesicFlowField_two (hΓ q.1 hq)) hε hcont hmem hα

end GeodesicFlowJointDerivative
end Poincare
