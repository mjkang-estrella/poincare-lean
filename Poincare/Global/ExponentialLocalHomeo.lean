import Poincare.Global.ExponentialFrechet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local homeomorphism boundary for the fixed-time exponential

This module upgrades the charted fixed-time exponential to a strict derivative
statement and packages the inverse-function-theorem payoff.  The main estimate
below is the two-base-point endpoint estimate needed by the strict derivative:
on a common Picard-Lindelöf tube, the failure of the chart-position endpoint
difference to be linear in the initial velocity difference is controlled by the
common time horizon.
-/

noncomputable section

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Two-base-point endpoint estimate for the common chart geodesic flow.

If two small initial velocities are evolved by the same PL chart flow, then the
position difference at time `t` differs from the linear model
`t • (v₂ - v₁)` by at most a constant times `T * ‖v₂ - v₁‖ * ‖t‖`, uniformly
for `t ∈ [0,T]`.  This is the nontrivial estimate needed to upgrade the
one-variable remainder from `ExponentialFrechet` to the strict, two-variable
remainder.
-/
theorem chart_flow_position_pair_sub_linear_norm_le
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ ε T : ℝ} {a K : ℝ≥0} {α : E × E → ℝ → E × E}
    {v₁ v₂ : E} {t : ℝ}
    (hε : 0 < ε) (hT_nonneg : 0 ≤ T) (hTε : T ≤ ε)
    (hv₁ : ‖v₁‖ < δ) (hv₂ : ‖v₂‖ < δ)
    (hLip : LipschitzOnWith K
      (geodesicFlowField (chartChristoffelField g x₀))
      (closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)))
    (hα : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ τ ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) τ))
            (Icc (-ε) ε) τ) ∧
        ∀ τ ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) τ ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ))
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖((α (extChartAt I x₀ x₀, v₂) t).1 -
        (α (extChartAt I x₀ x₀, v₁) t).1) - t • (v₂ - v₁)‖ ≤
      (((K : ℝ) * Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖) * T) * ‖t‖ := by
  let z₀ : E := extChartAt I x₀ x₀
  let F : E × E → E × E :=
    geodesicFlowField (chartChristoffelField g x₀)
  let Cacc : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖
  have hCacc_nonneg : 0 ≤ Cacc := by
    dsimp [Cacc]
    positivity
  have hIcc_subset : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) ε := by
    intro τ hτ
    exact ⟨hτ.1, hτ.2.trans hTε⟩
  have hfull_subset : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro τ hτ
    exact ⟨by linarith [hε, hτ.1], hτ.2.trans hTε⟩
  have hbase₁ := hα v₁ hv₁
  have hbase₂ := hα v₂ hv₂
  have hstate_bound : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖α (z₀, v₂) τ - α (z₀, v₁) τ‖ ≤
        Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖ := by
    intro τ hτ
    have hτe : τ ∈ Icc (0 : ℝ) ε := hIcc_subset hτ
    have hstate_lip :
        LipschitzOnWith
          ⟨Real.exp ((K : ℝ) * ε), (Real.exp_pos _).le⟩
          (fun v : E => α (z₀, v) τ)
          (ball (0 : E) δ) := by
      simpa [z₀, F] using
        chart_flow_initialVelocity_lipschitzOn_of_ODE
          (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := (a : ℝ))
          (K := K) (α := α) hε hLip
          (fun v hv => (hα v hv).1)
          (fun v hv r hr => (hα v hv).2.1 r hr)
          (fun v hv r hr => (hα v hv).2.2 r hr)
          hτe
    have hv₁ball : v₁ ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv₁
    have hv₂ball : v₂ ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv₂
    have hdist := hstate_lip.dist_le_mul v₂ hv₂ball v₁ hv₁ball
    simpa [dist_eq_norm] using hdist
  have hacc_bound : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖(F (α (z₀, v₂) τ)).2 - (F (α (z₀, v₁) τ)).2‖ ≤ Cacc := by
    intro τ hτ
    have hτfull : τ ∈ Icc (-ε) ε := hfull_subset hτ
    have hmem₂ :
        α (z₀, v₂) τ ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
      simpa [z₀] using hbase₂.2.2 τ hτfull
    have hmem₁ :
        α (z₀, v₁) τ ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
      simpa [z₀] using hbase₁.2.2 τ hτfull
    have hFdist :
        dist (F (α (z₀, v₂) τ)) (F (α (z₀, v₁) τ)) ≤
          (K : ℝ) * dist (α (z₀, v₂) τ) (α (z₀, v₁) τ) := by
      simpa [F, z₀] using
        hLip.dist_le_mul (α (z₀, v₂) τ) hmem₂ (α (z₀, v₁) τ) hmem₁
    have hsnd_le :
        dist (F (α (z₀, v₂) τ)).2 (F (α (z₀, v₁) τ)).2 ≤
          dist (F (α (z₀, v₂) τ)) (F (α (z₀, v₁) τ)) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    calc
      ‖(F (α (z₀, v₂) τ)).2 - (F (α (z₀, v₁) τ)).2‖
          = dist (F (α (z₀, v₂) τ)).2 (F (α (z₀, v₁) τ)).2 := by
            rw [dist_eq_norm]
      _ ≤ dist (F (α (z₀, v₂) τ)) (F (α (z₀, v₁) τ)) := hsnd_le
      _ ≤ (K : ℝ) * dist (α (z₀, v₂) τ) (α (z₀, v₁) τ) := hFdist
      _ = (K : ℝ) * ‖α (z₀, v₂) τ - α (z₀, v₁) τ‖ := by rw [dist_eq_norm]
      _ ≤ (K : ℝ) * (Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖) := by
        exact mul_le_mul_of_nonneg_left (hstate_bound τ hτ) K.2
      _ = Cacc := by
        simp [Cacc, mul_assoc]
  let Rvel : ℝ → E :=
    fun τ => (α (z₀, v₂) τ).2 - (α (z₀, v₁) τ).2 - (v₂ - v₁)
  have hRvel_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Rvel
        ((F (α (z₀, v₂) τ)).2 - (F (α (z₀, v₁) τ)).2)
        (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    have hτfull : τ ∈ Icc (-ε) ε := hfull_subset hτ
    have hder₂ :=
      (hbase₂.2.1 τ hτfull).mono hfull_subset
    have hder₁ :=
      (hbase₁.2.1 τ hτfull).mono hfull_subset
    have hsnd₂ :
        HasDerivWithinAt (fun r : ℝ => (α (z₀, v₂) r).2)
          (F (α (z₀, v₂) τ)).2 (Icc (0 : ℝ) T) τ := by
      have hraw := hder₂.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [F, z₀] using hraw
    have hsnd₁ :
        HasDerivWithinAt (fun r : ℝ => (α (z₀, v₁) r).2)
          (F (α (z₀, v₁) τ)).2 (Icc (0 : ℝ) T) τ := by
      have hraw := hder₁.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [F, z₀] using hraw
    have hconst :
        HasDerivWithinAt (fun _ : ℝ => v₂ - v₁) (0 : E)
          (Icc (0 : ℝ) T) τ :=
      (hasDerivAt_const τ (v₂ - v₁)).hasDerivWithinAt
    convert (hsnd₂.sub hsnd₁).sub hconst using 1
    · ext r
      simp
  have hRvel_zero : Rvel 0 = 0 := by
    have h₂0 : (α (z₀, v₂) 0).2 = v₂ := by
      simpa [z₀] using congrArg Prod.snd hbase₂.1
    have h₁0 : (α (z₀, v₁) 0).2 = v₁ := by
      simpa [z₀] using congrArg Prod.snd hbase₁.1
    simp [Rvel, h₂0, h₁0]
  have hRvel_bound : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖Rvel τ‖ ≤ Cacc * T := by
    intro τ hτ
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
      left_mem_Icc.mpr hT_nonneg
    have hmvt :
        ‖Rvel τ - Rvel 0‖ ≤ Cacc * ‖τ - 0‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := Rvel)
        (f' := fun r : ℝ => (F (α (z₀, v₂) r)).2 - (F (α (z₀, v₁) r)).2)
        (s := Icc (0 : ℝ) T) (x := 0) (y := τ)
        hRvel_der hacc_bound (convex_Icc (0 : ℝ) T) h0mem hτ
    have hτnorm : ‖τ - 0‖ ≤ T := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      exact hτ.2
    calc
      ‖Rvel τ‖ = ‖Rvel τ - Rvel 0‖ := by rw [hRvel_zero, sub_zero]
      _ ≤ Cacc * ‖τ - 0‖ := hmvt
      _ ≤ Cacc * T := mul_le_mul_of_nonneg_left hτnorm hCacc_nonneg
  let Rpos : ℝ → E :=
    fun τ => ((α (z₀, v₂) τ).1 - (α (z₀, v₁) τ).1) - τ • (v₂ - v₁)
  have hRpos_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Rpos (Rvel τ) (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    have hτfull : τ ∈ Icc (-ε) ε := hfull_subset hτ
    have hder₂ :=
      (hbase₂.2.1 τ hτfull).mono hfull_subset
    have hder₁ :=
      (hbase₁.2.1 τ hτfull).mono hfull_subset
    have hfst₂ :
        HasDerivWithinAt (fun r : ℝ => (α (z₀, v₂) r).1)
          (α (z₀, v₂) τ).2 (Icc (0 : ℝ) T) τ := by
      have hraw := hder₂.hasFDerivWithinAt.fst.hasDerivWithinAt
      simpa [F, geodesicFlowField, z₀] using hraw
    have hfst₁ :
        HasDerivWithinAt (fun r : ℝ => (α (z₀, v₁) r).1)
          (α (z₀, v₁) τ).2 (Icc (0 : ℝ) T) τ := by
      have hraw := hder₁.hasFDerivWithinAt.fst.hasDerivWithinAt
      simpa [F, geodesicFlowField, z₀] using hraw
    have hlin :
        HasDerivWithinAt (fun r : ℝ => r • (v₂ - v₁)) (v₂ - v₁)
          (Icc (0 : ℝ) T) τ := by
      simpa using (((hasDerivAt_id τ).smul_const (v₂ - v₁))).hasDerivWithinAt
    simpa [Rpos, Rvel] using (hfst₂.sub hfst₁).sub hlin
  have hRpos_zero : Rpos 0 = 0 := by
    have h₂0 : (α (z₀, v₂) 0).1 = z₀ := by
      simpa [z₀] using congrArg Prod.fst hbase₂.1
    have h₁0 : (α (z₀, v₁) 0).1 = z₀ := by
      simpa [z₀] using congrArg Prod.fst hbase₁.1
    simp [Rpos, h₂0, h₁0]
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
    left_mem_Icc.mpr hT_nonneg
  have hmvt_pos :
      ‖Rpos t - Rpos 0‖ ≤ (Cacc * T) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Rpos) (f' := Rvel)
      (s := Icc (0 : ℝ) T) (x := 0) (y := t)
      hRpos_der hRvel_bound (convex_Icc (0 : ℝ) T) h0mem ht
  simpa [Rpos, Cacc, hRpos_zero, sub_zero] using hmvt_pos

/-- The charted fixed-time exponential is strictly differentiable at zero. -/
theorem expAt_chart_hasStrictFDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    HasStrictFDerivAt
      (fun v : E => extChartAt I x₀ (expAt g x₀ v))
      (ContinuousLinearMap.id ℝ E) (0 : E) := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, hexp⟩
  rcases geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      (g := g) (x₀ := x₀) (p := (extChartAt I x₀ x₀, (0 : E)))
      (a := (a : ℝ)) with
    ⟨K, hLip⟩
  let z₀ : E := extChartAt I x₀ x₀
  let C₀ : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * ε)
  have hC₀_nonneg : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₀1_pos : 0 < C₀ + 1 := by
    linarith
  let T : ℝ := min τ (min ε (c / (C₀ + 1)))
  have hT_pos : 0 < T := by
    dsimp [T]
    exact lt_min hτ (lt_min hε (div_pos hc hC₀1_pos))
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hTτ : T ≤ τ := by
    dsimp [T]
    exact min_le_left _ _
  have hTε : T ≤ ε := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hC₀T_le : C₀ * T ≤ c := by
    have hTsmall : T ≤ c / (C₀ + 1) := by
      dsimp [T]
      exact (min_le_right _ _).trans (min_le_right _ _)
    calc
      C₀ * T ≤ (C₀ + 1) * T := by
        exact mul_le_mul_of_nonneg_right (by linarith) hT_nonneg
      _ ≤ (C₀ + 1) * (c / (C₀ + 1)) := by
        exact mul_le_mul_of_nonneg_left hTsmall hC₀1_pos.le
      _ = c := by
        field_simp [ne_of_gt hC₀1_pos]
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_ltδ : R < δ := by
    dsimp [R]
    linarith
  have hball :
      ball ((0 : E), (0 : E)) (R * T) ∈ 𝓝 ((0 : E), (0 : E)) :=
    Metric.ball_mem_nhds _ (mul_pos hR_pos hT_pos)
  filter_upwards [hball] with p hp
  have hp_prod :
      p ∈ ball (0 : E) (R * T) ×ˢ ball (0 : E) (R * T) := by
    simpa [ball_prod_same] using hp
  have hp₁_norm_lt : ‖p.1‖ < R * T := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp_prod.1
  have hp₂_norm_lt : ‖p.2‖ < R * T := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp_prod.2
  let m : ℝ := max ‖p.1‖ ‖p.2‖
  have hm_lt : m < R * T := max_lt hp₁_norm_lt hp₂_norm_lt
  by_cases hm0 : m = 0
  · have hp₁_zero : p.1 = 0 := by
      have hle : ‖p.1‖ ≤ 0 := by
        simpa [m, hm0] using (le_max_left ‖p.1‖ ‖p.2‖)
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg p.1))
    have hp₂_zero : p.2 = 0 := by
      have hle : ‖p.2‖ ≤ 0 := by
        simpa [m, hm0] using (le_max_right ‖p.1‖ ‖p.2‖)
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg p.2))
    simp [hp₁_zero, hp₂_zero, expAt_zero]
  · have hm_nonneg : 0 ≤ m := by
      exact le_max_of_le_left (norm_nonneg p.1)
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm0)
    let s : ℝ := m / R
    let v₁ : E := (R / m) • p.2
    let v₂ : E := (R / m) • p.1
    have hs_pos : 0 < s := by
      dsimp [s]
      exact div_pos hm_pos hR_pos
    have hsT_lt : s < T := by
      dsimp [s]
      rw [div_lt_iff₀ hR_pos]
      simpa [mul_comm] using hm_lt
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs_pos.le, le_of_lt hsT_lt⟩
    have hsτ : s ∈ Icc (0 : ℝ) τ := ⟨hs_pos.le, hsT.2.trans hTτ⟩
    have hsε : s ∈ Icc (0 : ℝ) ε := ⟨hs_pos.le, hsT.2.trans hTε⟩
    have hsfull : s ∈ Icc (-ε) ε :=
      ⟨by linarith [hε, hs_pos], hsε.2⟩
    have hv₂_norm_le_R : ‖v₂‖ ≤ R := by
      have hp₁_le_m : ‖p.1‖ ≤ m := le_max_left _ _
      dsimp [v₂]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR_pos hm_pos)]
      calc
        R / m * ‖p.1‖ ≤ R / m * m := by
          exact mul_le_mul_of_nonneg_left hp₁_le_m (div_nonneg hR_pos.le hm_pos.le)
        _ = R := by
          field_simp [ne_of_gt hm_pos]
    have hv₁_norm_le_R : ‖v₁‖ ≤ R := by
      have hp₂_le_m : ‖p.2‖ ≤ m := le_max_right _ _
      dsimp [v₁]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR_pos hm_pos)]
      calc
        R / m * ‖p.2‖ ≤ R / m * m := by
          exact mul_le_mul_of_nonneg_left hp₂_le_m (div_nonneg hR_pos.le hm_pos.le)
        _ = R := by
          field_simp [ne_of_gt hm_pos]
    have hv₂_norm_lt : ‖v₂‖ < δ := hv₂_norm_le_R.trans_lt hR_ltδ
    have hv₁_norm_lt : ‖v₁‖ < δ := hv₁_norm_le_R.trans_lt hR_ltδ
    have hscale₂ : s • v₂ = p.1 := by
      dsimp [s, v₂]
      rw [smul_smul]
      have hcoef : (m / R) * (R / m) = 1 := by
        field_simp [ne_of_gt hR_pos, ne_of_gt hm_pos]
      simp [hcoef]
    have hscale₁ : s • v₁ = p.2 := by
      dsimp [s, v₁]
      rw [smul_smul]
      have hcoef : (m / R) * (R / m) = 1 := by
        field_simp [ne_of_gt hR_pos, ne_of_gt hm_pos]
      simp [hcoef]
    have hchart₂ :
        extChartAt I x₀ (expAt g x₀ p.1) = (α (z₀, v₂) s).1 := by
      have hexp₂ := hexp v₂ hv₂_norm_lt s hsτ
      have htarget₂ : (α (z₀, v₂) s).1 ∈ (extChartAt I x₀).target := by
        simpa [z₀] using (hα v₂ hv₂_norm_lt).2.2.2.1 s hsfull
      rw [← hscale₂, hexp₂]
      exact (extChartAt I x₀).right_inv htarget₂
    have hchart₁ :
        extChartAt I x₀ (expAt g x₀ p.2) = (α (z₀, v₁) s).1 := by
      have hexp₁ := hexp v₁ hv₁_norm_lt s hsτ
      have htarget₁ : (α (z₀, v₁) s).1 ∈ (extChartAt I x₀).target := by
        simpa [z₀] using (hα v₁ hv₁_norm_lt).2.2.2.1 s hsfull
      rw [← hscale₁, hexp₁]
      exact (extChartAt I x₀).right_inv htarget₁
    have hres_eq :
        extChartAt I x₀ (expAt g x₀ p.1) -
            extChartAt I x₀ (expAt g x₀ p.2) - (p.1 - p.2) =
          ((α (z₀, v₂) s).1 - (α (z₀, v₁) s).1) - s • (v₂ - v₁) := by
      rw [hchart₂, hchart₁]
      congr 1
      rw [← hscale₂, ← hscale₁, smul_sub]
    have hα_short :
        ∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ τ ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) τ))
                (Icc (-ε) ε) τ) ∧
            ∀ τ ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) τ ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) := by
      intro v hv
      exact ⟨(hα v hv).1, (hα v hv).2.1, (hα v hv).2.2.1⟩
    have hest :
        ‖((α (z₀, v₂) s).1 - (α (z₀, v₁) s).1) - s • (v₂ - v₁)‖ ≤
          (((K : ℝ) * Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖) * T) * ‖s‖ := by
      simpa [z₀] using
        chart_flow_position_pair_sub_linear_norm_le
          (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (T := T)
          (a := a) (K := K) (α := α) (v₁ := v₁) (v₂ := v₂)
          (t := s) hε hT_nonneg hTε hv₁_norm_lt hv₂_norm_lt hLip
          hα_short hsT
    have hdiff_eq : p.1 - p.2 = s • (v₂ - v₁) := by
      rw [← hscale₂, ← hscale₁, smul_sub]
    have hmul_nonneg : 0 ≤ ‖v₂ - v₁‖ * ‖s‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖extChartAt I x₀ (expAt g x₀ p.1) -
          extChartAt I x₀ (expAt g x₀ p.2) -
          ContinuousLinearMap.id ℝ E (p.1 - p.2)‖
          = ‖((α (z₀, v₂) s).1 - (α (z₀, v₁) s).1) - s • (v₂ - v₁)‖ := by
            rw [ContinuousLinearMap.id_apply, hres_eq]
      _ ≤ (((K : ℝ) * Real.exp ((K : ℝ) * ε) * ‖v₂ - v₁‖) * T) * ‖s‖ := hest
      _ = (C₀ * T) * (‖v₂ - v₁‖ * ‖s‖) := by
            ring
      _ ≤ c * (‖v₂ - v₁‖ * ‖s‖) := by
            exact mul_le_mul_of_nonneg_right hC₀T_le hmul_nonneg
      _ = c * ‖p.1 - p.2‖ := by
            rw [hdiff_eq, norm_smul]
            ring

/-- The inverse-function-theorem partial homeomorphism for the charted exponential. -/
def expAtChartOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    OpenPartialHomeomorph E E :=
  let f : E → E := fun v => extChartAt I x₀ (expAt g x₀ v)
  let hf : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (0 : E) := by
    simpa [f] using expAt_chart_hasStrictFDerivAt_zero (g := g) (x₀ := x₀)
  hf.toOpenPartialHomeomorph f

@[simp]
theorem expAtChartOpenPartialHomeomorph_coe
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    (expAtChartOpenPartialHomeomorph (g := g) x₀ : E → E) =
      fun v : E => extChartAt I x₀ (expAt g x₀ v) :=
  rfl

theorem zero_mem_expAtChartOpenPartialHomeomorph_source
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    (0 : E) ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source := by
  let f : E → E := fun v => extChartAt I x₀ (expAt g x₀ v)
  let hf : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (0 : E) := by
    simpa [f] using expAt_chart_hasStrictFDerivAt_zero (g := g) (x₀ := x₀)
  simpa [expAtChartOpenPartialHomeomorph, f] using hf.mem_toOpenPartialHomeomorph_source

theorem expAt_base_mem_expAtChartOpenPartialHomeomorph_target
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    extChartAt I x₀ x₀ ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).target := by
  let f : E → E := fun v => extChartAt I x₀ (expAt g x₀ v)
  let hf : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (0 : E) := by
    simpa [f] using expAt_chart_hasStrictFDerivAt_zero (g := g) (x₀ := x₀)
  simpa [expAtChartOpenPartialHomeomorph, f, expAt_zero] using
    hf.image_mem_toOpenPartialHomeomorph_target

theorem expAtChartOpenPartialHomeomorph_eventually_left_inverse
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∀ᶠ v in 𝓝 (0 : E),
      (expAtChartOpenPartialHomeomorph (g := g) x₀).symm
          (extChartAt I x₀ (expAt g x₀ v)) = v := by
  simpa using
    (expAtChartOpenPartialHomeomorph (g := g) x₀).eventually_left_inverse
      (zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀)

theorem expAtChartOpenPartialHomeomorph_eventually_right_inverse
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∀ᶠ y in 𝓝 (extChartAt I x₀ x₀),
      extChartAt I x₀
          (expAt g x₀ ((expAtChartOpenPartialHomeomorph (g := g) x₀).symm y)) = y := by
  have hright :=
    (expAtChartOpenPartialHomeomorph (g := g) x₀).eventually_right_inverse'
      (zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀)
  simpa [expAt_zero] using hright

theorem expAt_chart_map_nhds_zero_eq
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    map (fun v : E => extChartAt I x₀ (expAt g x₀ v)) (𝓝 (0 : E)) =
      𝓝 (extChartAt I x₀ x₀) := by
  let f : E → E := fun v => extChartAt I x₀ (expAt g x₀ v)
  let hf : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (0 : E) := by
    simpa [f] using expAt_chart_hasStrictFDerivAt_zero (g := g) (x₀ := x₀)
  simpa [f, expAt_zero] using hf.map_nhds_eq_of_equiv

theorem expAt_chart_image_ball_mem_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {r : ℝ} (hr : 0 < r) :
    (fun v : E => extChartAt I x₀ (expAt g x₀ v)) '' ball (0 : E) r ∈
      𝓝 (extChartAt I x₀ x₀) := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0 : (0 : E) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  simpa [e, expAt_zero] using e.image_mem_nhds h0 (Metric.ball_mem_nhds (0 : E) hr)

/--
The fixed-time exponential is injective on a small vector ball, and its image is
an open manifold neighborhood of the base point.
-/
theorem expAt_injective_open_image_smallBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ r > (0 : ℝ),
      InjOn (expAt g x₀) (ball (0 : E) r) ∧
        IsOpen (expAt g x₀ '' ball (0 : E) r) ∧
          expAt g x₀ '' ball (0 : E) r ∈ 𝓝 x₀ := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0 : (0 : E) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0) with
    ⟨re, hre_pos, hre_subset⟩
  rcases expAt_mem_source_of_norm_lt (g := g) (x₀ := x₀) with
    ⟨ρ, hρ_pos, hρ_source⟩
  let r : ℝ := min re ρ / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    exact half_pos (lt_min hre_pos hρ_pos)
  have hr_lt_re : r < re := by
    dsimp [r]
    have hmin_le : min re ρ ≤ re := min_le_left _ _
    linarith
  have hr_lt_ρ : r < ρ := by
    dsimp [r]
    have hmin_le : min re ρ ≤ ρ := min_le_right _ _
    linarith
  have hball_source : ball (0 : E) r ⊆ e.source := by
    intro v hv
    exact hre_subset (lt_trans hv hr_lt_re)
  have hExp_source : ∀ v ∈ ball (0 : E) r, expAt g x₀ v ∈ (extChartAt I x₀).source := by
    intro v hv
    have hvnorm : ‖v‖ < ρ := by
      have hvr : ‖v‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hv
      exact lt_trans hvr hr_lt_ρ
    exact hρ_source v hvnorm
  have hinj : InjOn (expAt g x₀) (ball (0 : E) r) := by
    intro v hv w hw hEq
    have hvsrc : v ∈ e.source := hball_source hv
    have hwsrc : w ∈ e.source := hball_source hw
    exact e.injOn hvsrc hwsrc (by
      change extChartAt I x₀ (expAt g x₀ v) = extChartAt I x₀ (expAt g x₀ w)
      rw [hEq])
  let U : Set E := (fun v : E => extChartAt I x₀ (expAt g x₀ v)) '' ball (0 : E) r
  have hchart_image_open : IsOpen U := by
    simpa [e] using
      e.isOpen_image_of_subset_source (isOpen_ball : IsOpen (ball (0 : E) r)) hball_source
  have hchart_image_subset_target : U ⊆ (extChartAt I x₀).target := by
    rintro y ⟨v, hv, rfl⟩
    exact (extChartAt I x₀).map_source (hExp_source v hv)
  have hpreimage_eq :
      (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' U =
        expAt g x₀ '' ball (0 : E) r := by
    ext y
    constructor
    · rintro ⟨hy_source, ⟨v, hv, hvy⟩⟩
      refine ⟨v, hv, ?_⟩
      calc
        expAt g x₀ v =
            (extChartAt I x₀).symm (extChartAt I x₀ (expAt g x₀ v)) := by
              exact ((extChartAt I x₀).left_inv (hExp_source v hv)).symm
        _ = (extChartAt I x₀).symm (extChartAt I x₀ y) := by
              change extChartAt I x₀ (expAt g x₀ v) = extChartAt I x₀ y at hvy
              rw [hvy]
        _ = y := (extChartAt I x₀).left_inv hy_source
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hExp_source v hv, ⟨v, hv, rfl⟩⟩
  have hsymm_image_eq :
      (extChartAt I x₀).symm '' U =
        expAt g x₀ '' ball (0 : E) r := by
    ext y
    constructor
    · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨v, hv, ?_⟩
      exact ((extChartAt I x₀).left_inv (hExp_source v hv)).symm
    · rintro ⟨v, hv, rfl⟩
      refine ⟨extChartAt I x₀ (expAt g x₀ v), ⟨v, hv, rfl⟩, ?_⟩
      exact (extChartAt I x₀).left_inv (hExp_source v hv)
  have hopen : IsOpen (expAt g x₀ '' ball (0 : E) r) := by
    rw [← hpreimage_eq]
    exact isOpen_extChartAt_preimage' x₀ hchart_image_open
  have hchart_image_nhds :
      U ∈ 𝓝 (extChartAt I x₀ x₀) := by
    simpa [U] using expAt_chart_image_ball_mem_nhds (g := g) (x₀ := x₀) hr_pos
  have hchart_image_within :
      U ∈ 𝓝[range I] (extChartAt I x₀ x₀) :=
    mem_nhdsWithin_of_mem_nhds hchart_image_nhds
  have hnhds : expAt g x₀ '' ball (0 : E) r ∈ 𝓝 x₀ := by
    have hsymm_mem : (extChartAt I x₀).symm '' U ∈ 𝓝 x₀ := by
      rw [← (@map_extChartAt_symm_nhdsWithin_range ℝ E M E _ _ _ _ _ I _ x₀)]
      exact Filter.image_mem_map hchart_image_within
    rw [← hsymm_image_eq]
    exact hsymm_mem
  refine ⟨r, hr_pos, ?_⟩
  exact ⟨hinj, hopen, hnhds⟩

end GeodesicTransport
end Poincare
