import Poincare.Global.ExponentialStrictAtV

/-!
# Shifted strict derivative closure for the charted exponential

This module contains the endpoint Gronwall propagation step for a shifted
base velocity.  The exported theorem is intentionally conditional on the
concrete PL flow and linearized endpoint family it consumes; the proof itself
derives the strict two-variable endpoint remainder from the shifted Taylor
estimate of `ExponentialStrictAtV`.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Shifted endpoint Gronwall propagation closes the strict derivative of the
charted fixed-time exponential.

The direction parameter for `Ψ` is the original exponential-coordinate
increment `w`; consequently the linearized initial velocity is `τ⁻¹ • w`.
This is the derivative of the endpoint representation
`p ↦ (α (z₀, τ⁻¹ • p) τ).1`.
-/
theorem expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {τ δ ε : ℝ} {a : ℝ≥0} {α : E × E → ℝ → E × E}
    {Ψ : E → ℝ → E × E} {v : E}
    (hτ : 0 < τ) (hε : 0 < ε) (hτε : τ ≤ ε)
    (hv : ‖τ⁻¹ • v‖ < δ)
    (hα : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) t))
            (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) t ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
        ∀ t ∈ Icc (-ε) ε,
          (α (extChartAt I x₀ x₀, v₀) t).1 ∈
            (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ →
      expAt g x₀ (τ • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) τ).1)
    (hΨ0 : ∀ w : E, Ψ w 0 = ((0 : E), τ⁻¹ • w))
    (hΨder : ∀ w : E, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, τ⁻¹ • v)) t (Ψ w t))
        (Icc (-ε) ε) t)
    (hadd : ∀ w w' : E,
      (Ψ (w + w') τ).1 = (Ψ w τ).1 + (Ψ w' τ).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) τ).1 = c • (Ψ w τ).1) :
    HasStrictFDerivAt
      (expAtChartOpenPartialHomeomorph (g := g) x₀)
      (linearizedEndpointCLM (Ψ := Ψ) τ hadd hsmul) v := by
  let z₀ : E := extChartAt I x₀ x₀
  let p₀ : E × E := (z₀, (0 : E))
  let u₀ : E := τ⁻¹ • v
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : E × E → E × E := geodesicFlowField Γ
  let D : E →L[ℝ] E := linearizedEndpointCLM (Ψ := Ψ) τ hadd hsmul
  have hτ_nonneg : 0 ≤ τ := hτ.le
  have hτinv_pos : 0 < τ⁻¹ := inv_pos.mpr hτ
  have hτfull : τ ∈ Icc (-ε) ε := ⟨by linarith, hτε⟩
  have hτpos : τ ∈ Icc (0 : ℝ) ε := ⟨hτ.le, hτε⟩
  have hu₀ : ‖u₀‖ < δ := by simpa [u₀] using hv
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  rcases geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      (g := g) (x₀ := x₀) (p := p₀) (a := (a : ℝ) + 1) with
    ⟨K, hLipF⟩
  let Cflow : ℝ := Real.exp ((K : ℝ) * ε)
  let Cdiff : ℝ := Cflow * τ⁻¹
  have hCflow_nonneg : 0 ≤ Cflow := by
    dsimp [Cflow]
    positivity
  have hCdiff_nonneg : 0 ≤ Cdiff := by
    dsimp [Cdiff]
    positivity
  let Cgr : ℝ := gronwallBound 0 (K : ℝ) 1 τ
  have hCgr_nonneg : 0 ≤ Cgr := by
    have hmono : Monotone (gronwallBound 0 (K : ℝ) 1) :=
      gronwallBound_mono (by norm_num) (by norm_num) K.2
    have h0τ := hmono hτ_nonneg
    simpa [Cgr, gronwallBound_x0] using h0τ
  let η : ℝ := c / (Cgr + 1)
  have hden_gr_pos : 0 < Cgr + 1 := by positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hηC_le : η * Cgr ≤ c := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_gr_pos]
    nlinarith [hc.le, hCgr_nonneg]
  let θ : ℝ := η / (Cdiff + 1)
  have hden_diff_pos : 0 < Cdiff + 1 := by positivity
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθC_le : θ * Cdiff ≤ η := by
    dsimp [θ]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_diff_pos]
    nlinarith [hη_pos.le, hCdiff_nonneg]
  rcases
      chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
        (g := g) (x₀ := x₀) p₀ ((a : ℝ) + 1) θ hθ_pos with
    ⟨ρ, hρ_pos, hTaylor⟩
  let margin : ℝ := δ - ‖u₀‖
  have hmargin_pos : 0 < margin := sub_pos.mpr hu₀
  let Rvel : ℝ := τ * margin / 2
  have hRvel_pos : 0 < Rvel := by
    dsimp [Rvel]
    positivity
  let Rclose : ℝ := ρ / (Cdiff + 1)
  have hRclose_pos : 0 < Rclose := by
    dsimp [Rclose]
    positivity
  let R : ℝ := min Rvel Rclose
  have hR_pos : 0 < R := by
    dsimp [R]
    exact lt_min hRvel_pos hRclose_pos
  have hR_le_vel : R ≤ Rvel := by
    dsimp [R]
    exact min_le_left _ _
  have hR_le_close : R ≤ Rclose := by
    dsimp [R]
    exact min_le_right _ _
  have hball :
      ball ((v, v) : E × E) R ∈ 𝓝 ((v, v) : E × E) :=
    Metric.ball_mem_nhds _ hR_pos
  filter_upwards [hball] with p hp
  have hp_prod : p ∈ ball v R ×ˢ ball v R := by
    simpa [ball_prod_same] using hp
  have hp₁_norm_lt : ‖p.1 - v‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp_prod.1
  have hp₂_norm_lt : ‖p.2 - v‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp_prod.2
  let u₁ : E := τ⁻¹ • p.1
  let u₂ : E := τ⁻¹ • p.2
  let d : E := p.1 - p.2
  have hscale_sub₁ : u₁ - u₀ = τ⁻¹ • (p.1 - v) := by
    simp [u₁, u₀, smul_sub]
  have hscale_sub₂ : u₂ - u₀ = τ⁻¹ • (p.2 - v) := by
    simp [u₂, u₀, smul_sub]
  have hscale_sub₁₂ : u₁ - u₂ = τ⁻¹ • d := by
    simp [u₁, u₂, d, smul_sub]
  have hp₁_vel_margin : τ⁻¹ * ‖p.1 - v‖ < margin := by
    have hlt : ‖p.1 - v‖ < Rvel := lt_of_lt_of_le hp₁_norm_lt hR_le_vel
    have hlt' : τ⁻¹ * ‖p.1 - v‖ < τ⁻¹ * Rvel :=
      mul_lt_mul_of_pos_left hlt hτinv_pos
    have hτR : τ⁻¹ * Rvel = margin / 2 := by
      dsimp [Rvel]
      field_simp [ne_of_gt hτ]
    nlinarith [hmargin_pos, hlt']
  have hp₂_vel_margin : τ⁻¹ * ‖p.2 - v‖ < margin := by
    have hlt : ‖p.2 - v‖ < Rvel := lt_of_lt_of_le hp₂_norm_lt hR_le_vel
    have hlt' : τ⁻¹ * ‖p.2 - v‖ < τ⁻¹ * Rvel :=
      mul_lt_mul_of_pos_left hlt hτinv_pos
    have hτR : τ⁻¹ * Rvel = margin / 2 := by
      dsimp [Rvel]
      field_simp [ne_of_gt hτ]
    nlinarith [hmargin_pos, hlt']
  have hu₁ : ‖u₁‖ < δ := by
    have hnorm_sub : ‖u₁ - u₀‖ = τ⁻¹ * ‖p.1 - v‖ := by
      rw [hscale_sub₁, norm_smul, Real.norm_eq_abs, abs_of_pos hτinv_pos]
    have hlt : ‖u₀‖ + τ⁻¹ * ‖p.1 - v‖ < ‖u₀‖ + margin := by
      linarith
    calc
      ‖u₁‖ = ‖u₀ + (u₁ - u₀)‖ := by
        rw [add_sub_cancel]
      _ ≤ ‖u₀‖ + ‖u₁ - u₀‖ := norm_add_le _ _
      _ = ‖u₀‖ + τ⁻¹ * ‖p.1 - v‖ := by rw [hnorm_sub]
      _ < ‖u₀‖ + margin := hlt
      _ = δ := by
        dsimp [margin]
        ring
  have hu₂ : ‖u₂‖ < δ := by
    have hnorm_sub : ‖u₂ - u₀‖ = τ⁻¹ * ‖p.2 - v‖ := by
      rw [hscale_sub₂, norm_smul, Real.norm_eq_abs, abs_of_pos hτinv_pos]
    have hlt : ‖u₀‖ + τ⁻¹ * ‖p.2 - v‖ < ‖u₀‖ + margin := by
      linarith
    calc
      ‖u₂‖ = ‖u₀ + (u₂ - u₀)‖ := by
        rw [add_sub_cancel]
      _ ≤ ‖u₀‖ + ‖u₂ - u₀‖ := norm_add_le _ _
      _ = ‖u₀‖ + τ⁻¹ * ‖p.2 - v‖ := by rw [hnorm_sub]
      _ < ‖u₀‖ + margin := hlt
      _ = δ := by
        dsimp [margin]
        ring
  have hα₀ := hα u₀ hu₀
  have hα₁ := hα u₁ hu₁
  have hα₂ := hα u₂ hu₂
  have hchart₁ :
      extChartAt I x₀ (expAt g x₀ p.1) =
        (α (z₀, u₁) τ).1 := by
    have hscale : τ • u₁ = p.1 := by
      dsimp [u₁]
      rw [smul_smul]
      have hcoef : τ * τ⁻¹ = 1 := by field_simp [ne_of_gt hτ]
      simp [hcoef]
    have he := hexp u₁ hu₁
    rw [hscale] at he
    rw [he]
    exact (extChartAt I x₀).right_inv (by
      simpa [z₀, u₁] using hα₁.2.2.2 τ hτfull)
  have hchart₂ :
      extChartAt I x₀ (expAt g x₀ p.2) =
        (α (z₀, u₂) τ).1 := by
    have hscale : τ • u₂ = p.2 := by
      dsimp [u₂]
      rw [smul_smul]
      have hcoef : τ * τ⁻¹ = 1 := by field_simp [ne_of_gt hτ]
      simp [hcoef]
    have he := hexp u₂ hu₂
    rw [hscale] at he
    rw [he]
    exact (extChartAt I x₀).right_inv (by
      simpa [z₀, u₂] using hα₂.2.2.2 τ hτfull)
  let γ₀ : ℝ → E × E := α (z₀, u₀)
  let γ₁ : ℝ → E × E := α (z₀, u₁)
  let γ₂ : ℝ → E × E := α (z₀, u₂)
  let Rfun : ℝ → E × E := fun t => γ₁ t - γ₂ t - Ψ d t
  let Rder : ℝ → E × E := fun t =>
    F (γ₁ t) - F (γ₂ t) -
      linearizedGeodesicFlowOperator Γ (γ₀ t) (Ψ d t)
  have hIcc_subset : Icc (0 : ℝ) τ ⊆ Icc (-ε) ε := by
    intro t ht
    exact ⟨by linarith [hε, ht.1], ht.2.trans hτε⟩
  have hIco_subset : Ico (0 : ℝ) τ ⊆ Icc (-ε) ε := by
    intro t ht
    exact hIcc_subset (Ico_subset_Icc_self ht)
  have hRcont : ContinuousOn Rfun (Icc (0 : ℝ) τ) := by
    have hγ₁cont : ContinuousOn γ₁ (Icc (0 : ℝ) τ) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun t => F (γ₁ t)) ?_
      intro t ht
      simpa [γ₁, F, Γ, z₀] using (hα₁.2.1 t (hIcc_subset ht)).mono hIcc_subset
    have hγ₂cont : ContinuousOn γ₂ (Icc (0 : ℝ) τ) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun t => F (γ₂ t)) ?_
      intro t ht
      simpa [γ₂, F, Γ, z₀] using (hα₂.2.1 t (hIcc_subset ht)).mono hIcc_subset
    have hΨcont : ContinuousOn (Ψ d) (Icc (0 : ℝ) τ) := by
      refine HasDerivWithinAt.continuousOn
        (f' := fun t =>
          linearizedGeodesicFlowFieldAlong Γ γ₀ t (Ψ d t)) ?_
      intro t ht
      simpa [γ₀, Γ, z₀, u₀] using
        (hΨder d t (hIcc_subset ht)).mono hIcc_subset
    simpa [Rfun] using (hγ₁cont.sub hγ₂cont).sub hΨcont
  have hRderiv : ∀ t ∈ Ico (0 : ℝ) τ,
      HasDerivWithinAt Rfun (Rder t) (Ici t) t := by
    intro t ht
    have htfull : t ∈ Icc (-ε) ε := hIco_subset ht
    have ht_lt_ε : t < ε := lt_of_lt_of_le ht.2 hτε
    have hnhds : Icc (-ε) ε ∈ 𝓝[Ici t] t :=
      Icc_mem_nhdsGE_of_mem ⟨htfull.1, ht_lt_ε⟩
    have hγ₁der :
        HasDerivWithinAt γ₁ (F (γ₁ t)) (Ici t) t := by
      simpa [γ₁, F, Γ, z₀] using
        (hα₁.2.1 t htfull).mono_of_mem_nhdsWithin hnhds
    have hγ₂der :
        HasDerivWithinAt γ₂ (F (γ₂ t)) (Ici t) t := by
      simpa [γ₂, F, Γ, z₀] using
        (hα₂.2.1 t htfull).mono_of_mem_nhdsWithin hnhds
    have hΨder' :
        HasDerivWithinAt (Ψ d)
          (linearizedGeodesicFlowOperator Γ (γ₀ t) (Ψ d t)) (Ici t) t := by
      simpa [linearizedGeodesicFlowFieldAlong, γ₀, Γ, z₀, u₀] using
        (hΨder d t htfull).mono_of_mem_nhdsWithin hnhds
    simpa [Rfun, Rder] using (hγ₁der.sub hγ₂der).sub hΨder'
  have hR0 : Rfun 0 = 0 := by
    have hγ₁0 : γ₁ 0 = (z₀, u₁) := by simpa [γ₁, z₀, u₁] using hα₁.1
    have hγ₂0 : γ₂ 0 = (z₀, u₂) := by simpa [γ₂, z₀, u₂] using hα₂.1
    have hΨd0 : Ψ d 0 = ((0 : E), τ⁻¹ • d) := hΨ0 d
    ext <;> simp [Rfun, hγ₁0, hγ₂0, hΨd0, hscale_sub₁₂]
  have hbound : ∀ t ∈ Ico (0 : ℝ) τ,
      ‖Rder t‖ ≤ (K : ℝ) * ‖Rfun t‖ + η * ‖d‖ := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) τ := Ico_subset_Icc_self ht
    have htfull : t ∈ Icc (-ε) ε := hIco_subset ht
    let base : E × E := γ₀ t
    let q : E × E := γ₁ t
    let y : E × E := γ₂ t
    have hbase_mem_small : base ∈ closedBall p₀ (a : ℝ) := by
      simpa [base, γ₀, p₀, z₀, u₀] using hα₀.2.2.1 t htfull
    have hq_mem_small : q ∈ closedBall p₀ (a : ℝ) := by
      simpa [q, γ₁, p₀, z₀, u₁] using hα₁.2.2.1 t htfull
    have hy_mem_small : y ∈ closedBall p₀ (a : ℝ) := by
      simpa [y, γ₂, p₀, z₀, u₂] using hα₂.2.2.1 t htfull
    have hbase_mem : base ∈ closedBall p₀ ((a : ℝ) + 1) :=
      closedBall_subset_closedBall (by linarith [NNReal.coe_nonneg a]) hbase_mem_small
    have hq_mem : q ∈ closedBall p₀ ((a : ℝ) + 1) :=
      closedBall_subset_closedBall (by linarith [NNReal.coe_nonneg a]) hq_mem_small
    have hy_mem : y ∈ closedBall p₀ ((a : ℝ) + 1) :=
      closedBall_subset_closedBall (by linarith [NNReal.coe_nonneg a]) hy_mem_small
    have hstate_lip :
        LipschitzOnWith
          ⟨Cflow, by simpa [Cflow] using hCflow_nonneg⟩
          (fun u : E => α (z₀, u) t)
          (ball (0 : E) δ) := by
      simpa [Cflow, z₀, Γ, F] using
        chart_flow_initialVelocity_lipschitzOn_of_ODE
          (g := g) (x₀ := x₀) (δ := δ) (ε := ε)
          (a := (a : ℝ) + 1) (K := K) (α := α)
          hε hLipF
          (fun u hu => (hα u hu).1)
          (fun u hu r hr => (hα u hu).2.1 r hr)
          (fun u hu r hr =>
            closedBall_subset_closedBall
              (by linarith [NNReal.coe_nonneg a]) ((hα u hu).2.2.1 r hr))
          ⟨htIcc.1, htIcc.2.trans hτε⟩
    have hu₀ball : u₀ ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu₀
    have hu₁ball : u₁ ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu₁
    have hu₂ball : u₂ ∈ ball (0 : E) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu₂
    have hq_base_dist := hstate_lip.dist_le_mul u₁ hu₁ball u₀ hu₀ball
    have hy_base_dist := hstate_lip.dist_le_mul u₂ hu₂ball u₀ hu₀ball
    have hq_base_le : ‖q - base‖ ≤ Cdiff * ‖p.1 - v‖ := by
      calc
        ‖q - base‖ = dist q base := by rw [dist_eq_norm]
        _ ≤ Cflow * dist u₁ u₀ := by
          simpa [q, base, γ₁, γ₀, z₀] using hq_base_dist
        _ = Cflow * ‖u₁ - u₀‖ := by rw [dist_eq_norm]
        _ = Cdiff * ‖p.1 - v‖ := by
          rw [hscale_sub₁, norm_smul, Real.norm_eq_abs, abs_of_pos hτinv_pos]
          ring
    have hy_base_le : ‖y - base‖ ≤ Cdiff * ‖p.2 - v‖ := by
      calc
        ‖y - base‖ = dist y base := by rw [dist_eq_norm]
        _ ≤ Cflow * dist u₂ u₀ := by
          simpa [y, base, γ₂, γ₀, z₀] using hy_base_dist
        _ = Cflow * ‖u₂ - u₀‖ := by rw [dist_eq_norm]
        _ = Cdiff * ‖p.2 - v‖ := by
          rw [hscale_sub₂, norm_smul, Real.norm_eq_abs, abs_of_pos hτinv_pos]
          ring
    have hclose_from_lt {xnorm : ℝ} (hx : xnorm < R) :
        Cdiff * xnorm ≤ ρ := by
      have hxR : xnorm ≤ R := le_of_lt hx
      calc
        Cdiff * xnorm ≤ Cdiff * R :=
          mul_le_mul_of_nonneg_left hxR hCdiff_nonneg
        _ ≤ Cdiff * Rclose :=
          mul_le_mul_of_nonneg_left hR_le_close hCdiff_nonneg
        _ ≤ (Cdiff + 1) * Rclose := by
          exact mul_le_mul_of_nonneg_right (by linarith) hRclose_pos.le
        _ = ρ := by
          dsimp [Rclose]
          field_simp [ne_of_gt hden_diff_pos]
    have hq_close : ‖q - base‖ ≤ ρ :=
      hq_base_le.trans (hclose_from_lt hp₁_norm_lt)
    have hy_close : ‖y - base‖ ≤ ρ :=
      hy_base_le.trans (hclose_from_lt hp₂_norm_lt)
    have hq_y_dist := hstate_lip.dist_le_mul u₁ hu₁ball u₂ hu₂ball
    have hq_y_le : ‖q - y‖ ≤ Cdiff * ‖d‖ := by
      calc
        ‖q - y‖ = dist q y := by rw [dist_eq_norm]
        _ ≤ Cflow * dist u₁ u₂ := by
          simpa [q, y, γ₁, γ₂, z₀] using hq_y_dist
        _ = Cflow * ‖u₁ - u₂‖ := by rw [dist_eq_norm]
        _ = Cdiff * ‖d‖ := by
          rw [hscale_sub₁₂, norm_smul, Real.norm_eq_abs, abs_of_pos hτinv_pos]
          ring
    have hremθ :
        ‖F q - F y -
            linearizedGeodesicFlowOperator Γ base (q - y)‖ ≤
          θ * ‖q - y‖ := by
      simpa [F, Γ] using
        hTaylor base hbase_mem y hy_mem q hq_mem hy_close hq_close
    have hremη :
        ‖F q - F y -
            linearizedGeodesicFlowOperator Γ base (q - y)‖ ≤
          η * ‖d‖ := by
      calc
        ‖F q - F y -
            linearizedGeodesicFlowOperator Γ base (q - y)‖
            ≤ θ * ‖q - y‖ := hremθ
        _ ≤ θ * (Cdiff * ‖d‖) :=
          mul_le_mul_of_nonneg_left hq_y_le hθ_pos.le
        _ = (θ * Cdiff) * ‖d‖ := by ring
        _ ≤ η * ‖d‖ :=
          mul_le_mul_of_nonneg_right hθC_le (norm_nonneg d)
    have hbase_nhds :
        closedBall p₀ ((a : ℝ) + 1) ∈ 𝓝 base :=
      closedBall_radius_add_one_mem_nhds hbase_mem_small
    have hAnorm :
        ‖linearizedGeodesicFlowOperator Γ base‖ ≤ (K : ℝ) := by
      have hfd :
          ‖fderiv ℝ F base‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hbase_nhds hLipF
      simpa [linearizedGeodesicFlowOperator, F, Γ] using hfd
    have hlinear :
        ‖linearizedGeodesicFlowOperator Γ base
            (q - y - (1 : ℝ) • Ψ d t)‖ ≤
          (K : ℝ) * ‖q - y - (1 : ℝ) • Ψ d t‖ := by
      calc
        ‖linearizedGeodesicFlowOperator Γ base
            (q - y - (1 : ℝ) • Ψ d t)‖
            ≤ ‖linearizedGeodesicFlowOperator Γ base‖ *
                ‖q - y - (1 : ℝ) • Ψ d t‖ :=
          ContinuousLinearMap.le_opNorm
            (linearizedGeodesicFlowOperator Γ base)
            (q - y - (1 : ℝ) • Ψ d t)
        _ ≤ (K : ℝ) * ‖q - y - (1 : ℝ) • Ψ d t‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hraw :
        ‖Rder t‖ ≤
          (K : ℝ) * ‖q - y - (1 : ℝ) • Ψ d t‖ +
            (η * ‖d‖) * ‖(1 : ℝ)‖ :=
      residual_derivative_norm_bound_of_taylor_remainder
        (F := F) (A := linearizedGeodesicFlowOperator Γ base)
        (q := q) (γ := y) (ψ := Ψ d t) (R' := Rder t)
        (K := (K : ℝ)) (η := η * ‖d‖) (s := (1 : ℝ))
        (by
          simp [Rder, F, Γ, q, y, base])
        hlinear
        (by simpa using hremη)
    simpa [Rfun, Rder, q, y, base] using hraw
  have hgr :
      ‖Rfun τ‖ ≤ gronwallBound 0 (K : ℝ) (η * ‖d‖) τ :=
    gronwall_residual_norm_le
      (R := Rfun) (R' := Rder) (K := (K : ℝ)) (η := η * ‖d‖)
      hRcont hRderiv hR0 hbound ⟨hτ_nonneg, le_rfl⟩
  have hR_bound : ‖Rfun τ‖ ≤ c * ‖d‖ := by
    calc
      ‖Rfun τ‖ ≤ gronwallBound 0 (K : ℝ) (η * ‖d‖) τ := hgr
      _ = (η * ‖d‖) * Cgr := by
        rw [gronwallBound_zero_left_mul]
      _ = (η * Cgr) * ‖d‖ := by ring
      _ ≤ c * ‖d‖ :=
        mul_le_mul_of_nonneg_right hηC_le (norm_nonneg d)
  have hfst :
      (Rfun τ).1 =
        extChartAt I x₀ (expAt g x₀ p.1) -
          extChartAt I x₀ (expAt g x₀ p.2) - D (p.1 - p.2) := by
    have hD_apply : D (p.1 - p.2) = (Ψ d τ).1 := by
      simp [D, d,
        (linearizedEndpointCLM_apply (Ψ := Ψ) τ hadd hsmul d)
      ]
    calc
      (Rfun τ).1 = (α (z₀, u₁) τ).1 - (α (z₀, u₂) τ).1 - (Ψ d τ).1 := by
        simp [Rfun, γ₁, γ₂]
      _ = extChartAt I x₀ (expAt g x₀ p.1) -
          extChartAt I x₀ (expAt g x₀ p.2) - D (p.1 - p.2) := by
        rw [← hchart₁, ← hchart₂, ← hD_apply]
  calc
    ‖(expAtChartOpenPartialHomeomorph (g := g) x₀) p.1 -
        (expAtChartOpenPartialHomeomorph (g := g) x₀) p.2 -
        linearizedEndpointCLM (Ψ := Ψ) τ hadd hsmul (p.1 - p.2)‖
        = ‖(Rfun τ).1‖ := by
          rw [hfst]
          rfl
    _ ≤ ‖Rfun τ‖ := norm_fst_le _
    _ ≤ c * ‖p.1 - p.2‖ := by
          simpa [d] using hR_bound

end GeodesicTransport
end Poincare
