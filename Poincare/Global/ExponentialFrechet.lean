import Poincare.Global.ExponentialDerivativeZero

/-!
# Fréchet derivative of the fixed-time exponential at zero

This module closes the velocity-variable remainder left by
`Poincare.Global.ExponentialDerivativeZero`.

The proof uses the closed-interval PL-flow spelling exported by
`expAt_uniform_pl_flow_eq_on_Icc`.  A compact acceleration bound gives a
uniform short-time estimate
`z(t) - (z₀ + t • v) = O(T * t)` for all initial velocities in a fixed small
ball and all `t ≤ T`.  Writing a small velocity as `w = t • v` with `‖v‖`
fixed turns this into the little-o remainder in the velocity variable required
by `expAt_chart_hasFDerivAt_zero_of_remainder`.
-/

noncomputable section

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
For a first-order geodesic-flow solution with uniformly bounded acceleration
on `[0,T]`, the velocity changes by at most `B * ‖t‖`.
-/
theorem flow_velocity_sub_initial_norm_le_of_accel_bound
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {α : E × E → ℝ → E × E} {z₀ v : E}
    {ε T B t : ℝ}
    (hε : 0 < ε) (hT_nonneg : 0 ≤ T) (hTε : T ≤ ε)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hαder : ∀ r ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (z₀, v))
        (geodesicFlowField Γ (α (z₀, v) r)) (Icc (-ε) ε) r)
    (hacc_bound : ∀ r ∈ Icc (0 : ℝ) T,
      ‖(geodesicFlowField Γ (α (z₀, v) r)).2‖ ≤ B)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖(α (z₀, v) t).2 - v‖ ≤ B * ‖t‖ := by
  have hsubset : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro r hr
    exact ⟨by linarith [hε, hr.1], le_trans hr.2 hTε⟩
  have hvel_der : ∀ r ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (fun q : ℝ => (α (z₀, v) q).2)
        (geodesicFlowField Γ (α (z₀, v) r)).2
        (Icc (0 : ℝ) T) r := by
    intro r hr
    have hstate := (hαder r (hsubset hr)).mono hsubset
    have hsnd := hstate.hasFDerivWithinAt.snd.hasDerivWithinAt
    simpa [geodesicFlowField] using hsnd
  have hmvt :
      ‖(α (z₀, v) t).2 - (α (z₀, v) 0).2‖ ≤ B * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun q : ℝ => (α (z₀, v) q).2)
      (f' := fun q : ℝ => (geodesicFlowField Γ (α (z₀, v) q)).2)
      (s := Icc (0 : ℝ) T) (x := 0) (y := t)
      hvel_der hacc_bound (convex_Icc (0 : ℝ) T)
      (left_mem_Icc.mpr hT_nonneg) ht
  simpa [hα0] using hmvt

/--
Uniform short-time position remainder for a chart first-order geodesic flow.

The constant `T` in the right-hand side is the common time horizon; this is the
spelling used below to make the eventual `o(‖w‖)` estimate by shrinking `T`.
-/
theorem flow_position_sub_linear_norm_le_of_accel_bound
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {α : E × E → ℝ → E × E} {z₀ v : E}
    {ε T B t : ℝ}
    (hε : 0 < ε) (hT_nonneg : 0 ≤ T) (hTε : T ≤ ε)
    (hα0 : α (z₀, v) 0 = (z₀, v))
    (hαder : ∀ r ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (z₀, v))
        (geodesicFlowField Γ (α (z₀, v) r)) (Icc (-ε) ε) r)
    (hacc_bound : ∀ r ∈ Icc (0 : ℝ) T,
      ‖(geodesicFlowField Γ (α (z₀, v) r)).2‖ ≤ B)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖(α (z₀, v) t).1 - (z₀ + t • v)‖ ≤ (B * T) * ‖t‖ := by
  have hsubset : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro r hr
    exact ⟨by linarith [hε, hr.1], le_trans hr.2 hTε⟩
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T :=
    left_mem_Icc.mpr hT_nonneg
  have hB_nonneg : 0 ≤ B :=
    (norm_nonneg _).trans (hacc_bound 0 h0mem)
  have hvel_bound : ∀ r ∈ Icc (0 : ℝ) T,
      ‖(α (z₀, v) r).2 - v‖ ≤ B * ‖r‖ := by
    intro r hr
    exact flow_velocity_sub_initial_norm_le_of_accel_bound
      (Γ := Γ) (α := α) (z₀ := z₀) (v := v)
      (ε := ε) (T := T) (B := B) hε hT_nonneg hTε
      hα0 hαder hacc_bound hr
  have hvel_bound_T : ∀ r ∈ Icc (0 : ℝ) T,
      ‖(α (z₀, v) r).2 - v‖ ≤ B * T := by
    intro r hr
    have hrnorm : ‖r‖ ≤ T := by
      rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact hr.2
    exact (hvel_bound r hr).trans
      (mul_le_mul_of_nonneg_left hrnorm hB_nonneg)
  have hpos_der : ∀ r ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt
        (fun q : ℝ => (α (z₀, v) q).1 - (z₀ + q • v))
        ((α (z₀, v) r).2 - v)
        (Icc (0 : ℝ) T) r := by
    intro r hr
    have hstate := (hαder r (hsubset hr)).mono hsubset
    have hfst : HasDerivWithinAt
        (fun q : ℝ => (α (z₀, v) q).1)
        (α (z₀, v) r).2 (Icc (0 : ℝ) T) r := by
      have hfst_raw := hstate.hasFDerivWithinAt.fst.hasDerivWithinAt
      simpa [geodesicFlowField] using hfst_raw
    have hlin : HasDerivWithinAt
        (fun q : ℝ => z₀ + q • v) v (Icc (0 : ℝ) T) r := by
      simpa using (((hasDerivAt_id r).smul_const v).const_add z₀).hasDerivWithinAt
    exact hfst.sub hlin
  have hmvt :
      ‖((α (z₀, v) t).1 - (z₀ + t • v)) -
          ((α (z₀, v) 0).1 - (z₀ + (0 : ℝ) • v))‖ ≤
        (B * T) * ‖t - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun q : ℝ => (α (z₀, v) q).1 - (z₀ + q • v))
      (f' := fun q : ℝ => (α (z₀, v) q).2 - v)
      (s := Icc (0 : ℝ) T) (x := 0) (y := t)
      hpos_der hvel_bound_T (convex_Icc (0 : ℝ) T)
      h0mem ht
  simpa [hα0] using hmvt

namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
The uniform velocity-variable little-o remainder required by
`expAt_chart_hasFDerivAt_zero_of_remainder`.

Spelling note: the criterion from `ExponentialDerivativeZero` asks for the
residual against `extChartAt I x₀ x₀ + v`.  The proof below rewrites a small
velocity as `v = t • u` with `‖u‖ = δ / 2`, uses the closed-interval PL-flow
identity for `expAt (t • u)`, and applies the compact uniform short-time
position estimate above.
-/
theorem expAt_chart_remainder_isLittleO_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    (fun v : E =>
      extChartAt I x₀ (expAt g x₀ v) - (extChartAt I x₀ x₀ + v))
        =o[𝓝 (0 : E)] (fun v : E => v) := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, hexp⟩
  let z₀ : E := extChartAt I x₀ x₀
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : E × E → E × E := geodesicFlowField Γ
  have hF_cont : Continuous (fun p : E × E => (F p).2) := by
    exact continuous_snd.comp
      ((geodesicFlowField_chartChristoffelField_contDiff
        (g := g) (x₀ := x₀)).continuous)
  rcases (isCompact_closedBall (z₀, (0 : E)) (a : ℝ)).exists_bound_of_continuousOn
      hF_cont.continuousOn with
    ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  have hacc_bound_closed : ∀ p ∈ closedBall (z₀, (0 : E)) (a : ℝ),
      ‖(F p).2‖ ≤ B := by
    intro p hp
    exact (hB₀ p hp).trans (le_max_left B₀ 0)
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_ltδ : R < δ := by
    dsimp [R]
    linarith
  rw [isLittleO_iff]
  intro c hc
  let T : ℝ := min τ (min ε (c * R / (B + 1)))
  have hB1_pos : 0 < B + 1 := by linarith
  have hT_pos : 0 < T := by
    dsimp [T]
    exact lt_min hτ (lt_min hε (div_pos (mul_pos hc hR_pos) hB1_pos))
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hTτ : T ≤ τ := by
    dsimp [T]
    exact min_le_left _ _
  have hTε : T ≤ ε := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hTcR : B * T ≤ c * R := by
    have hTsmall : T ≤ c * R / (B + 1) := by
      dsimp [T]
      exact (min_le_right _ _).trans (min_le_right _ _)
    calc
      B * T ≤ (B + 1) * T := by
        exact mul_le_mul_of_nonneg_right (by linarith) hT_nonneg
      _ ≤ (B + 1) * (c * R / (B + 1)) := by
        exact mul_le_mul_of_nonneg_left hTsmall hB1_pos.le
      _ = c * R := by
        field_simp [ne_of_gt hB1_pos]
  have hball :
      ball (0 : E) (R * T) ∈ 𝓝 (0 : E) :=
    Metric.ball_mem_nhds _ (mul_pos hR_pos hT_pos)
  filter_upwards [hball] with w hw
  by_cases hw0 : w = 0
  · simp [hw0, expAt_zero]
  · have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    let t : ℝ := ‖w‖ / R
    let v₀ : E := (R / ‖w‖) • w
    have hw_norm_lt : ‖w‖ < R * T := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have ht_pos : 0 < t := by
      dsimp [t]
      exact div_pos hw_norm_pos hR_pos
    have htT_lt : t < T := by
      dsimp [t]
      rw [div_lt_iff₀ hR_pos]
      linarith
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht_pos.le, le_of_lt htT_lt⟩
    have htτ : t ∈ Icc (0 : ℝ) τ := ⟨ht_pos.le, htT.2.trans hTτ⟩
    have htfull : t ∈ Icc (-ε) ε := ⟨by linarith [hε, ht_pos], htT.2.trans hTε⟩
    have hv_norm_eq : ‖v₀‖ = R := by
      dsimp [v₀]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hR_pos hw_norm_pos)]
      field_simp [ne_of_gt hw_norm_pos]
    have hv_norm_lt : ‖v₀‖ < δ := by
      rw [hv_norm_eq]
      exact hR_ltδ
    have htv : t • v₀ = w := by
      dsimp [t, v₀]
      rw [smul_smul]
      have hcoef : (‖w‖ / R) * (R / ‖w‖) = 1 := by
        field_simp [ne_of_gt hR_pos, ne_of_gt hw_norm_pos]
      simp [hcoef]
    rcases hα v₀ hv_norm_lt with
      ⟨hα0, hαder, hαmem, hαtarget, _hhom⟩
    have hacc_bound : ∀ r ∈ Icc (0 : ℝ) T,
        ‖(geodesicFlowField Γ (α (z₀, v₀) r)).2‖ ≤ B := by
      intro r hr
      have hrfull : r ∈ Icc (-ε) ε :=
        ⟨by linarith [hε, hr.1], hr.2.trans hTε⟩
      have hmem : α (z₀, v₀) r ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
        simpa [z₀] using hαmem r hrfull
      simpa [F, Γ] using hacc_bound_closed (α (z₀, v₀) r) hmem
    have hpos_bound :
        ‖(α (z₀, v₀) t).1 - (z₀ + t • v₀)‖ ≤ (B * T) * ‖t‖ :=
      flow_position_sub_linear_norm_le_of_accel_bound
        (Γ := Γ) (α := α) (z₀ := z₀) (v := v₀)
        (ε := ε) (T := T) (B := B) hε hT_nonneg hTε
        hα0 hαder hacc_bound htT
    have hexp_w :
        expAt g x₀ w =
          (extChartAt I x₀).symm (α (z₀, v₀) t).1 := by
      simpa [z₀, htv] using hexp v₀ hv_norm_lt t htτ
    have htarget : (α (z₀, v₀) t).1 ∈ (extChartAt I x₀).target := by
      simpa [z₀] using hαtarget t htfull
    have hchart :
        extChartAt I x₀ (expAt g x₀ w) = (α (z₀, v₀) t).1 := by
      rw [hexp_w]
      exact (extChartAt I x₀).right_inv htarget
    have hres :
        extChartAt I x₀ (expAt g x₀ w) - (z₀ + w) =
          (α (z₀, v₀) t).1 - (z₀ + t • v₀) := by
      rw [hchart, htv]
    have ht_norm : ‖t‖ = t := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
    have hw_norm_eq : ‖w‖ = R * t := by
      dsimp [t]
      field_simp [ne_of_gt hR_pos]
    calc
      ‖extChartAt I x₀ (expAt g x₀ w) - (extChartAt I x₀ x₀ + w)‖
          = ‖(α (z₀, v₀) t).1 - (z₀ + t • v₀)‖ := by
            rw [show extChartAt I x₀ x₀ = z₀ from rfl, hres]
      _ ≤ (B * T) * ‖t‖ := hpos_bound
      _ = (B * T) * t := by rw [ht_norm]
      _ ≤ (c * R) * t := by
        exact mul_le_mul_of_nonneg_right hTcR ht_pos.le
      _ = c * (R * t) := by ring
      _ = c * ‖w‖ := by rw [← hw_norm_eq]

/-- The charted fixed-time exponential has Fréchet derivative `id` at zero. -/
theorem expAt_chart_hasFDerivAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    HasFDerivAt
      (fun v : E => extChartAt I x₀ (expAt g x₀ v))
      (ContinuousLinearMap.id ℝ E) (0 : E) :=
  expAt_chart_hasFDerivAt_zero_of_remainder
    (g := g) (x₀ := x₀)
    (expAt_chart_remainder_isLittleO_zero (g := g) (x₀ := x₀))

end GeodesicTransport
end Poincare
