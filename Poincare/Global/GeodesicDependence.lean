import Poincare.Global.ExponentialFixedTime

/-!
# Lipschitz dependence for local chart geodesic flows

This module records the first quantitative dependence statement needed before
the transverse Gauss-lemma smooth-dependence interface can be upgraded.  The
result is deliberately only Lipschitz/continuous dependence on the initial
velocity; no differentiability in the initial velocity is asserted here.
-/

noncomputable section

open Bundle Function Set Metric
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

omit [T2Space M] in
/-- The chart Christoffel field is globally `C¹` in the model chart variable. -/
theorem chartChristoffelField_contDiffAt_base
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z : E) :
    ContDiffAt ℝ 1 (chartChristoffelField g x₀) z := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hblend :
      ContDiff ℝ (1 + 1)
        (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀) := by
    simpa using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
        htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
        (cutoff_tsupport (n := n) x₀) hg2)
  apply contDiffAt_clm_of_apply
  intro u
  apply contDiffAt_clm_of_apply
  intro v
  simpa [chartChristoffelField] using
    (CovariantDerivative.contDiffAt_christoffelAt
      (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (k := 1) (x := z)
      hblend
      (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀)
      (CovariantDerivative.chartBilin_nondegenerate
        (cutoff (n := n) x₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
        (cutoff_support_invertible (n := n) x₀))
      (fun z v w => rfl) v u)

omit [T2Space M] in
/-- The chart Christoffel field is globally `C¹`. -/
theorem chartChristoffelField_contDiff
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContDiff ℝ 1 (chartChristoffelField g x₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact chartChristoffelField_contDiffAt_base (g := g) (x₀ := x₀) z

omit [T2Space M] in
/-- The first-order chart geodesic flow field is globally `C¹`. -/
theorem geodesicFlowField_chartChristoffelField_contDiff
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ContDiff ℝ 1 (geodesicFlowField (chartChristoffelField g x₀)) :=
  contDiff_geodesicFlowField
    (Γ := chartChristoffelField g x₀)
    (chartChristoffelField_contDiff (g := g) (x₀ := x₀))

omit [T2Space M] in
/--
On each compact closed ball in first-order chart state space, the chart
geodesic flow field has a finite Lipschitz constant.
-/
theorem geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (p : E × E) (a : ℝ) :
    ∃ K : ℝ≥0,
      LipschitzOnWith K
        (geodesicFlowField (chartChristoffelField g x₀))
        (closedBall p a) := by
  exact
    (geodesicFlowField_chartChristoffelField_contDiff (g := g) (x₀ := x₀)).contDiffOn
      |>.exists_lipschitzOnWith (by norm_num) (convex_closedBall p a)
        (isCompact_closedBall p a)

omit [T2Space M] in
/--
Gronwall dependence on initial velocity for any common PL chart flow.

If all solutions starting from `(z₀, v)` remain in one closed ball on
`[-ε, ε]`, and the vector field is `K`-Lipschitz on that ball, then for every
fixed `t ∈ [0, ε]` the time-`t` endpoint is Lipschitz in `v`.  The constant is
uniform in `t` on the right half-interval: `exp (K * ε)`.
-/
theorem chart_flow_initialVelocity_lipschitzOn_of_ODE
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ ε a : ℝ} {K : ℝ≥0} {α : E × E → ℝ → E × E}
    (hε : 0 < ε)
    (hLip : LipschitzOnWith K
      (geodesicFlowField (chartChristoffelField g x₀))
      (closedBall (extChartAt I x₀ x₀, (0 : E)) a))
    (hα0 : ∀ v : E, ‖v‖ < δ →
      α (extChartAt I x₀ x₀, v) 0 = (extChartAt I x₀ x₀, v))
    (hαder : ∀ v : E, ‖v‖ < δ → ∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v) τ))
        (Icc (-ε) ε) τ)
    (hαmem : ∀ v : E, ‖v‖ < δ → ∀ τ ∈ Icc (-ε) ε,
      α (extChartAt I x₀ x₀, v) τ ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ε) :
    LipschitzOnWith
      ⟨Real.exp ((K : ℝ) * ε), (Real.exp_pos _).le⟩
      (fun v : E => α (extChartAt I x₀ x₀, v) t)
      (ball (0 : E) δ) := by
  let z₀ : E := extChartAt I x₀ x₀
  let F : E × E → E × E := geodesicFlowField (chartChristoffelField g x₀)
  have hIcc_subset : Icc (0 : ℝ) ε ⊆ Icc (-ε) ε := by
    intro τ hτ
    exact ⟨by linarith [hτ.1, hε], hτ.2⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro v₁ hv₁ v₂ hv₂
  have hv₁norm : ‖v₁‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv₁
  have hv₂norm : ‖v₂‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv₂
  have hcont₁ :
      ContinuousOn (α (z₀, v₁)) (Icc (0 : ℝ) ε) := by
    refine HasDerivWithinAt.continuousOn
      (f' := fun τ => F (α (z₀, v₁) τ)) ?_
    intro τ hτ
    exact (hαder v₁ hv₁norm τ (hIcc_subset hτ)).mono hIcc_subset
  have hcont₂ :
      ContinuousOn (α (z₀, v₂)) (Icc (0 : ℝ) ε) := by
    refine HasDerivWithinAt.continuousOn
      (f' := fun τ => F (α (z₀, v₂) τ)) ?_
    intro τ hτ
    exact (hαder v₂ hv₂norm τ (hIcc_subset hτ)).mono hIcc_subset
  have hgr :
      dist (α (z₀, v₁) t) (α (z₀, v₂) t) ≤
        dist v₁ v₂ * Real.exp ((K : ℝ) * (t - 0)) := by
    refine
      dist_le_of_trajectories_ODE_of_mem
        (v := fun _ : ℝ => F)
        (s := fun _ : ℝ => closedBall (z₀, (0 : E)) a)
        (K := K) (a := 0) (b := ε)
        ?_ hcont₁ ?_ ?_ hcont₂ ?_ ?_ ?_ t ht
    · intro τ hτ
      simpa [F, z₀] using hLip
    · intro τ hτ
      have hτfull : τ ∈ Icc (-ε) ε :=
        hIcc_subset (Ico_subset_Icc_self hτ)
      exact (hαder v₁ hv₁norm τ hτfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hτfull.1, hτ.2⟩)
    · intro τ hτ
      exact hαmem v₁ hv₁norm τ (hIcc_subset (Ico_subset_Icc_self hτ))
    · intro τ hτ
      have hτfull : τ ∈ Icc (-ε) ε :=
        hIcc_subset (Ico_subset_Icc_self hτ)
      exact (hαder v₂ hv₂norm τ hτfull).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hτfull.1, hτ.2⟩)
    · intro τ hτ
      exact hαmem v₂ hv₂norm τ (hIcc_subset (Ico_subset_Icc_self hτ))
    · rw [hα0 v₁ hv₁norm, hα0 v₂ hv₂norm]
      simp [dist_prod_same_left]
  have hKt : (K : ℝ) * t ≤ (K : ℝ) * ε :=
    mul_le_mul_of_nonneg_left ht.2 K.2
  have hexp : Real.exp ((K : ℝ) * t) ≤ Real.exp ((K : ℝ) * ε) :=
    Real.exp_le_exp.mpr hKt
  calc
    dist (α (z₀, v₁) t) (α (z₀, v₂) t)
        ≤ Real.exp ((K : ℝ) * t) * dist v₁ v₂ := by
          simpa [sub_zero, mul_comm] using hgr
    _ ≤ Real.exp ((K : ℝ) * ε) * dist v₁ v₂ := by
          exact mul_le_mul_of_nonneg_right hexp dist_nonneg

omit [T2Space M] in
/--
Existence of a uniform local chart flow whose time slices are Lipschitz in the
initial velocity on the small velocity ball.
-/
theorem exists_uniform_local_geodesic_chart_flow_lipschitzOn_initialVelocity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0, ∃ K : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) t))
                (Icc (-ε) ε) t) ∧
            ∀ t ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) t ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
        ∀ t ∈ Icc (0 : ℝ) ε,
          LipschitzOnWith
            ⟨Real.exp ((K : ℝ) * ε), (Real.exp_pos _).le⟩
            (fun v : E => α (extChartAt I x₀ x₀, v) t)
            (ball (0 : E) δ) := by
  rcases exists_uniform_local_geodesic_chart_flow_with_mem_closedBall
      (g := g) (x₀ := x₀) with
    ⟨δ, hδ, ε, hε, a, α, hα⟩
  rcases geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      (g := g) (x₀ := x₀) (p := (extChartAt I x₀ x₀, (0 : E)))
      (a := (a : ℝ)) with
    ⟨K, hLip⟩
  refine ⟨δ, hδ, ε, hε, a, K, α, ?_, ?_⟩
  · exact hα
  · intro t ht
    exact chart_flow_initialVelocity_lipschitzOn_of_ODE
      (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := (a : ℝ))
      (K := K) (α := α) hε hLip
      (fun v hv => (hα v hv).1)
      (fun v hv => (hα v hv).2.1)
      (fun v hv => (hα v hv).2.2)
      ht

omit [T2Space M] in
/--
Continuity in the initial velocity for the uniform local chart flow, obtained
from the Lipschitz estimate.
-/
theorem exists_uniform_local_geodesic_chart_flow_initialVelocity_continuousOn
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) t))
                (Icc (-ε) ε) t) ∧
            ∀ t ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) t ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
        ∀ t ∈ Icc (0 : ℝ) ε,
          ContinuousOn
            (fun v : E => α (extChartAt I x₀ x₀, v) t)
            (ball (0 : E) δ) := by
  rcases exists_uniform_local_geodesic_chart_flow_lipschitzOn_initialVelocity
      (g := g) (x₀ := x₀) with
    ⟨δ, hδ, ε, hε, a, K, α, hα, hLip⟩
  refine ⟨δ, hδ, ε, hε, a, α, hα, ?_⟩
  intro t ht
  exact (hLip t ht).continuousOn

omit [T2Space M] in
/--
The fixed-time exponential map is continuous on a sufficiently small chart
velocity ball.

The proof uses the ray-law representation at a time
`η = min τ ε / 2`, so the endpoint lies inside both the exposed ray interval
and the exposed ODE-control interval.
-/
theorem expAt_continuousOn_smallBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ContinuousOn (expAt g x₀) (ball (0 : E) ρ) := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, hexp⟩
  rcases geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
      (g := g) (x₀ := x₀) (p := (extChartAt I x₀ x₀, (0 : E)))
      (a := (a : ℝ)) with
    ⟨K, hLip⟩
  let η : ℝ := min τ ε / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    exact half_pos (lt_min hτ hε)
  have hητ : η ∈ Icc (0 : ℝ) τ := by
    constructor
    · exact hη_pos.le
    · dsimp [η]
      have hmin : min τ ε ≤ τ := min_le_left τ ε
      linarith
  have hηε : η ∈ Icc (0 : ℝ) ε := by
    constructor
    · exact hη_pos.le
    · dsimp [η]
      have hmin : min τ ε ≤ ε := min_le_right τ ε
      linarith
  have hηfull : η ∈ Icc (-ε) ε := by
    exact ⟨by linarith [hη_pos, hε], hηε.2⟩
  let ρ : ℝ := η * δ
  have hρ_pos : 0 < ρ := mul_pos hη_pos hδ
  refine ⟨ρ, hρ_pos, ?_⟩
  have hscale_maps : MapsTo (fun w : E => η⁻¹ • w) (ball (0 : E) ρ) (ball (0 : E) δ) := by
    intro w hw
    have hw_norm : ‖w‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_zero]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hη_pos)]
    calc η⁻¹ * ‖w‖
        < η⁻¹ * (η * δ) := by
          exact mul_lt_mul_of_pos_left hw_norm (inv_pos.mpr hη_pos)
      _ = δ := by
          field_simp [ne_of_gt hη_pos]
  have hstate_lip :
      LipschitzOnWith
        ⟨Real.exp ((K : ℝ) * ε), (Real.exp_pos _).le⟩
        (fun v : E => α (extChartAt I x₀ x₀, v) η)
        (ball (0 : E) δ) :=
    chart_flow_initialVelocity_lipschitzOn_of_ODE
      (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := (a : ℝ))
      (K := K) (α := α) hε hLip
      (fun v hv => (hα v hv).1)
      (fun v hv => (hα v hv).2.1)
      (fun v hv => (hα v hv).2.2.1)
      hηε
  have hscale_cont :
      ContinuousOn (fun w : E => η⁻¹ • w) (ball (0 : E) ρ) :=
    (continuous_const_smul η⁻¹).continuousOn
  have hstate_cont :
      ContinuousOn
        (fun w : E => α (extChartAt I x₀ x₀, η⁻¹ • w) η)
        (ball (0 : E) ρ) :=
    hstate_lip.continuousOn.comp hscale_cont hscale_maps
  have hpos_cont :
      ContinuousOn
        (fun w : E => (α (extChartAt I x₀ x₀, η⁻¹ • w) η).1)
        (ball (0 : E) ρ) :=
    continuous_fst.comp_continuousOn hstate_cont
  have htarget :
      MapsTo
        (fun w : E => (α (extChartAt I x₀ x₀, η⁻¹ • w) η).1)
        (ball (0 : E) ρ) (extChartAt I x₀).target := by
    intro w hw
    have hv := hscale_maps hw
    have hv_norm : ‖η⁻¹ • w‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    exact (hα (η⁻¹ • w) hv_norm).2.2.2.1 η hηfull
  have hsymm_cont :
      ContinuousOn (extChartAt I x₀).symm (extChartAt I x₀).target :=
    continuousOn_extChartAt_symm x₀
  have hendpoint_cont :
      ContinuousOn
        (fun w : E =>
          (extChartAt I x₀).symm
            ((α (extChartAt I x₀ x₀, η⁻¹ • w) η).1))
        (ball (0 : E) ρ) :=
    hsymm_cont.comp hpos_cont htarget
  refine hendpoint_cont.congr ?_
  intro w hw
  have hv := hscale_maps hw
  have hv_norm : ‖η⁻¹ • w‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hrescale : η • (η⁻¹ • w) = w := by
    calc
      η • (η⁻¹ • w) = (η * η⁻¹) • w := by rw [smul_smul]
      _ = w := by
        rw [mul_inv_cancel₀ (ne_of_gt hη_pos), one_smul]
  simpa [hrescale] using hexp (η⁻¹ • w) hv_norm η hητ

end GeodesicTransport
end Poincare
