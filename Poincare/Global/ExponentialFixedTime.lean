import Poincare.Global.ExponentialMapDef

/-!
# Fixed-time local exponential endpoint

This file adds the closed-interval flow homogeneity needed for a fixed-time
endpoint construction.  The map `expAt` is chosen from the fixed-time package
below: on the honest small ball it is the endpoint at a positive time `τ` of
the target-controlled Picard-Lindelöf flow with initial velocity rescaled by
`τ⁻¹`; outside that ball the package uses the harmless junk value `x₀`.

The final ray law is currently proved as a right-neighborhood statement at
`0`.  The existing germ API identifies the PL flow with the chosen
`geodesicGermChartSolution` only as an `EventuallyEq` at `0`, not on a uniform
closed interval.
-/

noncomputable section

open Filter Function Set Metric
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

private theorem mul_mem_Icc_of_mem_Icc_zero_one
    {s t ε : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (-ε) ε) :
    s * t ∈ Icc (-ε) ε := by
  have ht_abs : |t| ≤ ε := abs_le.mpr ht
  have hε_nonneg : 0 ≤ ε := (abs_nonneg t).trans ht_abs
  have hs_abs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have hst_abs : |s * t| ≤ ε := by
    rw [abs_mul]
    calc |s| * |t|
        ≤ 1 * ε := by
          gcongr
      _ = ε := one_mul ε
  exact abs_le.mp hst_abs

private theorem norm_smul_lt_of_mem_Icc_zero_one
    {s δ : ℝ} {v : E} (hs : s ∈ Icc (0 : ℝ) 1) (hv : ‖v‖ < δ) :
    ‖s • v‖ < δ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖v‖
      ≤ 1 * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)
    _ = ‖v‖ := one_mul _
    _ < δ := hv

private theorem smul_mem_closedBall_zero_of_mem_Icc
    {s a : ℝ} {v : E} (hs : s ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ closedBall (0 : E) a) :
    s • v ∈ closedBall (0 : E) a := by
  have hvnorm : ‖v‖ ≤ a := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hnorm : ‖s • v‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖v‖
        ≤ 1 * ‖v‖ := by
          exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)
      _ = ‖v‖ := one_mul _
      _ ≤ a := hvnorm
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

private theorem inv_smul_smul_norm_lt_of_mem_Icc
    {τ δ t : ℝ} {v : E} (hτ : 0 < τ) (ht : t ∈ Icc (0 : ℝ) τ)
    (hv : ‖v‖ < δ) :
    ‖τ⁻¹ • (t • v)‖ < δ := by
  have hτinv_pos : 0 < τ⁻¹ := inv_pos.mpr hτ
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hτinv_pos, abs_of_nonneg ht.1]
  calc τ⁻¹ * (t * ‖v‖)
      ≤ τ⁻¹ * (τ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v))
          hτinv_pos.le
    _ = ‖v‖ := by
        field_simp [ne_of_gt hτ]
    _ < δ := hv

private theorem inv_mul_mem_Icc_zero_one
    {τ t : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc (0 : ℝ) τ) :
    τ⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hτ.le) ht.1
  · calc τ⁻¹ * t
        ≤ τ⁻¹ * τ := by
          exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hτ.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hτ)

private theorem half_mem_Icc_neg_self_self {ε : ℝ} (hε : 0 < ε) :
    ε / 2 ∈ Icc (-ε) ε := by
  constructor <;> linarith

private theorem geodesicGermChartSolution_eventually_hasDerivAt_fixedTime
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (geodesicGermChartSolution g x₀ v₀)
        (geodesicFlowField (chartChristoffelField g x₀)
          (geodesicGermChartSolution g x₀ v₀ t)) t := by
  have hspec := geodesicGermChartSolution_spec g x₀ v₀
  have hε := geodesicGermRadius_pos g x₀ v₀
  have hI :
      Ioo (-(geodesicGermRadius g x₀ v₀))
          (geodesicGermRadius g x₀ v₀) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hI] with t ht
  exact hspec.2.1 t ht

/-- The PL selector retains joint continuity in initial state and time while
its position is confined to any prescribed neighborhood of the chart center. -/
theorem exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {U : Set E} (hU : U ∈ 𝓝 (extChartAt I x₀ x₀)) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ α : (E × E) × ℝ → E × E,
        (∀ p ∈ closedBall (extChartAt I x₀ x₀, (0 : E)) (r : ℝ),
          α (p, 0) = p ∧
            ∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (fun s : ℝ => α (p, s))
                (geodesicFlowField (chartChristoffelField g x₀) (α (p, t)))
                (Icc (-ε) ε) t) ∧
        (∀ q ∈
          closedBall (extChartAt I x₀ x₀, (0 : E)) (r : ℝ) ×ˢ
            Icc (-ε) ε,
          (α q).1 ∈ U) ∧
        ContinuousOn α
          (closedBall (extChartAt I x₀ x₀, (0 : E)) (r : ℝ) ×ˢ
            Icc (-ε) ε) := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  let F : E × E → E × E :=
    geodesicFlowField (chartChristoffelField g x₀)
  have hflow : ContDiffAt ℝ 1 F p₀ := by
    simpa [F, p₀] using
      (geodesicFlowField_chartChristoffelField_contDiffAt
        (g := g) (x₀ := x₀) (v₀ := (0 : E)))
  rcases IsPicardLindelof.of_contDiffAt_one hflow with
    ⟨ε₀, hε₀, a₀, r₀, L, K, hr₀, hpl₀⟩
  rcases
      (hpl₀ (0 : ℝ)).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    with ⟨β, hβspec, hβcont⟩
  have hcenterState : p₀ ∈ closedBall p₀ (r₀ : ℝ) :=
    mem_closedBall_self r₀.2
  have hβcenter : β (p₀, (0 : ℝ)) = p₀ :=
    (hβspec p₀ hcenterState).1
  have hdomain_nhds :
      closedBall p₀ (r₀ : ℝ) ×ˢ Icc (-ε₀) ε₀ ∈
        𝓝 (p₀, (0 : ℝ)) := by
    exact prod_mem_nhds
      (closedBall_mem_nhds p₀ (by exact_mod_cast hr₀))
      (Icc_mem_nhds (by linarith) hε₀)
  have hβat : ContinuousAt β (p₀, (0 : ℝ)) := by
    apply hβcont.continuousAt
    simpa only [zero_sub, zero_add] using hdomain_nhds
  have hposition_nhds :
      {q : (E × E) × ℝ | (β q).1 ∈ U} ∈
        𝓝 (p₀, (0 : ℝ)) := by
    have hU' : U ∈ 𝓝 p₀.1 := by simpa [p₀] using hU
    have hUβ : U ∈ 𝓝 (β (p₀, (0 : ℝ))).1 := by
      rw [hβcenter]
      exact hU'
    exact hβat.fst.preimage_mem_nhds hUβ
  rcases mem_nhds_prod_iff.mp hposition_nhds with
    ⟨S, hS, T, hT, hST⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hS with
    ⟨ρs, hρs, hρsS⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hT with
    ⟨ρt, hρt, hρtT⟩
  let r : ℝ≥0 := min r₀ ⟨ρs, hρs.le⟩
  let ε : ℝ := min ε₀ ρt
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hr₀ (by exact_mod_cast hρs)
  have hε : 0 < ε := lt_min hε₀ hρt
  have hr_le_r₀ : (r : ℝ) ≤ (r₀ : ℝ) := by
    exact_mod_cast (show r ≤ r₀ by dsimp [r]; exact min_le_left _ _)
  have hr_le_ρs : (r : ℝ) ≤ ρs := by
    exact_mod_cast
      (show r ≤ (⟨ρs, hρs.le⟩ : ℝ≥0) by
        dsimp [r]
        exact min_le_right _ _)
  have hε_le_ε₀ : ε ≤ ε₀ := by dsimp [ε]; exact min_le_left _ _
  have hε_le_ρt : ε ≤ ρt := by dsimp [ε]; exact min_le_right _ _
  have htimeOld : Icc (-ε) ε ⊆ Icc (0 - ε₀) (0 + ε₀) := by
    intro t ht
    exact ⟨by simpa only [zero_sub] using (neg_le_neg hε_le_ε₀).trans ht.1,
      by simpa only [zero_add] using ht.2.trans hε_le_ε₀⟩
  refine ⟨r, hr, ε, hε, β, ?_, ?_, ?_⟩
  · intro p hp
    have hpOld : p ∈ closedBall p₀ (r₀ : ℝ) := by
      apply closedBall_subset_closedBall hr_le_r₀
      simpa [p₀] using hp
    have hspec := hβspec p hpOld
    refine ⟨hspec.1, ?_⟩
    intro t ht
    exact (hspec.2 t (htimeOld ht)).mono htimeOld
  · intro q hq
    apply hST
    constructor
    · apply hρsS
      exact closedBall_subset_closedBall hr_le_ρs hq.1
    · apply hρtT
      rw [Metric.mem_closedBall, Real.dist_eq]
      simpa only [sub_zero] using
        (abs_le.mpr ⟨(neg_le_neg hε_le_ρt).trans hq.2.1,
          hq.2.2.trans hε_le_ρt⟩)
  · apply hβcont.mono
    rintro ⟨p, t⟩ hpt
    constructor
    · apply closedBall_subset_closedBall hr_le_r₀
      simpa [p₀] using hpt.1
    · exact htimeOld hpt.2

/-- One fixed coordinate chart admits a uniform PL geodesic flow for every
initial position-velocity state in a genuine closed neighborhood of its
center.  All trajectories remain in one state ball and their position
components remain in any prescribed neighborhood of the center coordinate.
Choosing the fixed chart target gives target retention.  Velocity homogeneity
holds at each retained initial position. -/
theorem exists_uniform_local_geodesic_chart_flow_variable_initialState_with_position_mem_neighborhood
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {U : Set E} (hU : U ∈ 𝓝 (extChartAt I x₀ x₀)) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        ∀ p ∈ closedBall (extChartAt I x₀ x₀, (0 : E)) (r : ℝ),
          α p 0 = p ∧
          (∀ t ∈ Icc (-ε) ε,
            HasDerivWithinAt (α p)
              (geodesicFlowField (chartChristoffelField g x₀) (α p t))
              (Icc (-ε) ε) t) ∧
          (∀ t ∈ Icc (-ε) ε,
            α p t ∈
              closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
          (∀ t ∈ Icc (-ε) ε, (α p t).1 ∈ U) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
            α (p.1, s • p.2) σ =
              ((α p (s * σ)).1, s • (α p (s * σ)).2) := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  let z₀ : E := extChartAt I x₀ x₀
  let F : E × E → E × E :=
    geodesicFlowField (chartChristoffelField g x₀)
  have hflow : ContDiffAt ℝ 1 F p₀ := by
    simpa [F, p₀] using
      (geodesicFlowField_chartChristoffelField_contDiffAt
        (g := g) (x₀ := x₀) (v₀ := (0 : E)))
  rcases IsPicardLindelof.of_contDiffAt_one hflow with
    ⟨ε₀, hε₀, a₀, r₀, L, K, hr₀, hpl₀⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (by simpa [z₀] using hU) with
    ⟨ρ, hρpos, hρsub⟩
  have ha₀_pos : 0 < (a₀ : ℝ) := by
    have hpl := hpl₀ (0 : ℝ)
    have hnonneg :
        0 ≤ (L : ℝ) *
          max ((0 : ℝ) + ε₀ - (0 : ℝ)) ((0 : ℝ) - ((0 : ℝ) - ε₀)) := by
      exact mul_nonneg (NNReal.coe_nonneg L)
        (le_max_of_le_left (by linarith))
    have hsub_nonneg : 0 ≤ (a₀ : ℝ) - (r₀ : ℝ) :=
      hnonneg.trans hpl.mul_max_le
    have hr₀_real : 0 < (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  let targetRadius : ℝ≥0 := ⟨ρ / 2, (half_pos hρpos).le⟩
  let a : ℝ≥0 := min a₀ targetRadius
  have htargetRadius_pos : 0 < targetRadius := by
    change (0 : ℝ) < ρ / 2
    exact half_pos hρpos
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by exact_mod_cast ha₀_pos) htargetRadius_pos
  let r : ℝ≥0 := a / 2
  have hr_pos : 0 < r := by
    dsimp [r]
    exact half_pos ha_pos
  have hr_lt : r < a := by
    dsimp [r]
    exact half_lt_self ha_pos
  rcases (hpl₀ (0 : ℝ)).exists_shrink_radius hε₀ (a' := a) (r' := r)
      (by dsimp [a]; exact min_le_left _ _) hr_lt with
    ⟨ε, hε, hpl⟩
  rcases
      hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨α, hα⟩
  refine ⟨r, hr_pos, ε, hε, a, α, ?_⟩
  intro p hp
  have hspec := hα p (by simpa [p₀] using hp)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [p₀] using hspec.1
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa [F, p₀] using hspec.2.1 t ht'
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa [p₀] using hspec.2.2 t ht'
  · intro t ht
    have hmem : α p t ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
      have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
        simpa only [zero_sub, zero_add] using ht
      simpa [p₀, z₀] using hspec.2.2 t ht'
    have hpos_mem : (α p t).1 ∈ closedBall z₀ (a : ℝ) := by
      have hprod : α p t ∈
          closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        simpa [closedBall_prod_same] using hmem
      exact hprod.1
    apply hρsub
    have ha_le_half : (a : ℝ) ≤ ρ / 2 := by
      have ha_le_target : a ≤ targetRadius := by
        dsimp [a]
        exact min_le_right _ _
      exact_mod_cast ha_le_target
    exact closedBall_subset_closedBall (by linarith) hpos_mem
  · intro s hs σ hσ
    have hp_prod : p ∈
        closedBall z₀ (r : ℝ) ×ˢ closedBall (0 : E) (r : ℝ) := by
      simpa [p₀, z₀, closedBall_prod_same] using hp
    have hps_prod : (p.1, s • p.2) ∈
        closedBall z₀ (r : ℝ) ×ˢ closedBall (0 : E) (r : ℝ) :=
      ⟨hp_prod.1, smul_mem_closedBall_zero_of_mem_Icc hs hp_prod.2⟩
    have hps : (p.1, s • p.2) ∈ closedBall p₀ (r : ℝ) := by
      simpa [p₀, z₀, closedBall_prod_same] using hps_prod
    have hspec_s := hα (p.1, s • p.2) (by simpa [p₀] using hps)
    let γ : ℝ → E × E := α p
    let η : ℝ → E × E := fun τ =>
      ((γ (s * τ)).1, s • (γ (s * τ)).2)
    have hmaps : MapsTo (fun τ : ℝ => s * τ) (Icc (-ε) ε) (Icc (-ε) ε) :=
      fun τ hτ => mul_mem_Icc_of_mem_Icc_zero_one hs hτ
    have hηder : ∀ τ ∈ Icc (-ε) ε, HasDerivWithinAt η
        (F (η τ)) (Icc (-ε) ε) τ := by
      intro τ hτ
      have hγτ : HasDerivWithinAt γ (F (γ (s * τ)))
          (Icc (-ε) ε) (s * τ) := by
        have hτ' : s * τ ∈ Icc (0 - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using hmaps hτ
        simpa [γ, F, p₀, zero_sub, zero_add] using hspec.2.1 (s * τ) hτ'
      have hreparam : HasDerivWithinAt (fun τ' : ℝ => γ (s * τ'))
          (s • F (γ (s * τ))) (Icc (-ε) ε) τ := by
        simpa [Function.comp_def] using
          hγτ.scomp τ
            ((hasDerivAt_const_mul (x := τ) s).hasDerivWithinAt) hmaps
      have hpos : HasDerivWithinAt (fun τ' : ℝ => (γ (s * τ')).1)
          (s • (γ (s * τ)).2) (Icc (-ε) ε) τ := by
        have hfst := hreparam.hasFDerivWithinAt.fst.hasDerivWithinAt
        simpa [F, geodesicFlowField] using hfst
      have hvel_reparam :
          HasDerivWithinAt (fun τ' : ℝ => (γ (s * τ')).2)
            (s • (-(chartChristoffelField g x₀ (γ (s * τ)).1)
              (γ (s * τ)).2 (γ (s * τ)).2))
            (Icc (-ε) ε) τ := by
        have hsnd := hreparam.hasFDerivWithinAt.snd.hasDerivWithinAt
        simpa [F, geodesicFlowField] using hsnd
      have hvel : HasDerivWithinAt
          (fun τ' : ℝ => s • (γ (s * τ')).2)
          (-(chartChristoffelField g x₀ (γ (s * τ)).1
            (s • (γ (s * τ)).2) (s • (γ (s * τ)).2)))
          (Icc (-ε) ε) τ := by
        simpa [smul_smul] using hvel_reparam.const_smul s
      have hprod := hpos.prodMk hvel
      simpa [η, F, geodesicFlowField] using hprod
    have hηmem : ∀ τ ∈ Icc (-ε) ε,
        η τ ∈ closedBall p₀ (a : ℝ) := by
      intro τ hτ
      have hγmem : γ (s * τ) ∈
          closedBall (z₀, (0 : E)) (a : ℝ) := by
        have hτ' : s * τ ∈ Icc (0 - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using hmaps hτ
        simpa [γ, p₀, z₀] using hspec.2.2 (s * τ) hτ'
      have hprod : γ (s * τ) ∈
          closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        simpa [closedBall_prod_same] using hγmem
      have hηprod : η τ ∈
          closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) :=
        ⟨hprod.1, smul_mem_closedBall_zero_of_mem_Icc hs hprod.2⟩
      simpa [η, p₀, z₀, closedBall_prod_same] using hηprod
    have hη0 : η 0 = (p.1, s • p.2) := by
      simp [η, γ, hspec.1]
    have hsame₀ : α (p.1, s • p.2) 0 = η 0 := by
      rw [hspec_s.1, hη0]
    have heq : EqOn (α (p.1, s • p.2)) η (Icc (-ε) ε) := by
      have heq_raw : EqOn (α (p.1, s • p.2)) η
          (Icc (0 - ε) (0 + ε)) :=
        hpl.eqOn_Icc_of_mem_closedBall
          (hα := by
            intro τ hτ
            simpa [F, p₀] using hspec_s.2.1 τ hτ)
          (hαmem := by
            intro τ hτ
            simpa [p₀] using hspec_s.2.2 τ hτ)
          (hβ := by
            intro τ hτ
            have hτ' : τ ∈ Icc (-ε) ε := by
              simpa only [zero_sub, zero_add] using hτ
            simpa only [zero_sub, zero_add] using hηder τ hτ')
          (hβmem := by
            intro τ hτ
            have hτ' : τ ∈ Icc (-ε) ε := by
              simpa only [zero_sub, zero_add] using hτ
            exact hηmem τ hτ')
          hsame₀
      intro τ hτ
      exact heq_raw (by simpa only [zero_sub, zero_add] using hτ)
    simpa [η, γ] using heq hσ

/--
Target-controlled local geodesic chart flow with closed-interval homogeneity.

For `s ∈ [0,1]`, the reparametrized curve
`σ ↦ ((α (z₀, v) (s * σ)).1, s • (α (z₀, v) (s * σ)).2)` is the same PL
solution as the flow from the scaled initial velocity `s • v` on the whole
closed interval `Icc (-ε) ε`.
-/
theorem exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target_homogeneous
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E, ∀ v₀ : E, ‖v₀‖ < δ →
        α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
          (∀ t ∈ Icc (-ε) ε,
            HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
              (geodesicFlowField (chartChristoffelField g x₀)
                (α (extChartAt I x₀ x₀, v₀) t))
              (Icc (-ε) ε) t) ∧
          (∀ t ∈ Icc (-ε) ε,
            α (extChartAt I x₀ x₀, v₀) t ∈
              closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
          (∀ t ∈ Icc (-ε) ε,
            (α (extChartAt I x₀ x₀, v₀) t).1 ∈
              (extChartAt I x₀).target) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
            α (extChartAt I x₀ x₀, s • v₀) σ =
              ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
                s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2) := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  let z₀ : E := extChartAt I x₀ x₀
  let F : E × E → E × E :=
    geodesicFlowField (chartChristoffelField g x₀)
  have hflow : ContDiffAt ℝ 1 F p₀ := by
    simpa [F, p₀] using
      (geodesicFlowField_chartChristoffelField_contDiffAt
        (g := g) (x₀ := x₀) (v₀ := (0 : E)))
  rcases IsPicardLindelof.of_contDiffAt_one hflow with
    ⟨ε₀, hε₀, a₀, r₀, L, K, hr₀, hpl₀⟩
  have htarget_nhds :
      (extChartAt I x₀).target ∈ 𝓝 z₀ := by
    exact (isOpen_extChartAt_target x₀).mem_nhds
      (by simp [z₀])
  rcases Metric.nhds_basis_closedBall.mem_iff.mp htarget_nhds with
    ⟨ρ, hρpos, hρsub⟩
  have ha₀_pos : 0 < (a₀ : ℝ) := by
    have hpl := hpl₀ (0 : ℝ)
    have hnonneg :
        0 ≤ (L : ℝ) *
          max ((0 : ℝ) + ε₀ - (0 : ℝ)) ((0 : ℝ) - ((0 : ℝ) - ε₀)) := by
      exact mul_nonneg (NNReal.coe_nonneg L) (le_max_of_le_left (by linarith))
    have hsub_nonneg : 0 ≤ (a₀ : ℝ) - (r₀ : ℝ) :=
      hnonneg.trans hpl.mul_max_le
    have hr₀_real : 0 < (r₀ : ℝ) := by exact_mod_cast hr₀
    linarith
  let targetRadius : ℝ≥0 := ⟨ρ / 2, (half_pos hρpos).le⟩
  let a : ℝ≥0 := min a₀ targetRadius
  have htargetRadius_pos : 0 < targetRadius := by
    change (0 : ℝ) < ρ / 2
    exact half_pos hρpos
  have ha_pos : 0 < a := by
    dsimp [a]
    exact lt_min (by exact_mod_cast ha₀_pos) htargetRadius_pos
  let r : ℝ≥0 := a / 2
  have hr_lt : r < a := by
    dsimp [r]
    exact half_lt_self ha_pos
  rcases (hpl₀ (0 : ℝ)).exists_shrink_radius hε₀ (a' := a) (r' := r)
      (by dsimp [a]; exact min_le_left _ _) hr_lt with
    ⟨ε, hε, hpl_raw⟩
  rcases
      hpl_raw.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨α, hα⟩
  refine ⟨(r : ℝ), by exact_mod_cast (half_pos ha_pos), ε, hε, a, α,
    fun v₀ hv₀ ↦ ?_⟩
  have hp :
      (z₀, v₀) ∈ closedBall p₀ r := by
    rw [Metric.mem_closedBall]
    change dist (z₀, v₀) (z₀, (0 : E)) ≤ (r : ℝ)
    rw [dist_prod_same_left]
    simpa [dist_eq_norm, z₀] using le_of_lt hv₀
  have hspec := hα (z₀, v₀) hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [p₀, z₀] using hspec.1
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa [F, p₀, z₀] using hspec.2.1 t ht'
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa [p₀, z₀] using hspec.2.2 t ht'
  · intro t ht
    have hmem :
        α (z₀, v₀) t ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
      have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
        simpa only [zero_sub, zero_add] using ht
      simpa [p₀] using hspec.2.2 t ht'
    have hpos_mem :
        (α (z₀, v₀) t).1 ∈ closedBall z₀ (a : ℝ) := by
      have hprod :
          α (z₀, v₀) t ∈
            closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        simpa [closedBall_prod_same] using hmem
      exact hprod.1
    apply hρsub
    have ha_le_half : (a : ℝ) ≤ ρ / 2 := by
      have ha_le_target : a ≤ targetRadius := by
        dsimp [a]
        exact min_le_right _ _
      exact_mod_cast ha_le_target
    exact closedBall_subset_closedBall (by linarith) hpos_mem
  · intro s hs σ hσ
    have hsv₀ : ‖s • v₀‖ < (r : ℝ) :=
      norm_smul_lt_of_mem_Icc_zero_one (v := v₀) hs hv₀
    have hps :
        (z₀, s • v₀) ∈ closedBall p₀ r := by
      rw [Metric.mem_closedBall]
      change dist (z₀, s • v₀) (z₀, (0 : E)) ≤ (r : ℝ)
      rw [dist_prod_same_left]
      simpa [dist_eq_norm, z₀] using le_of_lt hsv₀
    have hspec_s := hα (z₀, s • v₀) hps
    let γ : ℝ → E × E := α (z₀, v₀)
    let η : ℝ → E × E := fun τ =>
      ((γ (s * τ)).1, s • (γ (s * τ)).2)
    have hmaps : MapsTo (fun τ : ℝ ↦ s * τ) (Icc (-ε) ε) (Icc (-ε) ε) :=
      fun τ hτ ↦ mul_mem_Icc_of_mem_Icc_zero_one hs hτ
    have hηder :
        ∀ τ ∈ Icc (-ε) ε, HasDerivWithinAt η
          (F (η τ)) (Icc (-ε) ε) τ := by
      intro τ hτ
      have hγτ :
          HasDerivWithinAt γ (F (γ (s * τ))) (Icc (-ε) ε) (s * τ) := by
        have hτ' : s * τ ∈ Icc (0 - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using hmaps hτ
        have hder := hspec.2.1 (s * τ) hτ'
        simpa [γ, F, p₀, z₀, zero_sub, zero_add] using hder
      have hreparam :
          HasDerivWithinAt (fun τ' : ℝ ↦ γ (s * τ'))
            (s • F (γ (s * τ))) (Icc (-ε) ε) τ := by
        simpa [Function.comp_def] using
          hγτ.scomp τ
            ((hasDerivAt_const_mul (x := τ) s).hasDerivWithinAt) hmaps
      have hpos :
          HasDerivWithinAt (fun τ' : ℝ ↦ (γ (s * τ')).1)
            (s • (γ (s * τ)).2) (Icc (-ε) ε) τ := by
        have hfst := hreparam.hasFDerivWithinAt.fst.hasDerivWithinAt
        simpa [F, geodesicFlowField] using hfst
      have hvel_reparam :
          HasDerivWithinAt (fun τ' : ℝ ↦ (γ (s * τ')).2)
            (s • (-(chartChristoffelField g x₀ (γ (s * τ)).1)
              (γ (s * τ)).2 (γ (s * τ)).2)) (Icc (-ε) ε) τ := by
        have hsnd := hreparam.hasFDerivWithinAt.snd.hasDerivWithinAt
        simpa [F, geodesicFlowField] using hsnd
      have hvel :
          HasDerivWithinAt (fun τ' : ℝ ↦ s • (γ (s * τ')).2)
            (-(chartChristoffelField g x₀ (γ (s * τ)).1
              (s • (γ (s * τ)).2) (s • (γ (s * τ)).2)))
            (Icc (-ε) ε) τ := by
        simpa [smul_smul] using hvel_reparam.const_smul s
      have hprod := hpos.prodMk hvel
      simpa [η, F, geodesicFlowField] using hprod
    have hηmem :
        ∀ τ ∈ Icc (-ε) ε, η τ ∈ closedBall p₀ (a : ℝ) := by
      intro τ hτ
      have hγmem :
          γ (s * τ) ∈ closedBall (z₀, (0 : E)) (a : ℝ) := by
        have hτ' : s * τ ∈ Icc (0 - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using hmaps hτ
        simpa [γ, p₀] using hspec.2.2 (s * τ) hτ'
      have hprod :
          γ (s * τ) ∈
            closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        simpa [closedBall_prod_same] using hγmem
      have hηprod :
          η τ ∈ closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        exact ⟨hprod.1, smul_mem_closedBall_zero_of_mem_Icc hs hprod.2⟩
      simpa [η, p₀, closedBall_prod_same] using hηprod
    have hη0 : η 0 = (z₀, s • v₀) := by
      simp [η, γ, hspec.1]
    have hsame₀ : α (z₀, s • v₀) 0 = η 0 := by
      rw [hspec_s.1, hη0]
    have heq :
        EqOn (α (z₀, s • v₀)) η (Icc (-ε) ε) :=
      by
        have heq_raw :
            EqOn (α (z₀, s • v₀)) η (Icc (0 - ε) (0 + ε)) :=
          hpl_raw.eqOn_Icc_of_mem_closedBall
            (hα := by
              intro τ hτ
              simpa [F, p₀, z₀] using hspec_s.2.1 τ hτ)
            (hαmem := by
              intro τ hτ
              simpa [p₀, z₀] using hspec_s.2.2 τ hτ)
            (hβ := by
              intro τ hτ
              have hτ' : τ ∈ Icc (-ε) ε := by
                simpa only [zero_sub, zero_add] using hτ
              simpa only [zero_sub, zero_add] using hηder τ hτ')
            (hβmem := by
              intro τ hτ
              have hτ' : τ ∈ Icc (-ε) ε := by
                simpa only [zero_sub, zero_add] using hτ
              exact hηmem τ hτ')
            hsame₀
        intro τ hτ
        have hτ' : τ ∈ Icc (0 - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using hτ
        exact heq_raw hτ'
    simpa [η, γ, z₀] using heq hσ

/--
Existence of a fixed positive-time endpoint map.

The witness is `w ↦ (extChartAt I x₀).symm (α (z₀, τ⁻¹ • w) τ).1`
when the rescaled velocity is in the honest PL ball, and the junk value `x₀`
otherwise.
-/
theorem exists_expAt_fixed_time_package
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ exp : E → M,
      exp 0 = x₀ ∧
      (∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ),
        ∀ v : E, ‖v‖ < δ →
          ∀ᶠ t in 𝓝[Icc (0 : ℝ) τ] (0 : ℝ),
            exp (t • v) = geodesicGermAt g x₀ v t) ∧
      (∃ ρ > (0 : ℝ), ∀ w : E, ‖w‖ < ρ →
        exp w ∈ (extChartAt I x₀).source) ∧
      ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
        ∃ α : E × E → ℝ → E × E,
          (∀ v₀ : E, ‖v₀‖ < δ →
            α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
              (∀ t ∈ Icc (-ε) ε,
                HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                  (geodesicFlowField (chartChristoffelField g x₀)
                    (α (extChartAt I x₀ x₀, v₀) t))
                  (Icc (-ε) ε) t) ∧
              (∀ t ∈ Icc (-ε) ε,
                α (extChartAt I x₀ x₀, v₀) t ∈
                  closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
              (∀ t ∈ Icc (-ε) ε,
                (α (extChartAt I x₀ x₀, v₀) t).1 ∈
                  (extChartAt I x₀).target) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
                α (extChartAt I x₀ x₀, s • v₀) σ =
                  ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
                    s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2)) ∧
          ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
            exp (t • v) =
              (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v) t).1 := by
  rcases
      exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target_homogeneous
        (g := g) (x₀ := x₀) with
    ⟨δ, hδ, ε, hε, a, α, hα⟩
  let z₀ : E := extChartAt I x₀ x₀
  let τ : ℝ := ε / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith
  let exp : E → M := fun w =>
    if hw : ‖τ⁻¹ • w‖ < δ then
      (extChartAt I x₀).symm (α (z₀, τ⁻¹ • w) τ).1
    else x₀
  refine ⟨exp, ?_, ?_, ?_, ?_⟩
  · have hzero_small : ‖τ⁻¹ • (0 : E)‖ < δ := by
      simpa using hδ
    have hzero_vel : ‖(0 : E)‖ < δ := by
      simpa using hδ
    have hspec0 := hα (0 : E) hzero_vel
    have hconst0 :
        α (z₀, (0 : E)) τ = (z₀, (0 : E)) := by
      have hhom := hspec0.2.2.2.2 (0 : ℝ)
        (by exact ⟨le_rfl, zero_le_one⟩) τ (half_mem_Icc_neg_self_self hε)
      calc
        α (z₀, (0 : E)) τ
            = ((α (z₀, (0 : E)) 0).1, (0 : E)) := by
              simpa [z₀] using hhom
        _ = (z₀, (0 : E)) := by
              rw [hspec0.1]
    change
      (if hw : ‖τ⁻¹ • (0 : E)‖ < δ then
        (extChartAt I x₀).symm (α (z₀, τ⁻¹ • (0 : E)) τ).1
      else x₀) = x₀
    rw [dif_pos hzero_small]
    have hzero_rescale : τ⁻¹ • (0 : E) = 0 := by simp
    rw [hzero_rescale, hconst0]
    simp [z₀]
  · refine ⟨τ, hτ, δ, hδ, ?_⟩
    intro v hv
    rcases hα v hv with ⟨hα0, hαder, hαmem, hαtarget, hhom⟩
    have hgerm :
        α (z₀, v) =ᶠ[𝓝 (0 : ℝ)]
          geodesicGermChartSolution g x₀ v := by
      have hflow_der :
          ∀ᶠ t in 𝓝 (0 : ℝ),
            HasDerivAt (α (z₀, v))
              (geodesicFlowField (chartChristoffelField g x₀)
                (α (z₀, v) t)) t := by
        have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
          Ioo_mem_nhds (by linarith) (by linarith)
        filter_upwards [hI] with t ht
        exact (hαder t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      have hgerm_der :=
        geodesicGermChartSolution_eventually_hasDerivAt_fixedTime g x₀ v
      have hgerm0 :
          geodesicGermChartSolution g x₀ v 0 =
            (extChartAt I x₀ x₀, v) :=
        (geodesicGermChartSolution_spec g x₀ v).1
      exact (geodesicFlowField_chartChristoffelField_eventuallyEq
        (g := g) (x₀ := x₀) (v₀ := v)
        hgerm0 (by simpa [z₀] using hα0) hgerm_der hflow_der).symm
    have hgerm_within :
        α (z₀, v) =ᶠ[𝓝[Icc (0 : ℝ) τ] (0 : ℝ)]
          geodesicGermChartSolution g x₀ v :=
      hgerm.filter_mono nhdsWithin_le_nhds
    filter_upwards [hgerm_within, eventually_mem_nhdsWithin] with t ht_eq ht_mem
    have hsmall : ‖τ⁻¹ • (t • v)‖ < δ :=
      inv_smul_smul_norm_lt_of_mem_Icc (v := v) hτ ht_mem hv
    have hs : τ⁻¹ * t ∈ Icc (0 : ℝ) 1 :=
      inv_mul_mem_Icc_zero_one hτ ht_mem
    have hτmem : τ ∈ Icc (-ε) ε := by
      dsimp [τ]
      exact half_mem_Icc_neg_self_self hε
    have hscaled :
        τ⁻¹ • (t • v) = (τ⁻¹ * t) • v := by
      rw [smul_smul]
    have hhomτ :
        α (z₀, τ⁻¹ • (t • v)) τ =
          ((α (z₀, v) t).1, (τ⁻¹ * t) • (α (z₀, v) t).2) := by
      calc
        α (z₀, τ⁻¹ • (t • v)) τ
            = α (z₀, (τ⁻¹ * t) • v) τ := by rw [hscaled]
        _ = ((α (z₀, v) ((τ⁻¹ * t) * τ)).1,
              (τ⁻¹ * t) • (α (z₀, v) ((τ⁻¹ * t) * τ)).2) := by
              exact hhom (τ⁻¹ * t) hs τ hτmem
        _ = ((α (z₀, v) t).1,
              (τ⁻¹ * t) • (α (z₀, v) t).2) := by
              field_simp [ne_of_gt hτ]
    have hpos_eq :
        (α (z₀, τ⁻¹ • (t • v)) τ).1 =
          (geodesicGermChartSolution g x₀ v t).1 := by
      calc
        (α (z₀, τ⁻¹ • (t • v)) τ).1
            = (α (z₀, v) t).1 := by
              simpa using congrArg Prod.fst hhomτ
        _ = (geodesicGermChartSolution g x₀ v t).1 := by
              exact congrArg Prod.fst ht_eq
    change
      (if hw : ‖τ⁻¹ • (t • v)‖ < δ then
        (extChartAt I x₀).symm (α (z₀, τ⁻¹ • (t • v)) τ).1
      else x₀) = geodesicGermAt g x₀ v t
    rw [dif_pos hsmall]
    simp [geodesicGermAt, hpos_eq]
  · refine ⟨τ * δ, mul_pos hτ hδ, ?_⟩
    intro w hw
    have hsmall : ‖τ⁻¹ • w‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      calc τ⁻¹ * ‖w‖
          < τ⁻¹ * (τ * δ) := by
            gcongr
        _ = δ := by
            field_simp [ne_of_gt hτ]
    have hτmem : τ ∈ Icc (-ε) ε := by
      dsimp [τ]
      exact half_mem_Icc_neg_self_self hε
    have hspec := hα (τ⁻¹ • w) hsmall
    have htarget :
        (α (z₀, τ⁻¹ • w) τ).1 ∈ (extChartAt I x₀).target := by
      simpa [z₀] using hspec.2.2.2.1 τ hτmem
    simpa [exp, hsmall] using (extChartAt I x₀).map_target htarget
  · refine ⟨τ, hτ, δ, hδ, ε, hε, a, α, ?_, ?_⟩
    · simpa [z₀] using hα
    · intro v hv t ht
      rcases hα v hv with ⟨hα0, hαder, hαmem, hαtarget, hhom⟩
      have hsmall : ‖τ⁻¹ • (t • v)‖ < δ :=
        inv_smul_smul_norm_lt_of_mem_Icc (v := v) hτ ht hv
      have hs : τ⁻¹ * t ∈ Icc (0 : ℝ) 1 :=
        inv_mul_mem_Icc_zero_one hτ ht
      have hτmem : τ ∈ Icc (-ε) ε := by
        dsimp [τ]
        exact half_mem_Icc_neg_self_self hε
      have hscaled :
          τ⁻¹ • (t • v) = (τ⁻¹ * t) • v := by
        rw [smul_smul]
      have hhomτ :
          α (z₀, τ⁻¹ • (t • v)) τ =
            ((α (z₀, v) t).1, (τ⁻¹ * t) • (α (z₀, v) t).2) := by
        calc
          α (z₀, τ⁻¹ • (t • v)) τ
              = α (z₀, (τ⁻¹ * t) • v) τ := by rw [hscaled]
          _ = ((α (z₀, v) ((τ⁻¹ * t) * τ)).1,
                (τ⁻¹ * t) • (α (z₀, v) ((τ⁻¹ * t) * τ)).2) := by
                exact hhom (τ⁻¹ * t) hs τ hτmem
          _ = ((α (z₀, v) t).1,
                (τ⁻¹ * t) • (α (z₀, v) t).2) := by
                field_simp [ne_of_gt hτ]
      have hpos_eq :
          (α (z₀, τ⁻¹ • (t • v)) τ).1 = (α (z₀, v) t).1 := by
        simpa using congrArg Prod.fst hhomτ
      change
        (if hw : ‖τ⁻¹ • (t • v)‖ < δ then
          (extChartAt I x₀).symm (α (z₀, τ⁻¹ • (t • v)) τ).1
        else x₀) =
          (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v) t).1
      rw [dif_pos hsmall]
      simpa [z₀] using
        congrArg (fun z : E => (extChartAt I x₀).symm z) hpos_eq

/--
The fixed-time local exponential map at `x₀`.

It is the chosen endpoint map from `exists_expAt_fixed_time_package`; outside
the package's honest small ball, its value is intentionally unspecified except
for the packaged junk-value construction.
-/
noncomputable def expAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : E → M :=
  Classical.choose (exists_expAt_fixed_time_package g x₀)

@[simp]
theorem expAt_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    expAt g x₀ (0 : E) = x₀ :=
  (Classical.choose_spec (exists_expAt_fixed_time_package g x₀)).1

/--
Right-neighborhood ray law at the origin for the fixed-time exponential map.

The filter `𝓝[Icc 0 τ] 0` records the honest nonnegative side of the interval.
Promoting this to all `t ∈ [0, τ)` requires a uniform interval identification
between the PL flow and the chosen `geodesicGermChartSolution`.
-/
theorem expAt_eventually_eq_geodesicGermAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ v : E, ‖v‖ < δ →
        ∀ᶠ t in 𝓝[Icc (0 : ℝ) τ] (0 : ℝ),
          expAt g x₀ (t • v) = geodesicGermAt g x₀ v t :=
  (Classical.choose_spec (exists_expAt_fixed_time_package g x₀)).2.1

/-- Small fixed-time endpoints lie in the anchor chart source. -/
theorem expAt_mem_source_of_norm_lt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∀ v : E, ‖v‖ < ρ →
      expAt g x₀ v ∈ (extChartAt I x₀).source :=
  (Classical.choose_spec (exists_expAt_fixed_time_package g x₀)).2.2.1

/--
The chosen fixed-time exponential agrees, on one uniform closed ray interval,
with the target-controlled PL chart flow used to package it.

This exposes the closed-ball, target, and homogeneity data for the chosen
`expAt` witness.  It is deliberately a PL-flow statement; comparison with the
independently chosen `geodesicGermChartSolution` still requires an interval
identification for that germ.
-/
theorem expAt_uniform_pl_flow_eq_on_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) t))
                (Icc (-ε) ε) t) ∧
            (∀ t ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, v₀) t ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) a) ∧
            (∀ t ∈ Icc (-ε) ε,
              (α (extChartAt I x₀ x₀, v₀) t).1 ∈
                (extChartAt I x₀).target) ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc (-ε) ε,
              α (extChartAt I x₀ x₀, s • v₀) σ =
                ((α (extChartAt I x₀ x₀, v₀) (s * σ)).1,
                  s • (α (extChartAt I x₀ x₀, v₀) (s * σ)).2)) ∧
        ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
          expAt g x₀ (t • v) =
            (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v) t).1 :=
  (Classical.choose_spec (exists_expAt_fixed_time_package g x₀)).2.2.2

end GeodesicTransport
end Poincare
