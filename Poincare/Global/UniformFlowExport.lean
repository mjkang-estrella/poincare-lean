import Poincare.Global.UniformShrink

/-!
# Uniform-flow exports for the aligned selector

This module replays the common-time base-flow construction just far enough to
keep the hosted uniform-flow facts (`hα0`, `hαder`, `hαmem`, `hαtarget`,
`hexp`) in the public result.  Those facts then feed
`IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow`
on the ball-uniform linearized PL intervals from `UniformShrink`.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformFlowExport

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/--
Single-side base package with the underlying hosted uniform-flow fields kept
public.  This is the base-flow part of `CommonTime`, without hiding the
`δ, hα0, hαder, hαmem, hαtarget, hexp` facts needed by `IntervalAlign`.
-/
theorem exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ε : ℝ, ∃ _hε_pos : 0 < ε, ∃ δ : ℝ, ∃ _hδ_pos : 0 < δ,
      ∃ a : ℝ≥0, ∃ α : E3 × E3 → ℝ → E3 × E3,
        (∀ v₀ : E3, ‖v₀‖ < δ →
          α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀)) ∧
        (∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I3 x₀ x₀, v₀) s))
            (Icc (-ε) ε) s) ∧
        (∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
          α (extChartAt I3 x₀ x₀, v₀) s ∈
            closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ)) ∧
        (∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
          (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target) ∧
        (∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (0 : ℝ) ε,
          expAt g x₀ (s • v₀) =
            (extChartAt I3 x₀).symm (α (extChartAt I3 x₀ x₀, v₀) s).1) ∧
        ∀ T : ℝ, 0 < T → T < ε →
          ∃ ρ > (0 : ℝ),
            ∀ v : E3, ‖v‖ < ρ →
              v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                ‖T⁻¹ • v‖ < δ ∧
                EnrichedCascade.BaseCurvePackage g x₀ T ε a α v := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0source : (0 : E3) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0source) with
    ⟨rSource, hrSource_pos, hrSource_sub⟩
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ₀, hτ₀_pos, δ, hδ_pos, ε₀, hε₀_pos, a, α, hα, hexp⟩
  let z₀ : E3 := extChartAt I3 x₀ x₀
  have hcut_locus_nhds :
      IsometryInstantiate.cutoffOneLocus x₀ ∈ 𝓝 z₀ := by
    simpa [z₀] using IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor (x₀ := x₀)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hcut_locus_nhds with
    ⟨rCut, hrCut_pos, hrCut_sub⟩
  let κ : ℝ := rCut / (2 * ((a : ℝ) + 1))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    positivity
  let ε : ℝ := min τ₀ (min ε₀ κ)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hτ₀_pos (lt_min hε₀_pos hκ_pos)
  have hετ₀ : ε ≤ τ₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεκ : ε ≤ κ := by
    dsimp [ε]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsubε : Icc (-ε) ε ⊆ Icc (-ε₀) ε₀ := by
    intro s hs
    exact ⟨(neg_le_neg hεε₀).trans hs.1, hs.2.trans hεε₀⟩
  have hαside : ∀ v₀ : E3, ‖v₀‖ < δ →
      α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀) ∧
        (∀ s ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I3 x₀ x₀, v₀) s))
            (Icc (-ε) ε) s) ∧
        (∀ s ∈ Icc (-ε) ε,
          α (extChartAt I3 x₀ x₀, v₀) s ∈
            closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ)) ∧
        ∀ s ∈ Icc (-ε) ε,
          (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈
            (extChartAt I3 x₀).target := by
    intro v₀ hv₀
    rcases hα v₀ hv₀ with ⟨hα0, hαder, hαmem, hαtarget, _hhom⟩
    exact ⟨hα0, (fun s hs => (hαder s (hsubε hs)).mono hsubε),
      (fun s hs => hαmem s (hsubε hs)),
      (fun s hs => hαtarget s (hsubε hs))⟩
  have hα0_all : ∀ v₀ : E3, ‖v₀‖ < δ →
      α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀) :=
    fun v₀ hv₀ => (hαside v₀ hv₀).1
  have hαder_all : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v₀) s))
        (Icc (-ε) ε) s :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.1
  have hαmem_all : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      α (extChartAt I3 x₀ x₀, v₀) s ∈
        closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ) :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.2.1
  have hαtarget_all : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.2.2
  have hexp_all : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (0 : ℝ) ε,
      expAt g x₀ (s • v₀) =
        (extChartAt I3 x₀).symm (α (extChartAt I3 x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexp v₀ hv₀ s ⟨hs.1, hs.2.trans hετ₀⟩
  have hcut_locus_all : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I3 x₀ x₀, v₀) s).1 ∈
        IsometryInstantiate.cutoffOneLocus x₀ := by
    intro v₀ hv₀ s hs
    rcases hα v₀ hv₀ with ⟨hα0_old, hαder_old, hαmem_old, _hαtarget_old, _hhom⟩
    apply hrCut_sub
    have hdist :
        dist (α (extChartAt I3 x₀ x₀, v₀) s).1 z₀ ≤ (a : ℝ) * |s| := by
      simpa [z₀] using
        plFlowPosition_dist_anchor_le_radius_mul_abs
          (g := g) (x₀ := x₀) (ε := ε₀) (τ := ε)
          (a := a) (α := α) (v₀ := v₀)
          hε_pos.le hεε₀ hα0_old hαder_old hαmem_old hs
    have habs : |s| ≤ ε := abs_le.mpr hs
    have hdistCut : dist (α (extChartAt I3 x₀ x₀, v₀) s).1 z₀ ≤ rCut := by
      have ha_nonneg : 0 ≤ (a : ℝ) := NNReal.coe_nonneg a
      have hmul_le : (a : ℝ) * |s| ≤ (a : ℝ) * ε :=
        mul_le_mul_of_nonneg_left habs ha_nonneg
      have hε_le : (a : ℝ) * ε ≤ rCut := by
        calc
          (a : ℝ) * ε ≤ (a : ℝ) * κ :=
            mul_le_mul_of_nonneg_left hεκ ha_nonneg
          _ = (a : ℝ) * (rCut / (2 * ((a : ℝ) + 1))) := rfl
          _ ≤ rCut := by
            have hfrac_le_one : (a : ℝ) / ((a : ℝ) + 1) ≤ 1 := by
              have hden' : 0 < (a : ℝ) + 1 := by positivity
              rw [div_le_one hden']
              linarith
            calc
              (a : ℝ) * (rCut / (2 * ((a : ℝ) + 1)))
                  = (rCut / 2) * ((a : ℝ) / ((a : ℝ) + 1)) := by
                    have hden' : ((a : ℝ) + 1) ≠ 0 := by positivity
                    field_simp [hden']
              _ ≤ (rCut / 2) * 1 := by
                    gcongr
              _ ≤ rCut := by linarith
      exact hdist.trans (hmul_le.trans hε_le)
    simpa [Metric.mem_closedBall] using hdistCut
  refine
    ⟨ε, hε_pos, δ, hδ_pos, a, α, hα0_all, hαder_all, hαmem_all,
      hαtarget_all, hexp_all, ?_⟩
  intro T hT_pos hT_lt_ε
  have hTε : T ≤ ε := le_of_lt hT_lt_ε
  have hTτ₀ : T ≤ τ₀ := hTε.trans hετ₀
  have hT_mem_τ₀ : T ∈ Icc (0 : ℝ) τ₀ := ⟨hT_pos.le, hTτ₀⟩
  let ρ : ℝ := min rSource (T * δ / 2) / 2
  have hTδ_pos : 0 < T * δ / 2 := by positivity
  have hmin_pos : 0 < min rSource (T * δ / 2) :=
    lt_min hrSource_pos hTδ_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hmin_pos
  have hρ_le_min : ρ ≤ min rSource (T * δ / 2) := by
    dsimp [ρ]
    linarith [hmin_pos.le]
  have hρ_le_source : ρ ≤ rSource :=
    hρ_le_min.trans (min_le_left rSource (T * δ / 2))
  have hρ_le_Tδ : ρ ≤ T * δ / 2 :=
    hρ_le_min.trans (min_le_right rSource (T * δ / 2))
  refine ⟨ρ, hρ_pos, ?_⟩
  intro v hv
  have hvsrc : v ∈ e.source := by
    apply hrSource_sub
    have hvdist : dist v (0 : E3) < rSource := by
      simpa [dist_eq_norm] using hv.trans_le hρ_le_source
    exact Metric.mem_ball.mpr hvdist
  have hT_inv_pos : 0 < T⁻¹ := inv_pos.mpr hT_pos
  have hv_scaled : ‖T⁻¹ • v‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT_inv_pos]
    have hvTδ : ‖v‖ < T * δ / 2 := hv.trans_le hρ_le_Tδ
    have hmul : T⁻¹ * (T * δ / 2) = δ / 2 := by
      field_simp [ne_of_gt hT_pos]
    calc
      T⁻¹ * ‖v‖ < T⁻¹ * (T * δ / 2) :=
        mul_lt_mul_of_pos_left hvTδ hT_inv_pos
      _ = δ / 2 := hmul
      _ < δ := by linarith
  have hsub0T : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hε_pos, hs.1], hs.2.trans hTε⟩
  let γ : ℝ → E3 × E3 := α (extChartAt I3 x₀ x₀, T⁻¹ • v)
  have hγ0 : γ 0 = (extChartAt I3 x₀ x₀, T⁻¹ • v) :=
    hα0_all (T⁻¹ • v) hv_scaled
  have hγder : ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s))
        (Icc (-ε) ε) s :=
    hαder_all (T⁻¹ • v) hv_scaled
  have hγder0T : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s))
        (Icc (0 : ℝ) T) s := by
    intro s hs
    exact (hγder s (hsub0T hs)).mono hsub0T
  have hγAt : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s :=
    IsometryInstantiate.geodesicFlow_hasDerivAt_on_shrunk_Icc
      (g := g) (x₀ := x₀) (γ := γ)
      (a := -ε) (b := ε) (c := 0) (d := T)
      (by linarith [hε_pos]) hT_lt_ε hγder
  have hγmem : ∀ s ∈ Icc (-ε) ε,
      γ s ∈ closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ) :=
    hαmem_all (T⁻¹ • v) hv_scaled
  have hγtarget : ∀ s ∈ Icc (-ε) ε,
      (γ s).1 ∈ (extChartAt I3 x₀).target :=
    hαtarget_all (T⁻¹ • v) hv_scaled
  have hγtarget0T : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I3 x₀).target := by
    intro s hs
    exact hγtarget s (hsub0T hs)
  have hγχ : ∀ s ∈ Icc (-ε) ε,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1 := by
    intro s hs
    exact
      IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
        (x₀ := x₀) (hcut_locus_all (T⁻¹ • v) hv_scaled s hs)
  have hγcut : ∀ s ∈ Icc (-ε) ε,
      cutoff (n := 3) x₀ (γ s).1 = 1 := by
    intro s hs
    exact (hγχ s hs).self_of_nhds
  have hγχ0T : ∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1 := by
    intro s hs
    exact hγχ s (hsub0T hs)
  have hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀
          (γ s).1 (γ s).2 (γ s).2 =
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) := by
    intro s hs
    exact
      SpeedPackage.hosted_source_curve_speedValue_eq_anchor_on_shrunk_Icc
        (g := g) (x₀ := x₀) (T := T) (ε := ε) hε_pos
        (α := α) (v := v) hγ0 hγder hγcut
        (by linarith [hε_pos]) hT_lt_ε hs
  have hT_smul : T • (T⁻¹ • v) = v := by
    rw [smul_smul]
    have hcoef : T * T⁻¹ = 1 := by field_simp [ne_of_gt hT_pos]
    simp [hcoef]
  have hendpoint : (γ T).1 = (expAtChartOpenPartialHomeomorph (g := g) x₀) v := by
    have hexpT :=
      hexp (T⁻¹ • v) hv_scaled T hT_mem_τ₀
    have hexpT' :
        expAt g x₀ v = (extChartAt I3 x₀).symm (γ T).1 := by
      simpa [γ, hT_smul] using hexpT
    have htargetT : (γ T).1 ∈ (extChartAt I3 x₀).target :=
      hγtarget T (hsub0T ⟨hT_pos.le, le_rfl⟩)
    have hchart :
        extChartAt I3 x₀ (expAt g x₀ v) = (γ T).1 := by
      rw [hexpT']
      exact (extChartAt I3 x₀).right_inv htargetT
    simpa [expAtChartOpenPartialHomeomorph_coe] using hchart.symm
  have hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε a α v := by
    dsimp [EnrichedCascade.BaseCurvePackage, γ]
    exact ⟨hγ0, hγder, hγder0T, hγAt, hγmem, hγtarget, hγtarget0T,
      hγcut, hγχ0T, hspeed, hendpoint⟩
  exact ⟨by simpa [e] using hvsrc, hv_scaled, hbase⟩

/--
Common source/target time where the five hosted uniform-flow fields are
exported on the ball-uniform linearized PL intervals and the enriched selector
fires on both sides.
-/
theorem exists_common_time_with_uniform_flow_exports_and_enriched_selectors
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ T > (0 : ℝ),
        ∃ εs : ℝ, ∃ _hεs_pos : 0 < εs,
          ∃ as : ℝ≥0, ∃ αs : E3 × E3 → ℝ → E3 × E3,
            ∃ εlin_source : ℝ, ∃ hεlin_source_pos : 0 < εlin_source,
              εlin_source ≤ εs ∧ T < εlin_source ∧
                ∃ δs : ℝ, ∃ _hδs_pos : 0 < δs,
                  ∃ _hα0S : ∀ v₀ : E3, ‖v₀‖ < δs →
                    αs (extChartAt I3 x₀ x₀, v₀) 0 =
                      (extChartAt I3 x₀ x₀, v₀),
                  ∃ _hαderS : ∀ v₀ : E3, ‖v₀‖ < δs →
                    ∀ s ∈ Icc (-εlin_source) εlin_source,
                      HasDerivWithinAt (αs (extChartAt I3 x₀ x₀, v₀))
                        (geodesicFlowField (chartChristoffelField g x₀)
                          (αs (extChartAt I3 x₀ x₀, v₀) s))
                        (Icc (-εlin_source) εlin_source) s,
                  ∃ _hαmemS : ∀ v₀ : E3, ‖v₀‖ < δs →
                    ∀ s ∈ Icc (-εlin_source) εlin_source,
                      αs (extChartAt I3 x₀ x₀, v₀) s ∈
                        closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (as : ℝ),
                  ∃ _hαtargetS : ∀ v₀ : E3, ‖v₀‖ < δs →
                    ∀ s ∈ Icc (-εlin_source) εlin_source,
                      (αs (extChartAt I3 x₀ x₀, v₀) s).1 ∈
                        (extChartAt I3 x₀).target,
                  ∃ _hexpS : ∀ v₀ : E3, ‖v₀‖ < δs →
                    ∀ s ∈ Icc (0 : ℝ) εlin_source,
                      expAt g x₀ (s • v₀) =
                        (extChartAt I3 x₀).symm
                          (αs (extChartAt I3 x₀ x₀, v₀) s).1,
                  ∃ aPLS rS LipS KS : ℝ≥0, 0 < (rS : ℝ) ∧
                    ∃ εt : ℝ, ∃ _hεt_pos : 0 < εt,
                      ∃ aTgt : ℝ≥0, ∃ αt : E3 × E3 → ℝ → E3 × E3,
                        ∃ εlin_target : ℝ, ∃ hεlin_target_pos : 0 < εlin_target,
                          εlin_target ≤ εt ∧ T < εlin_target ∧
                            ∃ δt : ℝ, ∃ _hδt_pos : 0 < δt,
                              ∃ _hα0T : ∀ v₀ : E3, ‖v₀‖ < δt →
                                αt (extChartAt I3 p₀ p₀, v₀) 0 =
                                  (extChartAt I3 p₀ p₀, v₀),
                              ∃ _hαderT : ∀ v₀ : E3, ‖v₀‖ < δt →
                                ∀ s ∈ Icc (-εlin_target) εlin_target,
                                  HasDerivWithinAt
                                    (αt (extChartAt I3 p₀ p₀, v₀))
                                    (geodesicFlowField
                                      (chartChristoffelField roundSphereMetric3 p₀)
                                      (αt (extChartAt I3 p₀ p₀, v₀) s))
                                    (Icc (-εlin_target) εlin_target) s,
                              ∃ _hαmemT : ∀ v₀ : E3, ‖v₀‖ < δt →
                                ∀ s ∈ Icc (-εlin_target) εlin_target,
                                  αt (extChartAt I3 p₀ p₀, v₀) s ∈
                                    closedBall (extChartAt I3 p₀ p₀, (0 : E3))
                                      (aTgt : ℝ),
                              ∃ _hαtargetT : ∀ v₀ : E3, ‖v₀‖ < δt →
                                ∀ s ∈ Icc (-εlin_target) εlin_target,
                                  (αt (extChartAt I3 p₀ p₀, v₀) s).1 ∈
                                    (extChartAt I3 p₀).target,
                              ∃ _hexpT : ∀ v₀ : E3, ‖v₀‖ < δt →
                                ∀ s ∈ Icc (0 : ℝ) εlin_target,
                                  expAt roundSphereMetric3 p₀ (s • v₀) =
                                    (extChartAt I3 p₀).symm
                                      (αt (extChartAt I3 p₀ p₀, v₀) s).1,
                              ∃ aPLT rT LipT KT : ℝ≥0, 0 < (rT : ℝ) ∧
                                ∀ v : E3, ‖v‖ < ρ →
                                  v ∈
                                      (expAtChartOpenPartialHomeomorph
                                        (g := g) x₀).source ∧
                                    align v ∈
                                      (expAtChartOpenPartialHomeomorph
                                        (g := roundSphereMetric3) p₀).source ∧
                                    ‖T⁻¹ • v‖ < δs ∧
                                    ‖T⁻¹ • align v‖ < δt ∧
                                    EnrichedCascade.BaseCurvePackage g x₀
                                      T εs as αs v ∧
                                    EnrichedCascade.BaseCurvePackage roundSphereMetric3
                                      p₀ T εt aTgt αt (align v) ∧
                                    IsPicardLindelof
                                      (fun s : ℝ => fun ψ : E3 × E3 =>
                                        linearizedGeodesicFlowOperator
                                          (chartChristoffelField g x₀)
                                          (αs
                                            (extChartAt I3 x₀ x₀, T⁻¹ • v) s)
                                          ψ)
                                      (tmin := -εlin_source)
                                      (tmax := εlin_source)
                                      ⟨(0 : ℝ), by
                                        constructor <;> linarith [hεlin_source_pos]⟩
                                      ((0 : E3), (0 : E3)) aPLS rS LipS KS ∧
                                    (∃ Ψs : E3 → ℝ → E3 × E3,
                                      ∃ hadds : ∀ w w' : E3,
                                        (Ψs (w + w') T).1 =
                                          (Ψs w T).1 + (Ψs w' T).1,
                                      ∃ hsmuls : ∀ (c : ℝ) (w : E3),
                                        (Ψs (c • w) T).1 = c • (Ψs w T).1,
                                        EnrichedCascade.LinearizedFamilyPackage
                                          g x₀ T εlin_source αs v Ψs ∧
                                          HasStrictFDerivAt
                                            (expAtChartOpenPartialHomeomorph
                                              (g := g) x₀)
                                            (linearizedEndpointCLM
                                              (Ψ := Ψs) T hadds hsmuls) v ∧
                                          (Ψs v T).1 =
                                            T •
                                              (αs
                                                (extChartAt I3 x₀ x₀,
                                                  T⁻¹ • v) T).2) ∧
                                    IsPicardLindelof
                                      (fun s : ℝ => fun ψ : E3 × E3 =>
                                        linearizedGeodesicFlowOperator
                                          (chartChristoffelField
                                            roundSphereMetric3 p₀)
                                          (αt
                                            (extChartAt I3 p₀ p₀,
                                              T⁻¹ • align v) s)
                                          ψ)
                                      (tmin := -εlin_target)
                                      (tmax := εlin_target)
                                      ⟨(0 : ℝ), by
                                        constructor <;> linarith [hεlin_target_pos]⟩
                                      ((0 : E3), (0 : E3)) aPLT rT LipT KT ∧
                                    ∃ Ψt : E3 → ℝ → E3 × E3,
                                      ∃ haddt : ∀ w w' : E3,
                                        (Ψt (w + w') T).1 =
                                          (Ψt w T).1 + (Ψt w' T).1,
                                      ∃ hsmult : ∀ (c : ℝ) (w : E3),
                                        (Ψt (c • w) T).1 = c • (Ψt w T).1,
                                        EnrichedCascade.LinearizedFamilyPackage
                                          roundSphereMetric3 p₀ T εlin_target
                                          αt (align v) Ψt ∧
                                          HasStrictFDerivAt
                                            (expAtChartOpenPartialHomeomorph
                                              (g := roundSphereMetric3) p₀)
                                            (linearizedEndpointCLM
                                              (Ψ := Ψt) T haddt hsmult)
                                            (align v) ∧
                                          (Ψt (align v) T).1 =
                                            T •
                                              (αt
                                                (extChartAt I3 p₀ p₀,
                                                  T⁻¹ • align v) T).2 := by
  rcases
      exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (g := g) (x₀ := x₀) with
    ⟨εs, hεs_pos, δs, hδs_pos, as, αs, hα0S_full, hαderS_full,
      hαmemS_full, hαtargetS_full, hexpS_full, hsourceT⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (g := g) (x₀ := x₀) hεs_pos as with
    ⟨εlinS, hεlinS_pos, hεlinS_le, aPLS, rS, LipS, KS, hrS, hplS_uniform⟩
  rcases
      exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨εt, hεt_pos, δt, hδt_pos, aTgt, αt, hα0T_full, hαderT_full,
      hαmemT_full, hαtargetT_full, hexpT_full, htargetT⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) hεt_pos
        aTgt with
    ⟨εlinT, hεlinT_pos, hεlinT_le, aPLT, rT, LipT, KT, hrT, hplT_uniform⟩
  let η : ℝ := min εs (min εt (min εlinS εlinT))
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hεs_pos (lt_min hεt_pos (lt_min hεlinS_pos hεlinT_pos))
  let T : ℝ := η / 2
  have hT_pos : 0 < T := by
    dsimp [T]
    exact half_pos hη_pos
  have hT_lt_η : T < η := by
    dsimp [T]
    linarith [hη_pos]
  have hη_le_εs : η ≤ εs := by
    dsimp [η]
    exact min_le_left _ _
  have hη_le_εt : η ≤ εt := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hη_le_εlinS : η ≤ εlinS := by
    dsimp [η]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hη_le_εlinT : η ≤ εlinT := by
    dsimp [η]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hT_lt_εs : T < εs := lt_of_lt_of_le hT_lt_η hη_le_εs
  have hT_lt_εt : T < εt := lt_of_lt_of_le hT_lt_η hη_le_εt
  have hT_lt_εlinS : T < εlinS := lt_of_lt_of_le hT_lt_η hη_le_εlinS
  have hT_lt_εlinT : T < εlinT := lt_of_lt_of_le hT_lt_η hη_le_εlinT
  rcases hsourceT T hT_pos hT_lt_εs with ⟨ρs, hρs_pos, hsource⟩
  rcases htargetT T hT_pos hT_lt_εt with ⟨ρt, hρt_pos, htarget⟩
  let C : ℝ := ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ + 1
  let ρ : ℝ := min ρs (ρt / C) / 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hρt_div_pos : 0 < ρt / C := div_pos hρt_pos hC_pos
  have hminρ_pos : 0 < min ρs (ρt / C) := lt_min hρs_pos hρt_div_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hminρ_pos
  have hρ_le_ρs : ρ ≤ ρs := by
    dsimp [ρ]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_left ρs (ρt / C))
  have hρ_le_ρt_div : ρ ≤ ρt / C := by
    dsimp [ρ]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_right ρs (ρt / C))
  have hsubS : Icc (-εlinS) εlinS ⊆ Icc (-εs) εs := by
    intro s hs
    exact ⟨(neg_le_neg hεlinS_le).trans hs.1, hs.2.trans hεlinS_le⟩
  have hαderS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        HasDerivWithinAt (αs (extChartAt I3 x₀ x₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (αs (extChartAt I3 x₀ x₀, v₀) s))
          (Icc (-εlinS) εlinS) s := by
    intro v₀ hv₀ s hs
    exact (hαderS_full v₀ hv₀ s (hsubS hs)).mono hsubS
  have hαmemS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        αs (extChartAt I3 x₀ x₀, v₀) s ∈
          closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (as : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemS_full v₀ hv₀ s (hsubS hs)
  have hαtargetS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        (αs (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetS_full v₀ hv₀ s (hsubS hs)
  have hexpS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (0 : ℝ) εlinS,
        expAt g x₀ (s • v₀) =
          (extChartAt I3 x₀).symm
            (αs (extChartAt I3 x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpS_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinS_le⟩
  have hsubT : Icc (-εlinT) εlinT ⊆ Icc (-εt) εt := by
    intro s hs
    exact ⟨(neg_le_neg hεlinT_le).trans hs.1, hs.2.trans hεlinT_le⟩
  have hαderT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        HasDerivWithinAt (αt (extChartAt I3 p₀ p₀, v₀))
          (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
            (αt (extChartAt I3 p₀ p₀, v₀) s))
          (Icc (-εlinT) εlinT) s := by
    intro v₀ hv₀ s hs
    exact (hαderT_full v₀ hv₀ s (hsubT hs)).mono hsubT
  have hαmemT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        αt (extChartAt I3 p₀ p₀, v₀) s ∈
          closedBall (extChartAt I3 p₀ p₀, (0 : E3)) (aTgt : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemT_full v₀ hv₀ s (hsubT hs)
  have hαtargetT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        (αt (extChartAt I3 p₀ p₀, v₀) s).1 ∈ (extChartAt I3 p₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetT_full v₀ hv₀ s (hsubT hs)
  have hexpT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (0 : ℝ) εlinT,
        expAt roundSphereMetric3 p₀ (s • v₀) =
          (extChartAt I3 p₀).symm
            (αt (extChartAt I3 p₀ p₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpT_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinT_le⟩
  refine
    ⟨ρ, hρ_pos, T, hT_pos, εs, hεs_pos, as, αs, εlinS, hεlinS_pos,
      hεlinS_le, hT_lt_εlinS, δs, hδs_pos, hα0S_full, hαderS,
      hαmemS, hαtargetS, hexpS, aPLS, rS, LipS, KS, hrS,
      εt, hεt_pos, aTgt, αt, εlinT, hεlinT_pos, hεlinT_le,
      hT_lt_εlinT, δt, hδt_pos, hα0T_full, hαderT, hαmemT,
      hαtargetT, hexpT, aPLT, rT, LipT, KT, hrT, ?_⟩
  intro v hv
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hρ_le_ρs
  have halign_norm : ‖align v‖ < ρt := by
    have hnorm_bound :
        ‖align v‖ ≤ ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (align.toContinuousLinearEquiv : E3 →L[ℝ] E3) v
    have hCnorm :
        ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hρ_le_ρt_div
    have hCmul : C * ‖v‖ < ρt := by
      calc
        C * ‖v‖ < C * (ρt / C) := mul_lt_mul_of_pos_left hv_div hC_pos
        _ = ρt := by field_simp [ne_of_gt hC_pos]
    exact lt_of_le_of_lt (hnorm_bound.trans hCnorm) hCmul
  rcases hsource v hv_source_norm with ⟨hvsrc, hvscaledS, hbaseS⟩
  rcases htarget (align v) halign_norm with ⟨hvtgt, hvscaledT, hbaseT⟩
  have hplS := hplS_uniform (T := T) (α := αs) (v := v) hbaseS
  have hplT := hplT_uniform (T := T) (α := αt) (v := align v) hbaseT
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (g := g) (x₀ := x₀) (δ := δs) (ε := εlinS) (T := T)
        (a := as) (α := αs) (v := v)
        hεlinS_pos hT_pos hT_lt_εlinS hvscaledS hα0S_full hαderS hαmemS
        hαtargetS hexpS hrS hplS with
    ⟨Ψs, hadds, hsmuls, hlinS, hstrictS, hRayS⟩
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀)
        (δ := δt) (ε := εlinT) (T := T) (a := aTgt) (α := αt)
        (v := align v) hεlinT_pos hT_pos hT_lt_εlinT hvscaledT hα0T_full
        hαderT hαmemT hαtargetT hexpT hrT hplT with
    ⟨Ψt, haddt, hsmult, hlinT, hstrictT, hRayT⟩
  exact
    ⟨hvsrc, hvtgt, hvscaledS, hvscaledT, hbaseS, hbaseT, hplS,
      ⟨Ψs, hadds, hsmuls, hlinS, hstrictS, hRayS⟩,
      hplT, Ψt, haddt, hsmult, hlinT, hstrictT, hRayT⟩

end UniformFlowExport
end Poincare
