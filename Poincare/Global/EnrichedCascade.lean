import Poincare.Global.CartanCascade
import Poincare.Global.GaussLemmaIntegrated
import Poincare.Global.IsometryInstantiate
import Poincare.Global.SpeedPackage

/-!
# Enriched Cartan cascade

This module strengthens the cascade export by keeping the hosted PL base-flow
package attached to the same opaque `α` used by the endpoint-linearized family.
The construction repeats the cascade shrink from the uniform hosted PL flow,
shrinks into the cutoff-one locus, and then exports the half-time margin
`T < ε`.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace EnrichedCascade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- The base-curve fields exported for the same hosted curve used by the cascade. -/
def BaseCurvePackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T ε : ℝ) (a : ℝ≥0) (α : E × E → ℝ → E × E) (v : E) : Prop :=
  let γ : ℝ → E × E := α (extChartAt I x₀ x₀, T⁻¹ • v)
  γ 0 = (extChartAt I x₀ x₀, T⁻¹ • v) ∧
    (∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s))
        (Icc (-ε) ε) s) ∧
    (∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s))
        (Icc (0 : ℝ) T) s) ∧
    (∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s) ∧
    (∀ s ∈ Icc (-ε) ε,
      γ s ∈ closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
    (∀ s ∈ Icc (-ε) ε,
      (γ s).1 ∈ (extChartAt I x₀).target) ∧
    (∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I x₀).target) ∧
    (∀ s ∈ Icc (-ε) ε,
      GeodesicTransport.cutoff (n := 3) x₀ (γ s).1 = 1) ∧
    (∀ s ∈ Icc (0 : ℝ) T,
      ∀ᶠ z' in 𝓝 (γ s).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1) ∧
    (∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀
          (γ s).1 (γ s).2 (γ s).2 =
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v)) ∧
    (γ T).1 = (expAtChartOpenPartialHomeomorph (g := g) x₀) v

/--
The linearized solution-family fields exported at the same hosted base curve,
including the one-sided derivative and initial-velocity variation facts.
-/
def LinearizedFamilyPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T ε : ℝ) (α : E × E → ℝ → E × E) (v : E)
    (Ψ : E → ℝ → E × E) : Prop :=
  let γ : ℝ → E × E := α (extChartAt I x₀ x₀, T⁻¹ • v)
  (∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w)) ∧
    (∀ w : E, ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc (-ε) ε) s) ∧
    (∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc (0 : ℝ) T) s) ∧
    (∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s) ∧
    (∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s)
        (Ψ w s) 0) ∧
    (∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).1
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).2
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
          (T⁻¹ • v + r • (T⁻¹ • w))
          (T⁻¹ • v + r • (T⁻¹ • w))))

/--
One-sided enriched hosted cascade package for a single metric.

The exported time is half of the cutoff-locus PL interval, so the strict
margin `T < ε` is available.  The base curve and all linearized families are
built from the same hosted flow `α`.
-/
theorem exists_shrunk_cutoff_one_strictDeriv_package
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ),
      ∃ T > (0 : ℝ), ∃ ε : ℝ, ∃ hε_pos : 0 < ε,
        ∃ a : ℝ≥0, ∃ α : E × E → ℝ → E × E,
          T < ε ∧
            ∀ v : E, ‖v‖ < ρ →
              v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                BaseCurvePackage g x₀ T ε a α v ∧
                (∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
                  IsPicardLindelof
                    (fun s : ℝ => fun ψ : E × E =>
                      linearizedGeodesicFlowOperator
                        (chartChristoffelField g x₀)
                        (α (extChartAt I x₀ x₀, T⁻¹ • v) s) ψ)
                    (tmin := -ε) (tmax := ε)
                    ⟨(0 : ℝ), by constructor <;> linarith [hε_pos]⟩
                    ((0 : E), (0 : E)) aPL r Lip K →
                  ∃ Ψ : E → ℝ → E × E,
                    ∃ hadd : ∀ w w' : E,
                      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1,
                      ∃ hsmul : ∀ (c : ℝ) (w : E),
                        (Ψ (c • w) T).1 = c • (Ψ w T).1,
                        LinearizedFamilyPackage g x₀ T ε α v Ψ ∧
                          HasStrictFDerivAt
                            (expAtChartOpenPartialHomeomorph (g := g) x₀)
                            (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v) := by
  let e := expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0source : (0 : E) ∈ e.source :=
    zero_mem_expAtChartOpenPartialHomeomorph_source (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0source) with
    ⟨rSource, hrSource_pos, hrSource_sub⟩
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ₀, hτ₀_pos, δ, hδ_pos, ε₀, hε₀_pos, a, α, hα, hexp⟩
  let z₀ : E := extChartAt I x₀ x₀
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
  let T : ℝ := ε / 2
  have hT_pos : 0 < T := by
    dsimp [T]
    exact half_pos hε_pos
  have hT_lt_ε : T < ε := by
    dsimp [T]
    linarith
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
  refine ⟨ρ, hρ_pos, T, hT_pos, ε, hε_pos, a, α, hT_lt_ε, ?_⟩
  intro v hv
  have hvsrc : v ∈ e.source := by
    apply hrSource_sub
    have hvdist : dist v (0 : E) < rSource := by
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
  have hsubε : Icc (-ε) ε ⊆ Icc (-ε₀) ε₀ := by
    intro s hs
    exact ⟨(neg_le_neg hεε₀).trans hs.1, hs.2.trans hεε₀⟩
  have hsub0T : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hε_pos, hs.1], hs.2.trans hTε⟩
  have hαside : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ s ∈ Icc (-ε) ε,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) s))
            (Icc (-ε) ε) s) ∧
        (∀ s ∈ Icc (-ε) ε,
          α (extChartAt I x₀ x₀, v₀) s ∈
            closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
        ∀ s ∈ Icc (-ε) ε,
          (α (extChartAt I x₀ x₀, v₀) s).1 ∈
            (extChartAt I x₀).target := by
    intro v₀ hv₀
    rcases hα v₀ hv₀ with ⟨hα0, hαder, hαmem, hαtarget, _hhom⟩
    exact ⟨hα0, (fun s hs => (hαder s (hsubε hs)).mono hsubε),
      (fun s hs => hαmem s (hsubε hs)),
      (fun s hs => hαtarget s (hsubε hs))⟩
  have hα0_all : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) :=
    fun v₀ hv₀ => (hαside v₀ hv₀).1
  have hαder_all : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) s))
        (Icc (-ε) ε) s :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.1
  have hαmem_all : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      α (extChartAt I x₀ x₀, v₀) s ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.2.1
  have hαtarget_all : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) s).1 ∈ (extChartAt I x₀).target :=
    fun v₀ hv₀ => (hαside v₀ hv₀).2.2.2
  have hcut_locus_all : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) s).1 ∈
        IsometryInstantiate.cutoffOneLocus x₀ := by
    intro v₀ hv₀ s hs
    rcases hα v₀ hv₀ with ⟨hα0_old, hαder_old, hαmem_old, _hαtarget_old, _hhom⟩
    apply hrCut_sub
    have hdist :
        dist (α (extChartAt I x₀ x₀, v₀) s).1 z₀ ≤ (a : ℝ) * |s| := by
      simpa [z₀] using
        plFlowPosition_dist_anchor_le_radius_mul_abs
          (g := g) (x₀ := x₀) (ε := ε₀) (τ := ε)
          (a := a) (α := α) (v₀ := v₀)
          hε_pos.le hεε₀ hα0_old hαder_old hαmem_old hs
    have habs : |s| ≤ ε := abs_le.mpr hs
    have hdistCut : dist (α (extChartAt I x₀ x₀, v₀) s).1 z₀ ≤ rCut := by
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
  let γ : ℝ → E × E := α (extChartAt I x₀ x₀, T⁻¹ • v)
  have hγ0 : γ 0 = (extChartAt I x₀ x₀, T⁻¹ • v) :=
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
      γ s ∈ closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) :=
    hαmem_all (T⁻¹ • v) hv_scaled
  have hγtarget : ∀ s ∈ Icc (-ε) ε,
      (γ s).1 ∈ (extChartAt I x₀).target :=
    hαtarget_all (T⁻¹ • v) hv_scaled
  have hγtarget0T : ∀ s ∈ Icc (0 : ℝ) T,
      (γ s).1 ∈ (extChartAt I x₀).target := by
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
        expAt g x₀ v = (extChartAt I x₀).symm (γ T).1 := by
      simpa [γ, hT_smul] using hexpT
    have htargetT : (γ T).1 ∈ (extChartAt I x₀).target :=
      hγtarget T (hsub0T ⟨hT_pos.le, le_rfl⟩)
    have hchart :
        extChartAt I x₀ (expAt g x₀ v) = (γ T).1 := by
      rw [hexpT']
      exact (extChartAt I x₀).right_inv htargetT
    simpa [expAtChartOpenPartialHomeomorph_coe] using hchart.symm
  have hbase : BaseCurvePackage g x₀ T ε a α v := by
    dsimp [BaseCurvePackage, γ]
    exact ⟨hγ0, hγder, hγder0T, hγAt, hγmem, hγtarget, hγtarget0T,
      hγcut, hγχ0T, hspeed, hendpoint⟩
  refine ⟨by simpa [e] using hvsrc, hbase, ?_⟩
  intro aPL rPL Lip K hr hpl
  have hTmemε : T ∈ Icc (-ε) ε := ⟨by linarith [hε_pos, hT_pos], hTε⟩
  rcases
      _root_.Poincare.LinearizedAdditivity.exists_hosted_rescaled_linearized_solution_family_endpoint_linear
        (g := g) (x₀ := x₀) (γ := γ)
        (ε := ε) (T := T) hε_pos hTmemε hr hpl with
    ⟨Ψ, hΨ0, hΨder, hadd, hsmul⟩
  have hΨder0T : ∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc (0 : ℝ) T) s := by
    intro w s hs
    exact (hΨder w s (hsub0T hs)).mono hsub0T
  have hΨAt : ∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s :=
    IsometryInstantiate.linearizedFlow_hasDerivAt_on_shrunk_Icc
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (a := -ε) (b := ε) (c := 0) (d := T)
      (by linarith [hε_pos]) hT_lt_ε hΨder
  have hflow : ∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt
        (fun r : ℝ =>
          α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s)
        (Ψ w s) 0 := by
    intro w s hs
    exact
      chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := a)
        (α := α) (v := T⁻¹ • v) (w := T⁻¹ • w)
        (Ψ := Ψ w) (t := s) hε_pos hv_scaled
        (by
          intro v₀ hv₀
          exact ⟨hα0_all v₀ hv₀, hαder_all v₀ hv₀, hαmem_all v₀ hv₀⟩)
        (hΨ0 w) (hΨder w) ⟨hs.1, hs.2.trans hTε⟩
  have hodeAt : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) s)) s := by
    intro v₀ hv₀ s hs
    exact
      IsometryInstantiate.hasDerivAt_of_hasDerivWithinAt_larger_Icc
        (hαder_all v₀ hv₀ s ⟨hs.1.le, hs.2.le⟩) hs.1 hs.2
  have hspeedConst : ∀ w : E, ∀ s ∈ Icc (0 : ℝ) T,
      (fun r : ℝ =>
        chartGeodesicMetric g x₀
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).1
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).2
          (α (extChartAt I x₀ x₀, T⁻¹ • v + r • (T⁻¹ • w)) s).2)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ =>
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
          (T⁻¹ • v + r • (T⁻¹ • w))
          (T⁻¹ • v + r • (T⁻¹ • w))) := by
    intro w s hs
    have hsIoo : s ∈ Ioo (-ε) ε :=
      ⟨by linarith [hε_pos, hs.1], lt_of_le_of_lt hs.2 hT_lt_ε⟩
    exact
      chart_initialVelocity_speed_eventuallyEq_initialSpeed_of_constantSpeed
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε)
        (α := α) (z₀ := extChartAt I x₀ x₀)
        (v := T⁻¹ • v) (w := T⁻¹ • w) (t := s)
        hε_pos hv_scaled hα0_all hodeAt hsIoo
  have hlin : LinearizedFamilyPackage g x₀ T ε α v Ψ := by
    dsimp [LinearizedFamilyPackage, γ]
    exact ⟨hΨ0, hΨder, hΨder0T, hΨAt, hflow, hspeedConst⟩
  have hstrict :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v :=
    expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall
      (g := g) (x₀ := x₀) (τ := T) (δ := δ) (ε := ε)
      (a := a) (α := α) (Ψ := Ψ) (v := v)
      hT_pos hε_pos hTε hv_scaled hαside
      (by
        intro v₀ hv₀
        exact hexp v₀ hv₀ T hT_mem_τ₀)
      hΨ0 hΨder hadd hsmul
  exact ⟨Ψ, hadd, hsmul, hlin, hstrict⟩

/--
Source and target enriched cascade package with the same small endpoint ball.

The source and target sides keep separate hosted times, as in
`CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`,
but each side now exports its own strict half-time margin and base package for
the same `α` used by its linearized family.
-/
theorem exists_common_enriched_source_target_cascade
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ Ts > (0 : ℝ), ∃ εs : ℝ, ∃ hεs_pos : 0 < εs,
        ∃ as : ℝ≥0, ∃ αs : E × E → ℝ → E × E,
          Ts < εs ∧
            ∃ Tt > (0 : ℝ), ∃ εt : ℝ, ∃ hεt_pos : 0 < εt,
              ∃ aTgt : ℝ≥0, ∃ αt : E × E → ℝ → E × E,
                Tt < εt ∧
                  ∀ v : E, ‖v‖ < ρ →
                    v ∈
                        (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                      align v ∈
                        (expAtChartOpenPartialHomeomorph
                          (g := roundSphereMetric3) p₀).source ∧
                      BaseCurvePackage g x₀ Ts εs as αs v ∧
                      BaseCurvePackage roundSphereMetric3 p₀ Tt εt aTgt αt (align v) ∧
                      (∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
                        IsPicardLindelof
                          (fun s : ℝ => fun ψ : E × E =>
                            linearizedGeodesicFlowOperator
                              (chartChristoffelField g x₀)
                              (αs (extChartAt I x₀ x₀, Ts⁻¹ • v) s) ψ)
                          (tmin := -εs) (tmax := εs)
                          ⟨(0 : ℝ), by constructor <;> linarith [hεs_pos]⟩
                          ((0 : E), (0 : E)) aPL r Lip K →
                        ∃ Ψ : E → ℝ → E × E,
                          ∃ hadd : ∀ w w' : E,
                            (Ψ (w + w') Ts).1 = (Ψ w Ts).1 + (Ψ w' Ts).1,
                            ∃ hsmul : ∀ (c : ℝ) (w : E),
                              (Ψ (c • w) Ts).1 = c • (Ψ w Ts).1,
                              LinearizedFamilyPackage g x₀ Ts εs αs v Ψ ∧
                                HasStrictFDerivAt
                                  (expAtChartOpenPartialHomeomorph (g := g) x₀)
                                  (linearizedEndpointCLM (Ψ := Ψ) Ts hadd hsmul) v) ∧
                      (∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
                        IsPicardLindelof
                          (fun s : ℝ => fun ψ : E × E =>
                            linearizedGeodesicFlowOperator
                              (chartChristoffelField roundSphereMetric3 p₀)
                              (αt (extChartAt I p₀ p₀, Tt⁻¹ • align v) s) ψ)
                          (tmin := -εt) (tmax := εt)
                          ⟨(0 : ℝ), by constructor <;> linarith [hεt_pos]⟩
                          ((0 : E), (0 : E)) aPL r Lip K →
                        ∃ Ψ : E → ℝ → E × E,
                          ∃ hadd : ∀ w w' : E,
                            (Ψ (w + w') Tt).1 = (Ψ w Tt).1 + (Ψ w' Tt).1,
                            ∃ hsmul : ∀ (c : ℝ) (w : E),
                              (Ψ (c • w) Tt).1 = c • (Ψ w Tt).1,
                              LinearizedFamilyPackage roundSphereMetric3 p₀
                                Tt εt αt (align v) Ψ ∧
                                HasStrictFDerivAt
                                  (expAtChartOpenPartialHomeomorph
                                    (g := roundSphereMetric3) p₀)
                                  (linearizedEndpointCLM (Ψ := Ψ) Tt hadd hsmul)
                                  (align v)) := by
  rcases exists_shrunk_cutoff_one_strictDeriv_package (g := g) (x₀ := x₀) with
    ⟨ρs, hρs_pos, Ts, hTs_pos, εs, hεs_pos, as, αs, hTsεs, hsource⟩
  rcases
      exists_shrunk_cutoff_one_strictDeriv_package
        (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨ρt, hρt_pos, Tt, hTt_pos, εt, hεt_pos, aTgt, αt, hTtεt, htarget⟩
  let C : ℝ := ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ + 1
  let ρ : ℝ := min ρs (ρt / C) / 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hρt_div_pos : 0 < ρt / C := div_pos hρt_pos hC_pos
  have hmin_pos : 0 < min ρs (ρt / C) := lt_min hρs_pos hρt_div_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hmin_pos
  have hρ_le_ρs : ρ ≤ ρs := by
    dsimp [ρ]
    exact (by linarith [hmin_pos.le] : min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
      (min_le_left ρs (ρt / C))
  have hρ_le_ρt_div : ρ ≤ ρt / C := by
    dsimp [ρ]
    exact (by linarith [hmin_pos.le] : min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
      (min_le_right ρs (ρt / C))
  refine ⟨ρ, hρ_pos, Ts, hTs_pos, εs, hεs_pos, as, αs, hTsεs,
    Tt, hTt_pos, εt, hεt_pos, aTgt, αt, hTtεt, ?_⟩
  intro v hv
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hρ_le_ρs
  have halign_norm : ‖align v‖ < ρt := by
    have hnorm_bound :
        ‖align v‖ ≤ ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (align.toContinuousLinearEquiv : E →L[ℝ] E) v
    have hCnorm :
        ‖(align.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hρ_le_ρt_div
    have hCmul : C * ‖v‖ < ρt := by
      calc
        C * ‖v‖ < C * (ρt / C) := mul_lt_mul_of_pos_left hv_div hC_pos
        _ = ρt := by field_simp [ne_of_gt hC_pos]
    exact lt_of_le_of_lt (hnorm_bound.trans hCnorm) hCmul
  rcases hsource v hv_source_norm with ⟨hvsrc, hbaseS, hlinS⟩
  rcases htarget (align v) halign_norm with ⟨hvtgt, hbaseT, hlinT⟩
  exact ⟨hvsrc, hvtgt, hbaseS, hbaseT, hlinS, hlinT⟩

end EnrichedCascade
end Poincare
