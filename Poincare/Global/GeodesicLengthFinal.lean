import Poincare.Global.GeodesicLength
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Final local geodesic length estimate

This module shrinks the fixed-time `expAt` Picard-Lindelof package once more:
on the smaller interval the chart positions stay in the cutoff-`1` region.
That removes the remaining hypothesis from the length-integrand bridge and
gives the constant-speed path-length formula and local distance estimate.
-/

noncomputable section

open Bundle Set Metric MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The blended chart metric is nonnegative on diagonal entries. -/
theorem chartGeodesicMetric_self_nonneg
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (z v : E) :
    0 ≤ chartGeodesicMetric g x₀ z v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt
      (CovariantDerivative.blendedChartMetric_posDef
        (cutoff (n := n) x₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (cutoff_nonneg (n := n) x₀ z)
        (cutoff_le_one (n := n) x₀ z)
        (cutoff_support_invertible (n := n) x₀ z) hv)

/--
If a PL flow state remains in a product closed ball of radius `a`, then the
position component moves from the anchor by at most `a * |s|` on any smaller
closed interval.
-/
theorem plFlowPosition_dist_anchor_le_radius_mul_abs
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε τ : ℝ} {a : ℝ≥0} {α : E × E → ℝ → E × E} {v₀ : E}
    (hτ_nonneg : 0 ≤ τ) (hτε : τ ≤ ε)
    (hα0 : α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαmem : ∀ t ∈ Icc (-ε) ε,
      α (extChartAt I x₀ x₀, v₀) t ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ))
    {s : ℝ} (hs : s ∈ Icc (-τ) τ) :
    dist (α (extChartAt I x₀ x₀, v₀) s).1 (extChartAt I x₀ x₀) ≤
      (a : ℝ) * |s| := by
  let z : ℝ → E := fun t => (α (extChartAt I x₀ x₀, v₀) t).1
  let u : ℝ → E := fun t => (α (extChartAt I x₀ x₀, v₀) t).2
  have hsub : Icc (-τ) τ ⊆ Icc (-ε) ε := by
    intro r hr
    exact ⟨(neg_le_neg hτε).trans hr.1, hr.2.trans hτε⟩
  have hder : ∀ r ∈ Icc (-τ) τ, HasDerivWithinAt z (u r) (Icc (-τ) τ) r := by
    intro r hr
    have hstate :
        HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (α (extChartAt I x₀ x₀, v₀) r))
          (Icc (-τ) τ) r :=
      (hαder r (hsub hr)).mono hsub
    have hfst := hstate.hasFDerivWithinAt.fst.hasDerivWithinAt
    simpa [z, u, geodesicFlowField] using hfst
  have hbound : ∀ r ∈ Icc (-τ) τ, ‖u r‖ ≤ (a : ℝ) := by
    intro r hr
    have hmem := hαmem r (hsub hr)
    have hprod :
        α (extChartAt I x₀ x₀, v₀) r ∈
          closedBall (extChartAt I x₀ x₀) (a : ℝ) ×ˢ
            closedBall (0 : E) (a : ℝ) := by
      simpa [closedBall_prod_same] using hmem
    simpa [u, mem_closedBall, dist_eq_norm] using hprod.2
  have h0mem : (0 : ℝ) ∈ Icc (-τ) τ := by
    exact ⟨by linarith, hτ_nonneg⟩
  have hmvt :
      ‖z s - z 0‖ ≤ (a : ℝ) * ‖s - 0‖ :=
    (convex_Icc (-τ) τ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (𝕜 := ℝ) hder hbound h0mem hs
  have hz0 : z 0 = extChartAt I x₀ x₀ := by
    change (α (extChartAt I x₀ x₀, v₀) 0).1 = extChartAt I x₀ x₀
    rw [hα0]
  have hmvt' : ‖z s - extChartAt I x₀ x₀‖ ≤ (a : ℝ) * |s| := by
    simpa [hz0, Real.norm_eq_abs] using hmvt
  simpa [z, dist_eq_norm] using hmvt'

/--
The fixed `expAt` PL flow can be uniformly shrunk so that its chart positions
remain in the cutoff-`1` region on the whole symmetric flow interval.
-/
theorem expAt_uniform_pl_flow_cutoff_one_eq_on_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ a : ℝ≥0,
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ s ∈ Icc (-τ) τ,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) s))
                (Icc (-τ) τ) s) ∧
            (∀ s ∈ Icc (-τ) τ,
              α (extChartAt I x₀ x₀, v₀) s ∈
                closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
            (∀ s ∈ Icc (-τ) τ,
              (α (extChartAt I x₀ x₀, v₀) s).1 ∈
                (extChartAt I x₀).target) ∧
            (∀ s ∈ Icc (-τ) τ,
              cutoff (n := n) x₀
                (α (extChartAt I x₀ x₀, v₀) s).1 = 1) ∧
            ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (-τ) τ,
              α (extChartAt I x₀ x₀, r • v₀) s =
                ((α (extChartAt I x₀ x₀, v₀) (r * s)).1,
                  r • (α (extChartAt I x₀ x₀, v₀) (r * s)).2)) ∧
        ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
          expAt g x₀ (t • v) =
            (extChartAt I x₀).symm
              (α (extChartAt I x₀ x₀, v) t).1 := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ₀, hτ₀, δ, hδ, ε, hε, a, α, hα, hexp⟩
  let z₀ : E := extChartAt I x₀ x₀
  have hcut_nhds :
      {z : E | cutoff (n := n) x₀ z = 1} ∈ 𝓝 z₀ := by
    simpa [z₀] using cutoff_eventuallyEq_one (n := n) x₀
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hcut_nhds with
    ⟨ρ, hρpos, hρsub⟩
  let κ : ℝ := ρ / (2 * ((a : ℝ) + 1))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    positivity
  let τ : ℝ := min τ₀ (min ε κ)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min hτ₀ (lt_min hε hκ_pos)
  have hττ₀ : τ ≤ τ₀ := by
    dsimp [τ]
    exact min_le_left _ _
  have hτε : τ ≤ ε := by
    dsimp [τ]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hτκ : τ ≤ κ := by
    dsimp [τ]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨τ, hτ, δ, hδ, a, α, ?_, ?_⟩
  · intro v₀ hv₀
    rcases hα v₀ hv₀ with ⟨hα0, hαder, hαmem, hαtarget, hhom⟩
    have hsub : Icc (-τ) τ ⊆ Icc (-ε) ε := by
      intro s hs
      exact ⟨(neg_le_neg hτε).trans hs.1, hs.2.trans hτε⟩
    refine ⟨hα0, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      exact (hαder s (hsub hs)).mono hsub
    · intro s hs
      exact hαmem s (hsub hs)
    · intro s hs
      exact hαtarget s (hsub hs)
    · intro s hs
      apply hρsub
      have hdist :
          dist (α (extChartAt I x₀ x₀, v₀) s).1 z₀ ≤ (a : ℝ) * |s| := by
        simpa [z₀] using
          plFlowPosition_dist_anchor_le_radius_mul_abs
            (g := g) (x₀ := x₀) (ε := ε) (τ := τ) (a := a)
            (α := α) (v₀ := v₀) hτ.le hτε hα0 hαder hαmem hs
      have habs : |s| ≤ τ := by
        exact abs_le.mpr hs
      have hdistρ : dist (α (extChartAt I x₀ x₀, v₀) s).1 z₀ ≤ ρ := by
        have ha_nonneg : 0 ≤ (a : ℝ) := NNReal.coe_nonneg a
        have hmul_le : (a : ℝ) * |s| ≤ (a : ℝ) * τ :=
          mul_le_mul_of_nonneg_left habs ha_nonneg
        have hτ_le : (a : ℝ) * τ ≤ ρ := by
          calc
            (a : ℝ) * τ ≤ (a : ℝ) * κ :=
              mul_le_mul_of_nonneg_left hτκ ha_nonneg
            _ = (a : ℝ) * (ρ / (2 * ((a : ℝ) + 1))) := rfl
            _ ≤ ρ := by
              have hfrac_le_one : (a : ℝ) / ((a : ℝ) + 1) ≤ 1 := by
                have hden' : 0 < (a : ℝ) + 1 := by positivity
                rw [div_le_one hden']
                linarith
              calc
                (a : ℝ) * (ρ / (2 * ((a : ℝ) + 1)))
                    = (ρ / 2) * ((a : ℝ) / ((a : ℝ) + 1)) := by
                      have hden' : ((a : ℝ) + 1) ≠ 0 := by positivity
                      field_simp [hden']
                _ ≤ (ρ / 2) * 1 := by
                      gcongr
                _ ≤ ρ := by linarith
        exact hdist.trans (hmul_le.trans hτ_le)
      simpa [mem_closedBall] using hdistρ
    · intro r hr s hs
      have hs_old : s ∈ Icc (-ε) ε := hsub hs
      have hrs : r * s ∈ Icc (-τ) τ := by
        have hτ_abs : |s| ≤ τ := abs_le.mpr hs
        have hr_abs : |r| ≤ 1 := by
          rw [abs_of_nonneg hr.1]
          exact hr.2
        have hprod_abs : |r * s| ≤ τ := by
          rw [abs_mul]
          calc
            |r| * |s| ≤ 1 * τ := by
              gcongr
            _ = τ := one_mul τ
        exact abs_le.mp hprod_abs
      have hrs_old : r * s ∈ Icc (-ε) ε := hsub hrs
      exact hhom r hr s hs_old
  · intro v hv t ht
    exact hexp v hv t ⟨ht.1, ht.2.trans hττ₀⟩

/-- Constant-speed path-length formula for the cutoff-one PL curve. -/
theorem plFlowCurve_pathELength_eq
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {τ : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hτ : 0 < τ)
    (hα0 : α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ s ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) s))
        (Icc (-τ) τ) s)
    (hαtarget : ∀ s ∈ Icc (-τ) τ,
      (α (extChartAt I x₀ x₀, v₀) s).1 ∈ (extChartAt I x₀).target)
    (hαcut : ∀ s ∈ Icc (-τ) τ,
      cutoff (n := n) x₀ (α (extChartAt I x₀ x₀, v₀) s).1 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) τ) :
    let c : ℝ → M :=
      fun s => (extChartAt I x₀).symm
        (α (extChartAt I x₀ x₀, v₀) s).1
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    Manifold.pathELength I c 0 t =
      ENNReal.ofReal
        (t * Real.sqrt
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  let c : ℝ → M :=
    fun s => (extChartAt I x₀).symm
      (α (extChartAt I x₀ x₀, v₀) s).1
  let C : ℝ :=
    Real.sqrt (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀)
  have hC_nonneg : 0 ≤ C := by
    exact Real.sqrt_nonneg _
  have hintegrand :
      ∀ s ∈ Ioo (0 : ℝ) t,
        ‖mfderiv 𝓘(ℝ) I c s 1‖ₑ = ENNReal.ofReal C := by
    intro s hs
    have hsτ : s ∈ Ioo (-τ) τ := by
      constructor
      · linarith [hτ, hs.1]
      · exact hs.2.trans_le ht.2
    have hsτc : s ∈ Icc (-τ) τ := Ioo_subset_Icc_self hsτ
    have hnorm :=
      plFlowCurve_enorm_mfderiv_eq_chartGeodesicMetric_of_mem_Ioo
        (g := g) (x₀ := x₀) (ε := τ) (α := α) (v₀ := v₀)
        hαder hαtarget hsτ (hαcut s hsτc)
    have hspeed :=
      plFlow_chartGeodesicMetric_speed_eq_initial_of_mem_Ioo
        (g := g) (x₀ := x₀) (ε := τ) hτ
        (α := α) (v₀ := v₀) hα0 hαder hsτ
    rw [hspeed] at hnorm
    simpa [c, C] using hnorm
  calc
    Manifold.pathELength I c 0 t
        = ∫⁻ s in Ioo (0 : ℝ) t,
            ‖mfderiv 𝓘(ℝ) I c s 1‖ₑ := by
          rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    _ = ∫⁻ _s in Ioo (0 : ℝ) t, ENNReal.ofReal C := by
          exact setLIntegral_congr_fun measurableSet_Ioo hintegrand
    _ = ENNReal.ofReal C * volume (Ioo (0 : ℝ) t) := by
          rw [setLIntegral_const]
    _ = ENNReal.ofReal (t * C) := by
          rw [Real.volume_Ioo, sub_zero]
          rw [← ENNReal.ofReal_mul hC_nonneg]
          rw [mul_comm]

/--
Uniform constant-speed path-length formula for the installed local
exponential map.
-/
theorem expAt_pathELength_eq_chartGeodesicMetric_sqrt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∀ t ∈ Icc (0 : ℝ) τ,
        ∃ c : ℝ → M,
          c 0 = x₀ ∧
            c t = expAt g x₀ (t • v₀) ∧
            ContMDiffOn 𝓘(ℝ) I 1 c (Icc (0 : ℝ) t) ∧
            letI : RiemannianBundle
                (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
              g.toRiemannianBundle
            Manifold.pathELength I c 0 t =
              ENNReal.ofReal
                (t * Real.sqrt
                  (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀)) := by
  rcases expAt_uniform_pl_flow_cutoff_one_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, _a, α, hα, hexp⟩
  refine ⟨τ, hτ, δ, hδ, ?_⟩
  intro v₀ hv₀ t ht
  rcases hα v₀ hv₀ with ⟨hα0, hαder, _hαmem, hαtarget, hαcut, _hhom⟩
  let c : ℝ → M :=
    fun s => (extChartAt I x₀).symm
      (α (extChartAt I x₀ x₀, v₀) s).1
  have ht_sub : Icc (0 : ℝ) t ⊆ Icc (-τ) τ := by
    intro s hs
    constructor
    · linarith [hτ, hs.1]
    · exact hs.2.trans ht.2
  have hc_smooth : ContMDiffOn 𝓘(ℝ) I 1 c (Icc (0 : ℝ) t) :=
    plFlowCurve_contMDiffOn_Icc (g := g) (x₀ := x₀)
      (ε := τ) (a := 0) (b := t) (α := α) (v₀ := v₀)
      (hsub := ht_sub) (hαder := hαder) (hαtarget := hαtarget)
  have hc0 : c 0 = x₀ := by
    change (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) 0).1 = x₀
    rw [hα0]
    simp
  have hct : c t = expAt g x₀ (t • v₀) := by
    dsimp [c]
    exact (hexp v₀ hv₀ t ht).symm
  have hlen :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      Manifold.pathELength I c 0 t =
        ENNReal.ofReal
          (t * Real.sqrt
            (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀)) :=
    plFlowCurve_pathELength_eq (g := g) (x₀ := x₀)
      (τ := τ) (α := α) (v₀ := v₀) hτ hα0 hαder hαtarget hαcut ht
  exact ⟨c, hc0, hct, hc_smooth, hlen⟩

/-- Sharp distance bound along the local exponential rays. -/
theorem expAt_dist_le_time_mul_chartGeodesicMetric_sqrt
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ v₀ : E, ‖v₀‖ < δ →
      ∀ t ∈ Icc (0 : ℝ) τ,
        letI : MetricSpace M := g.toMetricSpace
        dist x₀ (expAt g x₀ (t • v₀)) ≤
          t * Real.sqrt
            (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀) := by
  rcases expAt_pathELength_eq_chartGeodesicMetric_sqrt (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, hpack⟩
  refine ⟨τ, hτ, δ, hδ, ?_⟩
  intro v₀ hv₀ t ht
  rcases hpack v₀ hv₀ t ht with ⟨c, hc0, hct, hc_smooth, hlen⟩
  let L : ℝ :=
    t * Real.sqrt
      (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀)
  have hL_nonneg : 0 ≤ L := by
    exact mul_nonneg ht.1 (Real.sqrt_nonneg _)
  have hLenLe :
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        g.toRiemannianBundle
      Manifold.pathELength I c 0 t ≤ ENNReal.ofReal L := by
    simpa [L] using le_of_eq hlen
  have hdist :=
    induced_dist_le_of_pathELength_le_ofReal (g := g)
      (x := x₀) (y := expAt g x₀ (t • v₀)) (γ := c)
      (a := 0) (b := t) (L := L)
      hc_smooth hc0 hct ht.1 hL_nonneg hLenLe
  simpa [L] using hdist

private theorem chartGeodesicMetric_smul_smul
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z v : E) (r : ℝ) :
    chartGeodesicMetric g x₀ z (r • v) (r • v) =
      r * r * chartGeodesicMetric g x₀ z v v := by
  simp [mul_assoc]

private theorem pos_mul_sqrt_inv_smul_speed
    {τ S : ℝ} (hτ : 0 < τ) :
    τ * Real.sqrt ((τ⁻¹ * τ⁻¹) * S) = Real.sqrt S := by
  have hτinv_nonneg : 0 ≤ τ⁻¹ := (inv_pos.mpr hτ).le
  calc
    τ * Real.sqrt ((τ⁻¹ * τ⁻¹) * S)
        = τ * (Real.sqrt (τ⁻¹ * τ⁻¹) * Real.sqrt S) := by
          rw [Real.sqrt_mul (mul_nonneg hτinv_nonneg hτinv_nonneg)]
    _ = τ * (τ⁻¹ * Real.sqrt S) := by
          rw [Real.sqrt_mul_self hτinv_nonneg]
    _ = Real.sqrt S := by
          field_simp [ne_of_gt hτ]

/-- Endpoint form of the sharp local exponential distance bound. -/
theorem expAt_dist_le_chartGeodesicMetric_sqrt
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ δ > (0 : ℝ), ∀ v : E, ‖v‖ < δ →
      letI : MetricSpace M := g.toMetricSpace
      dist x₀ (expAt g x₀ v) ≤
        Real.sqrt (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v v) := by
  rcases expAt_dist_le_time_mul_chartGeodesicMetric_sqrt (g := g) (x₀ := x₀) with
    ⟨τ, hτ, δ, hδ, hdist⟩
  refine ⟨τ * δ, mul_pos hτ hδ, ?_⟩
  intro v hv
  letI : MetricSpace M := g.toMetricSpace
  let v₀ : E := τ⁻¹ • v
  have hv₀ : ‖v₀‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    calc
      τ⁻¹ * ‖v‖ < τ⁻¹ * (τ * δ) := by
        exact mul_lt_mul_of_pos_left hv (inv_pos.mpr hτ)
      _ = δ := by
        field_simp [ne_of_gt hτ]
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.le, le_rfl⟩
  have hdistτ := hdist v₀ hv₀ τ hτmem
  have harg :
      τ • v₀ = v := by
    dsimp [v₀]
    rw [smul_smul]
    have hcoeff : τ * τ⁻¹ = 1 := by
      field_simp [ne_of_gt hτ]
    rw [hcoeff, one_smul]
  have hscale :
      τ * Real.sqrt
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀) =
        Real.sqrt (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v v) := by
    dsimp [v₀]
    change
      τ * Real.sqrt
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀)
            (τ⁻¹ • v) (τ⁻¹ • v)) =
        Real.sqrt (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v v)
    rw [chartGeodesicMetric_smul_smul]
    exact pos_mul_sqrt_inv_smul_speed hτ
  calc
    dist x₀ (expAt g x₀ v)
        ≤ τ * Real.sqrt
            (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀) := by
          simpa [harg] using hdistτ
    _ = Real.sqrt
          (chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v v) := hscale

end GeodesicTransport
end Poincare
