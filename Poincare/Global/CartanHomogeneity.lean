import Poincare.Global.CartanDifferential
import Poincare.Global.GeodesicLengthFinal

/-!
# Cartan homogeneity conversion

This module records the non-unit-speed conversion needed after
`CartanDomainShrink`: a small endpoint vector `v` is represented as
`T • u`, where `u` is a genuinely small working velocity and `T` is a
corresponding positive time.  The cutoff-one PL package then applies to `u`
on the interval containing `T`.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanHomogeneity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The small working velocity used to host a nonzero endpoint vector. -/
def workingVelocity (δ : ℝ) (v : E) : E :=
  (δ / 2) • (‖v‖⁻¹ • v)

/-- The time paired with `workingVelocity`: `workingTime δ v • workingVelocity δ v = v`. -/
def workingTime (δ : ℝ) (v : E) : ℝ :=
  ‖v‖ / (δ / 2)

theorem norm_workingVelocity_lt (δ : ℝ) (hδ : 0 < δ) (v : E) :
    ‖workingVelocity δ v‖ < δ := by
  by_cases hv : v = 0
  · simp [workingVelocity, hv, hδ]
  · have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hnorm_inv_pos : 0 < ‖v‖⁻¹ := inv_pos.mpr hnorm_pos
    have hhalf_pos : 0 < δ / 2 := by linarith
    rw [workingVelocity, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hhalf_pos, abs_of_pos hnorm_inv_pos]
    calc
      δ / 2 * (‖v‖⁻¹ * ‖v‖) = δ / 2 := by
        rw [inv_mul_cancel₀ (ne_of_gt hnorm_pos), mul_one]
      _ < δ := by linarith

theorem workingTime_smul_workingVelocity (δ : ℝ) (hδ : 0 < δ) (v : E) :
    workingTime δ v • workingVelocity δ v = v := by
  by_cases hv : v = 0
  · simp [workingTime, workingVelocity, hv]
  · have hnorm_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hhalf_ne : δ / 2 ≠ 0 := by linarith
    calc
      workingTime δ v • workingVelocity δ v
          = ((‖v‖ / (δ / 2)) * (δ / 2) * ‖v‖⁻¹) • v := by
            simp [workingTime, workingVelocity, smul_smul, mul_assoc]
      _ = (‖v‖ * ‖v‖⁻¹) • v := by
            congr 1
            field_simp [hhalf_ne]
      _ = v := by
            rw [mul_inv_cancel₀ hnorm_ne]
            simp

theorem workingTime_mem_Icc_of_norm_lt
    {δ τ ρ : ℝ} (hδ : 0 < δ) (hρτ : ρ ≤ (δ / 2) * τ)
    {v : E} (hv : ‖v‖ < ρ) :
    workingTime δ v ∈ Icc (0 : ℝ) τ := by
  have hhalf_pos : 0 < δ / 2 := by linarith
  constructor
  · exact div_nonneg (norm_nonneg v) hhalf_pos.le
  · calc
      workingTime δ v = ‖v‖ / (δ / 2) := rfl
      _ ≤ ρ / (δ / 2) := by
        exact div_le_div_of_nonneg_right hv.le hhalf_pos.le
      _ ≤ ((δ / 2) * τ) / (δ / 2) := by
        exact div_le_div_of_nonneg_right hρτ hhalf_pos.le
      _ = τ := by
        field_simp [ne_of_gt hhalf_pos]

theorem workingTime_mem_Ioo_of_norm_lt
    {δ τ ρ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (hρτ : ρ ≤ ((δ / 2) * τ) / 2)
    {v : E} (hvne : v ≠ 0) (hv : ‖v‖ < ρ) :
    workingTime δ v ∈ Ioo (0 : ℝ) τ := by
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  constructor
  · exact div_pos hnorm_pos hhalf_pos
  · calc
      workingTime δ v = ‖v‖ / (δ / 2) := rfl
      _ < ρ / (δ / 2) := by
        exact div_lt_div_of_pos_right hv hhalf_pos
      _ ≤ (((δ / 2) * τ) / 2) / (δ / 2) := by
        exact div_le_div_of_nonneg_right hρτ hhalf_pos.le
      _ = τ / 2 := by
        field_simp [ne_of_gt hhalf_pos]
      _ < τ := by linarith

/--
Shrinking once more turns each small endpoint vector `v` into a small working
velocity `u = (δ / 2) • (‖v‖⁻¹ • v)` and time `T = ‖v‖ / (δ / 2)`.

The theorem exports the useful data at `(u, T)`: `u` is inside the cutoff-one
velocity ball, `T` lies in the PL interval, `v = T • u`, the cutoff-one PL
block hypotheses hold for `u`, `expAt v` is the corresponding PL endpoint, and
for nonzero `v` the radial endpoint derivative is read at `(u, T)`.
-/
theorem exists_shrunk_cutoff_one_homogeneity_conversion
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball (0 : E) ρ ⊆
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
      ∃ τ : ℝ, 0 < τ ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ a : NNReal,
        ∃ α : E × E → ℝ → E × E,
          ρ ≤ ((δ / 2) * τ) / 2 ∧
          (∀ v : E, ‖v‖ < ρ →
            let u : E := workingVelocity δ v
            let T : ℝ := workingTime δ v
            ‖u‖ < δ ∧
              T ∈ Icc (0 : ℝ) τ ∧
              T • u = v ∧
              α (extChartAt I x₀ x₀, u) 0 = (extChartAt I x₀ x₀, u) ∧
              (∀ s ∈ Icc (-τ) τ,
                HasDerivWithinAt (α (extChartAt I x₀ x₀, u))
                  (geodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                    (α (extChartAt I x₀ x₀, u) s))
                  (Icc (-τ) τ) s) ∧
              (∀ s ∈ Icc (-τ) τ,
                α (extChartAt I x₀ x₀, u) s ∈
                  Metric.closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) ∧
              (∀ s ∈ Icc (-τ) τ,
                (α (extChartAt I x₀ x₀, u) s).1 ∈
                  (extChartAt I x₀).target) ∧
              (∀ s ∈ Icc (-τ) τ,
                GeodesicTransport.cutoff (n := 3) x₀
                  (α (extChartAt I x₀ x₀, u) s).1 = 1) ∧
              (∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (-τ) τ,
                α (extChartAt I x₀ x₀, r • u) s =
                  ((α (extChartAt I x₀ x₀, u) (r * s)).1,
                    r • (α (extChartAt I x₀ x₀, u) (r * s)).2)) ∧
              GeodesicTransport.expAt g x₀ v =
                (extChartAt I x₀).symm
                  (α (extChartAt I x₀ x₀, u) T).1 ∧
              (v ≠ 0 →
                HasDerivAt
                  (fun s : ℝ =>
                    extChartAt I x₀
                      (GeodesicTransport.expAt g x₀ ((T + s) • u)))
                  (α (extChartAt I x₀ x₀, u) T).2 0)) := by
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  have h0 : (0 : E) ∈ e.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) x₀
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds h0) with
    ⟨r, hr_pos, hr_source⟩
  rcases GeodesicTransport.expAt_uniform_pl_flow_cutoff_one_eq_on_Icc
      (g := g) (x₀ := x₀) with
    ⟨τ, hτ_pos, δ, hδ_pos, a, α, hα, hexp⟩
  let ρ : ℝ := min r (((δ / 2) * τ) / 2) / 2
  have hhalf_pos : 0 < δ / 2 := by linarith
  have hprod_pos : 0 < ((δ / 2) * τ) / 2 := by positivity
  have hmin_pos : 0 < min r (((δ / 2) * τ) / 2) :=
    lt_min hr_pos hprod_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρ_le_min : ρ ≤ min r (((δ / 2) * τ) / 2) := by
    dsimp [ρ]
    linarith
  have hρ_le_r : ρ ≤ r :=
    hρ_le_min.trans (min_le_left r (((δ / 2) * τ) / 2))
  have hρ_le_prod : ρ ≤ ((δ / 2) * τ) / 2 :=
    hρ_le_min.trans (min_le_right r (((δ / 2) * τ) / 2))
  refine ⟨ρ, hρ_pos, ?_, τ, hτ_pos, δ, hδ_pos, a, α, hρ_le_prod, ?_⟩
  · intro v hv
    apply hr_source
    have hvdist : dist v (0 : E) < r :=
      (Metric.mem_ball.mp hv).trans_le hρ_le_r
    exact Metric.mem_ball.mpr hvdist
  · intro v hv
    let u : E := workingVelocity δ v
    let T : ℝ := workingTime δ v
    have hu : ‖u‖ < δ := by
      simpa [u] using norm_workingVelocity_lt δ hδ_pos v
    have hT : T ∈ Icc (0 : ℝ) τ := by
      have hρ_le_tau : ρ ≤ (δ / 2) * τ := by
        calc
          ρ ≤ ((δ / 2) * τ) / 2 := hρ_le_prod
          _ ≤ (δ / 2) * τ := by linarith
      simpa [T] using
        workingTime_mem_Icc_of_norm_lt (δ := δ) (τ := τ) (ρ := ρ)
          hδ_pos hρ_le_tau hv
    have hTu : T • u = v := by
      simpa [u, T] using workingTime_smul_workingVelocity δ hδ_pos v
    rcases hα u hu with
      ⟨hα0, hαder, hαmem, hαtarget, hαcut, hhom⟩
    have hexpv :
        GeodesicTransport.expAt g x₀ v =
          (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, u) T).1 := by
      rw [← hTu]
      exact hexp u hu T hT
    have hradial :
        v ≠ 0 →
          HasDerivAt
            (fun s : ℝ =>
              extChartAt I x₀
                (GeodesicTransport.expAt g x₀ ((T + s) • u)))
            (α (extChartAt I x₀ x₀, u) T).2 0 := by
      intro hvne
      have hTioo : T ∈ Ioo (0 : ℝ) τ := by
        simpa [T] using
          workingTime_mem_Ioo_of_norm_lt (δ := δ) (τ := τ) (ρ := ρ)
            hδ_pos hτ_pos hρ_le_prod hvne hv
      have hTiooε : T ∈ Ioo (-τ) τ := ⟨by linarith [hTioo.1], hTioo.2⟩
      have hderAll :
          ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
            HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
              (geodesicFlowField
                (GeodesicTransport.chartChristoffelField g x₀)
                (α (extChartAt I x₀ x₀, v₀) r))
              (Icc (-τ) τ) r := by
        intro v₀ hv₀ r hr
        exact (hα v₀ hv₀).2.1 r hr
      have htargetAll :
          ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
            (α (extChartAt I x₀ x₀, v₀) r).1 ∈
              (extChartAt I x₀).target := by
        intro v₀ hv₀ r hr
        exact (hα v₀ hv₀).2.2.2.1 r hr
      have hder :=
        CartanDifferential.expAt_chart_radial_hasDerivAt_of_uniform_geodesicFlow
          (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (ε := τ)
          (α := α) (v := u) (t := T) (c := 1)
          hu hderAll htargetAll hexp hTioo hTiooε
      simpa [one_mul] using hder
    exact ⟨hu, hT, hTu, hα0, hαder, hαmem, hαtarget, hαcut, hhom,
      hexpv, hradial⟩

end CartanHomogeneity
end Poincare
