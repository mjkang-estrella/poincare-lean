import Poincare.Global.ExponentialFixedTime
import Poincare.Global.GeodesicDependence
import Poincare.Global.GeodesicDistance

/-!
# Radial geodesic path length boundary

This module records the interval-level path regularity that is available for
the target-shrunk Picard-Lindelöf chart flow used by `expAt`.  The exported
fixed-time package gives a closed-interval ODE solution whose position stays
inside the inverse chart target; Mathlib's ODE regularity theorem upgrades the
pointwise `HasDerivWithinAt` data to `C¹` on every closed subinterval.

The sharp `pathELength` computation for the selected exponential ray still
requires an additional bridge from this PL-flow chart path to the tangent norm
integrand used by `Manifold.pathELength`; see
`harness/reports/M5-geo-28_blocked.md`.
-/

noncomputable section

open Bundle Set
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

/--
The closed-interval PL chart flow used in the fixed-time exponential package
is `C¹` as an `E × E`-valued path on every closed subinterval of its exported
time interval.
-/
theorem plFlowState_contDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε a b : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t) :
    ContDiffOn ℝ 1 (α (extChartAt I x₀ x₀, v₀)) (Icc a b) := by
  let F : E × E → E × E := geodesicFlowField (chartChristoffelField g x₀)
  let f : ℝ → E × E → E × E := fun _ p => F p
  have hf : ContDiffOn ℝ 1 (Function.uncurry f) ((Icc a b) ×ˢ (univ : Set (E × E))) := by
    have hF : ContDiff ℝ 1 F :=
      geodesicFlowField_chartChristoffelField_contDiff (g := g) (x₀ := x₀)
    have hsnd : ContDiff ℝ 1 (fun p : ℝ × (E × E) => p.2) := contDiff_snd
    simpa [f, F, Function.uncurry] using (hF.comp hsnd).contDiffOn
  have hder : ∀ t ∈ Icc a b,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (f t (α (extChartAt I x₀ x₀, v₀) t)) (Icc a b) t := by
    intro t ht
    simpa [f, F] using (hαder t (hsub ht)).mono hsub
  have hmem : MapsTo (α (extChartAt I x₀ x₀, v₀)) (Icc a b) (univ : Set (E × E)) :=
    fun _ _ => mem_univ _
  exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (f := f) (u := (univ : Set (E × E))) hf hder hmem

/--
The position component of the same PL chart flow is `C¹` on every closed
subinterval of the exported time interval.
-/
theorem plFlowPosition_contDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε a b : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t) :
    ContDiffOn ℝ 1 (fun t : ℝ => (α (extChartAt I x₀ x₀, v₀) t).1) (Icc a b) := by
  have hstate :=
    plFlowState_contDiffOn_Icc (g := g) (x₀ := x₀)
      (hsub := hsub) (hαder := hαder)
  simpa using hstate.fst

/--
Composing the `C¹` chart-position path with the smooth inverse chart gives a
`C¹` manifold path on the same closed interval.
-/
theorem plFlowCurve_contMDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε a b : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hsub : Icc a b ⊆ Icc (-ε) ε)
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαtarget : ∀ t ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) t).1 ∈ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ) I 1
      (fun t : ℝ => (extChartAt I x₀).symm
        (α (extChartAt I x₀ x₀, v₀) t).1)
      (Icc a b) := by
  have hpos :=
    plFlowPosition_contDiffOn_Icc (g := g) (x₀ := x₀)
      (hsub := hsub) (hαder := hαder)
  have hposM : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1
      (fun t : ℝ => (α (extChartAt I x₀ x₀, v₀) t).1) (Icc a b) := by
    exact hpos.contMDiffOn
  exact (contMDiffOn_extChartAt_symm x₀).comp hposM
    (fun t ht => hαtarget t (hsub ht))

/--
On interior times of the PL-flow interval, the derivative of the chart
position is the velocity component of the first-order state.
-/
theorem plFlowPosition_hasDerivAt_of_mem_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt
      (fun s : ℝ => (α (extChartAt I x₀ x₀, v₀) s).1)
      (α (extChartAt I x₀ x₀, v₀) t).2 t := by
  have hstate :
      HasDerivAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t)) t :=
    (hαder t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  exact geodesic_position_hasDerivAt
    (Γ := chartChristoffelField g x₀) (γ := α (extChartAt I x₀ x₀, v₀)) hstate

/--
The blended chart-metric speed of the PL chart flow is constant on the
interior of its exported interval.
-/
theorem plFlow_chartGeodesicMetric_speed_eq_initial_of_mem_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v₀ : E}
    (hα0 : α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    chartGeodesicMetric g x₀
        (α (extChartAt I x₀ x₀, v₀) t).1
        (α (extChartAt I x₀ x₀, v₀) t).2
        (α (extChartAt I x₀ x₀, v₀) t).2 =
      chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ := by
  have hder : ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) s)) s := by
    intro s hs
    exact (hαder s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have hconst :=
    chart_geodesic_speed_constantOn_Ioo
      (g := g) (x₀ := x₀) (a := -ε) (b := ε)
      (γ := α (extChartAt I x₀ x₀, v₀)) hder ht hzero
  have hinit :
      chartGeodesicMetric g x₀
          (α (extChartAt I x₀ x₀, v₀) 0).1
          (α (extChartAt I x₀ x₀, v₀) 0).2
          (α (extChartAt I x₀ x₀, v₀) 0).2 =
        chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) v₀ v₀ := by
    rw [hα0]
  exact hconst.trans hinit

/--
The fixed-time `expAt` package supplies, for every small initial chart
velocity, a closed interval ending at `t` whose PL-flow path is a `C¹`
manifold path from `x₀` to `expAt g x₀ (t • v₀)`.
-/
theorem expAt_plFlowCurve_contMDiffOn_Icc
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ τ > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∃ α : E × E → ℝ → E × E,
        (∀ v₀ : E, ‖v₀‖ < δ →
          α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
            (∀ s ∈ Icc (-ε) ε,
              HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
                (geodesicFlowField (chartChristoffelField g x₀)
                  (α (extChartAt I x₀ x₀, v₀) s))
                (Icc (-ε) ε) s) ∧
            (∀ s ∈ Icc (-ε) ε,
              (α (extChartAt I x₀ x₀, v₀) s).1 ∈
                (extChartAt I x₀).target)) ∧
        ∀ v₀ : E, ‖v₀‖ < δ → ∀ t ∈ Icc (0 : ℝ) τ,
          let c : ℝ → M :=
            fun s => (extChartAt I x₀).symm
              (α (extChartAt I x₀ x₀, v₀) s).1
          c 0 = x₀ ∧
            c t = expAt g x₀ (t • v₀) ∧
            ContMDiffOn 𝓘(ℝ) I 1 c (Icc (0 : ℝ) t) := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x₀) with
    ⟨τ₀, hτ₀, δ, hδ, ε, hε, _a, α, hα, hexp⟩
  let τ : ℝ := min τ₀ ε
  have hτ : 0 < τ := by
    exact lt_min hτ₀ hε
  refine ⟨τ, hτ, δ, hδ, ε, hε, α, ?_, ?_⟩
  · intro v₀ hv₀
    rcases hα v₀ hv₀ with ⟨hα0, hαder, _hαmem, hαtarget, _hhom⟩
    exact ⟨hα0, hαder, hαtarget⟩
  · intro v₀ hv₀ t ht
    rcases hα v₀ hv₀ with ⟨hα0, hαder, _hαmem, hαtarget, _hhom⟩
    let c : ℝ → M :=
      fun s => (extChartAt I x₀).symm
        (α (extChartAt I x₀ x₀, v₀) s).1
    have hzero_mem : (0 : ℝ) ∈ Icc (-ε) ε := by
      constructor <;> linarith
    have htτ₀ : t ≤ τ₀ := ht.2.trans (min_le_left τ₀ ε)
    have htε : t ≤ ε := ht.2.trans (min_le_right τ₀ ε)
    have ht_raw : t ∈ Icc (0 : ℝ) τ₀ := ⟨ht.1, htτ₀⟩
    have ht_sub : Icc (0 : ℝ) t ⊆ Icc (-ε) ε := by
      intro s hs
      constructor
      · linarith [hε, hs.1]
      · exact hs.2.trans htε
    have hc_smooth : ContMDiffOn 𝓘(ℝ) I 1 c (Icc (0 : ℝ) t) :=
      plFlowCurve_contMDiffOn_Icc (g := g) (x₀ := x₀)
        (hsub := ht_sub) (hαder := hαder) (hαtarget := hαtarget)
    have hc0 : c 0 = x₀ := by
      change (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) 0).1 = x₀
      rw [hα0]
      simp
    have hct : c t = expAt g x₀ (t • v₀) := by
      dsimp [c]
      exact (hexp v₀ hv₀ t ht_raw).symm
    exact ⟨hc0, hct, hc_smooth⟩

end GeodesicTransport
end Poincare
