import Poincare.Global.ExponentialMap

/-!
# Local exponential-map endpoint package

This module continues the endpoint-controlled geodesic-flow construction from
`Poincare.Global.ExponentialMap`.  The first step is a target-shrunk version
of the uniform PL flow: the common Picard-Lindelöf ball is shrunk so that the
position component stays inside the anchor chart target on the whole closed
time interval.

The fixed-time exponential map itself is not introduced below.  The remaining
gap is recorded in `harness/reports/M5-geo-7_blocked.md`: proving the requested
ray law requires a flow-level homogeneity theorem at a positive endpoint, not
just the germ-level eventual homogeneity already available in
`Poincare.Global.ExponentialGerm`.
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

private theorem geodesicGermChartSolution_eventually_hasDerivAt'
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

/--
Uniform local geodesic chart flow with the PL ball shrunk into the anchor
chart target in the position coordinate.

The proof reruns the Picard-Lindelöf construction from the endpoint-controlled
flow, then uses `IsPicardLindelof.exists_shrink_radius` with a closed ball
contained in `(extChartAt I x₀).target`.  The returned radius `a` controls the
whole first-order state, so the product metric immediately gives target
membership for the position component.
-/
theorem exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target
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
          ∀ t ∈ Icc (-ε) ε,
            (α (extChartAt I x₀ x₀, v₀) t).1 ∈
              (extChartAt I x₀).target := by
  let p₀ : E × E := (extChartAt I x₀ x₀, 0)
  let z₀ : E := extChartAt I x₀ x₀
  have hflow :
      ContDiffAt ℝ 1
        (geodesicFlowField (chartChristoffelField g x₀)) p₀ := by
    simpa [p₀] using
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
    ⟨ε, hε, hpl⟩
  rcases
      hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall
    with ⟨α, hα⟩
  refine ⟨(r : ℝ), by exact_mod_cast (half_pos ha_pos), ε, hε, a, α,
    fun v₀ hv₀ ↦ ?_⟩
  have hp :
      (extChartAt I x₀ x₀, v₀) ∈ closedBall p₀ r := by
    rw [Metric.mem_closedBall]
    change dist (extChartAt I x₀ x₀, v₀) (extChartAt I x₀ x₀, (0 : E)) ≤ (r : ℝ)
    rw [dist_prod_same_left]
    simpa [dist_eq_norm] using le_of_lt hv₀
  have hspec := hα (extChartAt I x₀ x₀, v₀) hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.1
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.2.1 t ht'
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.2.2 t ht'
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      simpa only [zero_sub, zero_add] using ht
    have hmem :
        α (extChartAt I x₀ x₀, v₀) t ∈
          closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) := by
      simpa only [p₀, sub_eq_add_neg, zero_sub, zero_add] using hspec.2.2 t ht'
    have hpos_mem :
        (α (extChartAt I x₀ x₀, v₀) t).1 ∈
          closedBall z₀ (a : ℝ) := by
      have hprod :
          α (extChartAt I x₀ x₀, v₀) t ∈
            closedBall z₀ (a : ℝ) ×ˢ closedBall (0 : E) (a : ℝ) := by
        simpa [closedBall_prod_same, z₀] using hmem
      exact hprod.1
    apply hρsub
    have ha_le_half : (a : ℝ) ≤ ρ / 2 := by
      have ha_le_target : a ≤ targetRadius := by
        dsimp [a]
        exact min_le_right _ _
      exact_mod_cast ha_le_target
    exact closedBall_subset_closedBall (by linarith) hpos_mem

/--
The target-shrunk PL flow can be chosen so that, for each sufficiently small
initial velocity, its chart solution agrees with the already chosen
`geodesicGermChartSolution` as a germ at `0`.

This is still a germ-level identification.  It intentionally does not claim
equality at a fixed positive endpoint; that requires the separate flow
homogeneity and interval-control argument recorded in the blocked report.
-/
theorem exists_uniform_local_geodesic_chart_flow_with_mem_target_eventuallyEq_germ
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
          α (extChartAt I x₀ x₀, v₀) =ᶠ[𝓝 (0 : ℝ)]
            geodesicGermChartSolution g x₀ v₀ := by
  rcases exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target
      (g := g) (x₀ := x₀) with
    ⟨δ, hδ, ε, hε, a, α, hα⟩
  refine ⟨δ, hδ, ε, hε, a, α, fun v₀ hv₀ ↦ ?_⟩
  rcases hα v₀ hv₀ with ⟨hα0, hαder, hαmem, hαtarget⟩
  refine ⟨hα0, hαder, hαmem, hαtarget, ?_⟩
  have hflow_der :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt (α (extChartAt I x₀ x₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (α (extChartAt I x₀ x₀, v₀) t)) t := by
    have hI : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hI] with t ht
    exact (hαder t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hgerm_der :=
    geodesicGermChartSolution_eventually_hasDerivAt' g x₀ v₀
  have hgerm0 :
      geodesicGermChartSolution g x₀ v₀ 0 =
        (extChartAt I x₀ x₀, v₀) :=
    (geodesicGermChartSolution_spec g x₀ v₀).1
  exact (geodesicFlowField_chartChristoffelField_eventuallyEq
    (g := g) (x₀ := x₀) (v₀ := v₀)
    hgerm0 hα0 hgerm_der hflow_der).symm

end GeodesicTransport
end Poincare
