import Poincare.Global.ChristoffelTransition
import Poincare.Global.TransitionLawFires

/-!
# Side-condition discharge for local re-anchoring

This module feeds the cutoff-one signed Christoffel transition law into the
re-anchoring bridge.  The remaining hypothesis is the genuine chain-rule
producer for the velocity component of the chart-transition state.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

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
Strict local re-anchor law from the cutoff-one side conditions and the
remaining velocity chain rule.  The cutoff/overlap hypotheses are neighborhood
facts along the shifted source geodesic; they discharge the side conditions of
the signed Christoffel transition law pointwise near each shifted time.
-/
theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_eventually_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ)
    (ht₀ :
      t₀ ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀))
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hx_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        q ∈ (extChartAt I x₀).target)
    (hy_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hχx_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        cutoff (n := n) x₀ q = 1)
    (hχy_chart : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∀ᶠ q in 𝓝 (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1,
        cutoff (n := n) y₀ (chartTransition x₀ y₀ q) = 1)
    (hchain : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun s : ℝ =>
          chartTransitionDeriv x₀ y₀
            (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).1
            (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).2)
        (chartTransitionDeriv x₀ y₀
          (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1
          (-(chartChristoffelField g x₀
              (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2) +
          (fderiv ℝ (chartTransitionDeriv x₀ y₀)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).1
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2)
            (geodesicGermChartSolution g x₀ v₀ (t₀ + t)).2)
        t) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀) := by
  let γ : ℝ → E × E :=
    fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
  let B : ℝ → E :=
    fun t : ℝ =>
      (fderiv ℝ (chartTransitionDeriv x₀ y₀) (γ t).1 (γ t).2) (γ t).2
  have hx_target : ∀ᶠ t in 𝓝 (0 : ℝ),
      (γ t).1 ∈ (extChartAt I x₀).target := by
    filter_upwards [by simpa [γ] using hx_chart] with t ht
    have ht' : ∀ᶠ q in 𝓝 (γ t).1, q ∈ (extChartAt I x₀).target := by
      simpa [γ, extChartAt_target] using ht
    exact mem_of_mem_nhds ht'
  have hy_source : ∀ᶠ t in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ v₀ (t₀ + t) ∈ (extChartAt I y₀).source := by
    filter_upwards [by simpa [γ] using hy_chart] with t ht
    have ht' : ∀ᶠ q in 𝓝 (γ t).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source := by
      simpa [γ, extChartAt_source] using ht
    have hpre :
        (γ t).1 ∈
          {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source} :=
      mem_of_mem_nhds ht'
    have hmem :
        (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source :=
      hpre
    simpa [γ, geodesicGermAt] using hmem
  have hchain' :
      let γ : ℝ → E × E :=
        fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt
          (fun s : ℝ => chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2)
          (chartTransitionDeriv x₀ y₀ (γ t).1
              (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) + B t)
          t := by
    simpa [γ, B] using hchain
  have hchristoffel :
      let γ : ℝ → E × E :=
        fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (chartChristoffelField g y₀
            (chartTransitionState x₀ y₀ γ t).1)
          (chartTransitionState x₀ y₀ γ t).2
          (chartTransitionState x₀ y₀ γ t).2 =
        chartTransitionDeriv x₀ y₀ (γ t).1
          ((chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) - B t := by
    filter_upwards
      [by simpa [γ] using hx_chart,
       by simpa [γ] using hy_chart,
       by simpa [γ] using hχx_chart,
       by simpa [γ] using hχy_chart] with
      t hxt hyt hχxt hχyt
    have hxt' : ∀ᶠ q in 𝓝 (γ t).1,
        q ∈ (extChartAt I x₀).target := by
      simpa [γ, extChartAt_target] using hxt
    have hyt' : ∀ᶠ q in 𝓝 (γ t).1,
        (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source := by
      simpa [γ, extChartAt_source] using hyt
    have hΓ :=
      chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
        (g := g) (x₀ := x₀) (y₀ := y₀) (z := (γ t).1)
        hxt' hyt' hχxt hχyt (γ t).2 (γ t).2
    simpa [chartTransitionState, B] using hΓ
  exact
    shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_signed_christoffel_transition
      (g := g) (x₀ := x₀) (y₀ := y₀) (v₀ := v₀) (t₀ := t₀)
      ht₀ hy₀ hx_target hy_source B hchain' hchristoffel

end GeodesicTransport
end Poincare
