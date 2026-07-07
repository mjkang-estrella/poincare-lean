import Poincare.Global.GeodesicReanchorClose

/-!
# Final local re-anchor assembly

This module keeps the double-anchor reanchor wall narrowed to the single
remaining chart-covariance input: the velocity-component Christoffel transition
for `chartTransitionState`.
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
Strict local re-anchor assembly.  Once the velocity component of the
transitioned shifted state satisfies the target-anchor Christoffel equation,
the shifted `x₀` geodesic germ agrees near `0` with the `y₀`-anchored germ
whose initial velocity is the transported velocity.
-/
theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_velocity_component
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ)
    (ht₀ :
      t₀ ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀))
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hx_target : ∀ᶠ s in 𝓝 (0 : ℝ),
      (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).1 ∈ (extChartAt I x₀).target)
    (hy_source : ∀ᶠ s in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ v₀ (t₀ + s) ∈ (extChartAt I y₀).source)
    (hvel : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun s : ℝ =>
          (chartTransitionState x₀ y₀
            (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) s).2)
        (-(chartChristoffelField g y₀
            (chartTransitionState x₀ y₀
              (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).1)
          (chartTransitionState x₀ y₀
            (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2
          (chartTransitionState x₀ y₀
            (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2)
        t) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀) := by
  let γ : ℝ → E × E := fun s => geodesicGermChartSolution g x₀ v₀ (t₀ + s)
  have hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t := by
    have hspec := (geodesicGermChartSolution_spec g x₀ v₀).2.1
    have hI :
        Ioo (-(geodesicGermRadius g x₀ v₀))
            (geodesicGermRadius g x₀ v₀) ∈ 𝓝 t₀ :=
      Ioo_mem_nhds ht₀.1 ht₀.2
    have hshift :
        ∀ᶠ t in 𝓝 (0 : ℝ),
          t₀ + t ∈
            Ioo (-(geodesicGermRadius g x₀ v₀))
              (geodesicGermRadius g x₀ v₀) := by
      have htend :
          Tendsto (fun t : ℝ => t₀ + t) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
        simpa [Pi.add_apply] using
          ((continuousAt_const : ContinuousAt (fun _ : ℝ => t₀) 0).add
          continuousAt_id).tendsto
      exact htend.eventually hI
    filter_upwards [hshift] with t ht
    have hder := hspec (t₀ + t) ht
    have hlin : HasDerivAt (fun s : ℝ => t₀ + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add t₀
    have hcomp := hder.scomp t hlin
    simpa [γ] using hcomp
  have hy_overlap : ∀ᶠ t in 𝓝 (0 : ℝ),
      (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source := by
    simpa [γ, geodesicGermAt] using hy_source
  have htransport :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt
          (chartTransitionState x₀ y₀ γ)
          (geodesicFlowField (chartChristoffelField g y₀)
            (chartTransitionState x₀ y₀ γ t)) t := by
    exact chartTransitionState_eventually_solves_of_velocity_component
      (g := g) (x₀ := x₀) (y₀ := y₀) (γ := γ)
      hγ hx_target hy_overlap hvel
  exact shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored
    (g := g) (x₀ := x₀) (y₀ := y₀) (v₀ := v₀) (t₀ := t₀)
    hy₀ hy_source htransport

end GeodesicTransport
end Poincare
