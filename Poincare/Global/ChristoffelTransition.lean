import Poincare.Global.ReanchorLawFinal

/-!
# Christoffel transition assembly for re-anchoring

This module isolates the chart-change calculation still missing from the
exported API.  If the derivative of the chart-transition differential carries
the source geodesic acceleration plus the second-derivative correction, and
the target Christoffel field satisfies the corresponding signed transition
identity, then the velocity-component hypothesis consumed by
`ReanchorLawFinal` follows.
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
Re-anchor assembly from the signed chart-change formula for Christoffels.

Here `B t` is the second-derivative correction
`D²(chartTransition x₀ y₀)((γ t).2, (γ t).2)` along the shifted source
geodesic.  The signed identity

`Γ¹(Dσ v, Dσ v) = Dσ(Γ⁰(v,v)) - B`

is the form compatible with the convention used by `geodesicFlowField`,
namely `γ₂' = -Γ(γ₁)(γ₂,γ₂)`.
-/
theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_signed_christoffel_transition
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ)
    (ht₀ :
      t₀ ∈ Ioo (-(geodesicGermRadius g x₀ v₀)) (geodesicGermRadius g x₀ v₀))
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hx_target : ∀ᶠ s in 𝓝 (0 : ℝ),
      (geodesicGermChartSolution g x₀ v₀ (t₀ + s)).1 ∈ (extChartAt I x₀).target)
    (hy_source : ∀ᶠ s in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ v₀ (t₀ + s) ∈ (extChartAt I y₀).source)
    (B : ℝ → E)
    (hchain :
      let γ : ℝ → E × E :=
        fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt
          (fun s : ℝ => chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2)
          (chartTransitionDeriv x₀ y₀ (γ t).1
              (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) + B t)
          t)
    (hchristoffel :
      let γ : ℝ → E × E :=
        fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (chartChristoffelField g y₀
            (chartTransitionState x₀ y₀ γ t).1)
          (chartTransitionState x₀ y₀ γ t).2
          (chartTransitionState x₀ y₀ γ t).2 =
        chartTransitionDeriv x₀ y₀ (γ t).1
          ((chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) - B t) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀) := by
  let γ : ℝ → E × E :=
    fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)
  have hchain' :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt
          (fun s : ℝ => chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2)
          (chartTransitionDeriv x₀ y₀ (γ t).1
              (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) + B t)
          t := by
    simpa [γ] using hchain
  have hchristoffel' :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        (chartChristoffelField g y₀
            (chartTransitionState x₀ y₀ γ t).1)
          (chartTransitionState x₀ y₀ γ t).2
          (chartTransitionState x₀ y₀ γ t).2 =
        chartTransitionDeriv x₀ y₀ (γ t).1
          ((chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) - B t := by
    simpa [γ] using hchristoffel
  have hvel :
      ∀ᶠ t in 𝓝 (0 : ℝ),
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
          t := by
    filter_upwards [hchain', hchristoffel'] with t ht hΓ
    have htarget :
        chartTransitionDeriv x₀ y₀ (γ t).1
            (-(chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2) + B t =
          -(chartChristoffelField g y₀
              (chartTransitionState x₀ y₀ γ t).1)
            (chartTransitionState x₀ y₀ γ t).2
            (chartTransitionState x₀ y₀ γ t).2 := by
      rw [hΓ]
      simp only [map_neg]
      abel
    rw [htarget] at ht
    simpa [γ, chartTransitionState] using ht
  exact
    shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored_of_velocity_component
      (g := g) (x₀ := x₀) (y₀ := y₀) (v₀ := v₀) (t₀ := t₀)
      ht₀ hy₀ hx_target hy_source hvel

end GeodesicTransport
end Poincare
