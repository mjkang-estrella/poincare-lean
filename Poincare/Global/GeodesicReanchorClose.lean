import Poincare.Global.GeodesicReanchorLaw

/-!
# First-order close for geodesic re-anchoring

This module resumes the re-anchoring thread without changing the parked
modules.  It closes the first-order chart-transition gap left in
`GeodesicReanchorLaw`: the total Frechet derivative used by
`chartTransitionState` agrees, on the honest overlap, with the manifold
differential expression used by the chart-metric transport API.

The full transported ODE still needs the velocity-component Christoffel
transition law.  The last theorem below reduces the conditional
`htransport_solves` input to exactly that remaining component.
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
On an honest overlap, the total chart transition has the Frechet derivative
spelled by the manifold chart differential.
-/
theorem chartTransition_hasFDerivAt_chartTransitionMFDeriv
    (x₀ y₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source) :
    HasFDerivAt (chartTransition (n := n) x₀ y₀)
      (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z) z := by
  have hy_chart : (extChartAt I x₀).symm z ∈ (chartAt E y₀).source := by
    rwa [extChartAt_source] at hy
  have houter :
      HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I y₀)
        ((extChartAt I x₀).symm z)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I y₀)
          ((extChartAt I x₀).symm z)) :=
    (mdifferentiableAt_extChartAt hy_chart).hasMFDerivAt
  have hinnerWithin :
      HasMFDerivWithinAt 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) z
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (range I) z) :=
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt
  have hrange : range I ∈ 𝓝 z := by
    rw [ModelWithCorners.range_eq_univ I]
    exact univ_mem
  have hinner :
      HasMFDerivAt 𝓘(ℝ, E) I ((extChartAt I x₀).symm) z
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (range I) z) :=
    hinnerWithin.hasMFDerivAt hrange
  have hcomp := houter.comp z hinner
  simpa [chartTransition, chartTransitionMFDeriv, Function.comp_def]
    using hcomp.hasFDerivAt

/--
The Frechet derivative used by `chartTransitionState` is the manifold
transition differential from `GeodesicReanchorLaw` on the overlap.
-/
theorem chartTransitionDeriv_eq_chartTransitionMFDeriv
    (x₀ y₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source) :
    chartTransitionDeriv (n := n) x₀ y₀ z =
      chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z := by
  exact (chartTransition_hasFDerivAt_chartTransitionMFDeriv
    (x₀ := x₀) (y₀ := y₀) hz hy).fderiv

/--
Metric transport for the actual transition derivative stored in the
first-order state.
-/
theorem chartMetric_chartTransitionDeriv
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source)
    (u v : E) :
    CovariantDerivative.chartMetric g.inner y₀ (chartTransition x₀ y₀ z)
        (chartTransitionDeriv x₀ y₀ z u)
        (chartTransitionDeriv x₀ y₀ z v) =
      CovariantDerivative.chartMetric g.inner x₀ z u v := by
  rw [chartTransitionDeriv_eq_chartTransitionMFDeriv
    (x₀ := x₀) (y₀ := y₀) hz hy]
  exact chartMetric_chartTransitionMFDeriv
    (g := g) (x₀ := x₀) (y₀ := y₀) hy u v

/--
The position component of a transitioned chart-geodesic state satisfies the
target chart's first-order position equation.
-/
theorem chartTransitionState_fst_hasDerivAt
    (x₀ y₀ : M) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField Γ (γ t)) t)
    (hz : (γ t).1 ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source) :
    HasDerivAt
      (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).1)
      (chartTransitionState x₀ y₀ γ t).2 t := by
  have hF := chartTransition_hasFDerivAt_chartTransitionMFDeriv
    (x₀ := x₀) (y₀ := y₀) hz hy
  have hpos : HasDerivAt (fun s : ℝ => (γ s).1) (γ t).2 t :=
    geodesic_position_hasDerivAt hγ
  have hcomp := hF.comp_hasDerivAt t hpos
  have hD := chartTransitionDeriv_eq_chartTransitionMFDeriv
    (x₀ := x₀) (y₀ := y₀) hz hy
  simpa [chartTransitionState, hD, Function.comp_def] using hcomp

/-- Eventual form of `chartTransitionState_fst_hasDerivAt`. -/
theorem chartTransitionState_eventually_fst_hasDerivAt
    (x₀ y₀ : M) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {γ : ℝ → E × E}
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ (geodesicFlowField Γ (γ t)) t)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ), (γ t).1 ∈ (extChartAt I x₀).target)
    (hy : ∀ᶠ t in 𝓝 (0 : ℝ),
      (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt
        (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).1)
        (chartTransitionState x₀ y₀ γ t).2 t := by
  filter_upwards [hγ, hz, hy] with t htγ htz hty
  exact chartTransitionState_fst_hasDerivAt (x₀ := x₀) (y₀ := y₀)
    htγ htz hty

/--
The remaining transition law is now only the velocity component: once that is
proved, the transported state solves the target-anchor chart ODE.
-/
theorem chartTransitionState_eventually_solves_of_velocity_component
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {γ : ℝ → E × E}
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ), (γ t).1 ∈ (extChartAt I x₀).target)
    (hy : ∀ᶠ t in 𝓝 (0 : ℝ),
      (extChartAt I x₀).symm (γ t).1 ∈ (extChartAt I y₀).source)
    (hvel : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).2)
        (-(chartChristoffelField g y₀
            (chartTransitionState x₀ y₀ γ t).1)
          (chartTransitionState x₀ y₀ γ t).2
          (chartTransitionState x₀ y₀ γ t).2) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (chartTransitionState x₀ y₀ γ)
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀ γ t)) t := by
  have hpos := chartTransitionState_eventually_fst_hasDerivAt
    (x₀ := x₀) (y₀ := y₀)
    (Γ := chartChristoffelField g x₀) hγ hz hy
  exact chartTransitionState_eventually_solves_of_components
    (g := g) (x₀ := x₀) (y₀ := y₀) hpos hvel

end GeodesicTransport
end Poincare
