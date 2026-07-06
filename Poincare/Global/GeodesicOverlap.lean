import Poincare.Global.GeodesicGerm
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Chart-overlap scaffolding for geodesic transport

This file introduces the chart-transition state used by the overlap problem.
The transition is deliberately written as the total map
`extChartAt I y₀ ∘ (extChartAt I x₀).symm`; overlap hypotheses in downstream
theorems restrict it to the source where this is the usual partial-equivalence
transition.

The full chart-overlap theorem needs the nontrivial Christoffel
transformation law on an overlap.  The intended route is to derive that law
from `chartLeviCivita_eventuallyEq_closed` at the two anchors, rather than by
a bare second-derivative computation.  The lemmas below fix the state,
initial data, and final ODE assembly point without assuming that missing
transformation law.
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
variable [hM : IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
The model-side transition from the preferred chart at `x₀` to the preferred
chart at `y₀`, written as a total function.  On points whose inverse
`x₀`-chart value lies in the `y₀` chart source, this is the usual overlap map.
-/
def chartTransition (x₀ y₀ : M) : E → E :=
  fun z => extChartAt I y₀ ((extChartAt I x₀).symm z)

/--
The Frechet derivative used to transport chart velocities through
`chartTransition`.  The derivative is total; overlap smoothness hypotheses are
the downstream obligation that identify it with the transition differential
on the actual common source.
-/
def chartTransitionDeriv (x₀ y₀ : M) (z : E) : E →L[ℝ] E :=
  fderiv ℝ (chartTransition (n := n) x₀ y₀) z

/--
The first-order state obtained by reading an `x₀`-chart state in the `y₀`
chart and pushing the velocity by the derivative of the chart transition.
-/
def chartTransitionState (x₀ y₀ : M) (γ : ℝ → E × E) : ℝ → E × E :=
  fun t =>
    (chartTransition x₀ y₀ (γ t).1,
      chartTransitionDeriv x₀ y₀ (γ t).1 (γ t).2)

omit hM in
theorem chartTransition_apply (x₀ y₀ : M) (z : E) :
    chartTransition x₀ y₀ z =
      extChartAt I y₀ ((extChartAt I x₀).symm z) :=
  rfl

omit hM in
theorem chartTransitionDeriv_apply (x₀ y₀ : M) (z v : E) :
    chartTransitionDeriv x₀ y₀ z v =
      fderiv ℝ (chartTransition (n := n) x₀ y₀) z v :=
  rfl

omit hM in
theorem chartTransitionState_fst (x₀ y₀ : M) (γ : ℝ → E × E) (t : ℝ) :
    (chartTransitionState x₀ y₀ γ t).1 =
      chartTransition x₀ y₀ (γ t).1 :=
  rfl

omit hM in
theorem chartTransitionState_snd (x₀ y₀ : M) (γ : ℝ → E × E) (t : ℝ) :
    (chartTransitionState x₀ y₀ γ t).2 =
      chartTransitionDeriv x₀ y₀ (γ t).1 (γ t).2 :=
  rfl

attribute [simp] chartTransition_apply chartTransitionDeriv_apply
  chartTransitionState_fst chartTransitionState_snd

-- Initial data transported from the `x₀` chart to the `y₀` chart.
omit hM in
theorem chartTransitionState_zero
    (x₀ y₀ : M) {γ : ℝ → E × E} {v₀ : E}
    (hγ0 : γ 0 = (extChartAt I x₀ x₀, v₀)) :
    chartTransitionState x₀ y₀ γ 0 =
      (extChartAt I y₀ x₀,
        chartTransitionDeriv x₀ y₀ (extChartAt I x₀ x₀) v₀) := by
  simp [chartTransitionState, chartTransition, hγ0]

/--
Reading the chosen `x₀` geodesic germ in the `y₀` chart is exactly the first
component of the transported chart state.
-/
theorem geodesicGermAt_chartTransitionState_fst
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) :
    (fun t : ℝ =>
        (chartTransitionState x₀ y₀
          (geodesicGermChartSolution g x₀ v₀) t).1) =
      fun t : ℝ => extChartAt I y₀ (geodesicGermAt g x₀ v₀ t) :=
  rfl

/-- Initial state of the chosen geodesic germ after chart transition. -/
theorem geodesicGermAt_chartTransitionState_zero
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) :
    chartTransitionState x₀ y₀ (geodesicGermChartSolution g x₀ v₀) 0 =
      (extChartAt I y₀ x₀,
        chartTransitionDeriv x₀ y₀ (extChartAt I x₀ x₀) v₀) := by
  exact chartTransitionState_zero x₀ y₀
    (geodesicGermChartSolution_spec g x₀ v₀).1

/--
To prove that a transported state solves a chart geodesic system, it is enough
to prove the two component derivative identities.  For chart overlaps, the
first component is the ordinary chain rule for the chart transition; the
second component is exactly the Christoffel transformation law.
-/
theorem geodesicFlowField_hasDerivAt_of_components
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {η : ℝ → E × E} {t : ℝ}
    (hpos : HasDerivAt (fun s : ℝ => (η s).1) (η t).2 t)
    (hvel : HasDerivAt (fun s : ℝ => (η s).2)
      (-(Γ (η t).1) (η t).2 (η t).2) t) :
    HasDerivAt η (geodesicFlowField Γ (η t)) t := by
  simpa [geodesicFlowField] using hpos.prodMk hvel

/-- Eventual version of `geodesicFlowField_hasDerivAt_of_components`. -/
theorem geodesicFlowField_eventually_hasDerivAt_of_components
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {η : ℝ → E × E}
    (hpos : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (η s).1) (η t).2 t)
    (hvel : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (η s).2)
        (-(Γ (η t).1) (η t).2 (η t).2) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η (geodesicFlowField Γ (η t)) t := by
  filter_upwards [hpos, hvel] with t htpos htvel
  exact geodesicFlowField_hasDerivAt_of_components htpos htvel

/--
Specialization of the component assembly lemma to the transition state and
the `y₀` chart Christoffel field.
-/
theorem chartTransitionState_eventually_solves_of_components
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {γ : ℝ → E × E}
    (hpos : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).1)
        (chartTransitionState x₀ y₀ γ t).2 t)
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
  exact geodesicFlowField_eventually_hasDerivAt_of_components hpos hvel

end GeodesicTransport
end Poincare
