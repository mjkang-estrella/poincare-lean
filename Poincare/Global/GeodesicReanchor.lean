import Poincare.Global.GeodesicOverlap

/-!
# Geodesic germ re-anchoring

This module records the part of the geodesic extension step that does not
require the false global-overlap naturality statement.  Near an anchor,
the cutoff is identically `1`, so the blended chart metric has the same
first-order germ as the transported metric of `g`.  Consequently the
Christoffel field satisfies the genuine transported Koszul pairing formula
there.

The remaining transition computation is isolated as the hypothesis that the
transitioned shifted state solves the current-anchor chart ODE.  Once that is
available, same-anchor ODE uniqueness gives the re-anchoring germ equality.
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

section Coefficients

variable (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)

/--
On the cutoff-`1` zone, the blended chart metric is exactly the transported
chart metric of `g`.
-/
theorem blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    {z : E} (hz : cutoff (n := n) x₀ z = 1) :
    CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z =
      CovariantDerivative.chartMetric g.inner x₀ z := by
  exact CovariantDerivative.blendedChartMetric_eq_chartMetric_of_eq_one
    (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀ hz

/--
Near the anchor chart center, the blended chart metric and the transported
chart metric of `g` agree as germs.
-/
theorem blendedChartMetric_eventuallyEq_chartMetric :
    (fun z : E =>
        CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀ z)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)]
    (fun z : E => CovariantDerivative.chartMetric g.inner x₀ z) := by
  filter_upwards [cutoff_eventuallyEq_one (n := n) x₀] with z hz
  exact blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) hz

/--
If the cutoff is `1` as a germ at `z`, then the chart Christoffel field has
the Koszul pairing formula for the genuine transported chart metric of `g`
at `z`.  This is the first-derivative-strength form of "the blended
Christoffel is the transported Christoffel" and is the coefficient identity
needed inside a cutoff-`1` zone.
-/
theorem chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    {z : E} (hz : ∀ᶠ z' in 𝓝 z, cutoff (n := n) x₀ z' = 1)
    (u v w : E) :
    CovariantDerivative.chartMetric g.inner x₀ z
        ((chartChristoffelField g x₀ z) u v) w =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z v) u w) +
          ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z u) v w) -
            ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z w) v u)) := by
  have hGerm :
      (fun z' : E =>
          CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ z')
        =ᶠ[𝓝 z]
      (fun z' : E => CovariantDerivative.chartMetric g.inner x₀ z') := by
    filter_upwards [hz] with z' hz'
    exact blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
      (g := g) (x₀ := x₀) hz'
  have hfd :
      fderiv ℝ
          (fun z' : E =>
            CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
              (backgroundMetric (n := n)) g.inner x₀ z') z =
        fderiv ℝ (fun z' : E => CovariantDerivative.chartMetric g.inner x₀ z') z :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hGerm
  have hz_one : cutoff (n := n) x₀ z = 1 := hz.self_of_nhds
  rw [← blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) hz_one]
  rw [show CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z
        ((chartChristoffelField g x₀ z) u v) w =
      CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z
        ((chartChristoffelField g x₀ z) u v) w from rfl]
  change
      CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z
        (CovariantDerivative.christoffelAt
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀)
          z
          (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ z)
          (CovariantDerivative.chartBilin_nondegenerate
            (cutoff (n := n) x₀) (backgroundMetric (n := n))
            (backgroundMetric_pos (n := n)) g.inner
            (fun y u hu => g.inner_pos y (v := u) hu) x₀
            (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
            (cutoff_support_invertible (n := n) x₀) z)
          v u) w =
        (1 / 2 : ℝ) *
          ((((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z) v) u) w +
            (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z) u) v) w -
              (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z) w) v) u)
  rw [CovariantDerivative.b_christoffelAt]
  rw [hfd]

/--
At the anchor, the chart Christoffel field satisfies the genuine transported
Koszul formula for `g`.
-/
theorem chartChristoffelField_pairing_eq_chartMetric_at_anchor
    (u v w : E) :
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀)
        ((chartChristoffelField g x₀ (extChartAt I x₀ x₀)) u v) w =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
            (extChartAt I x₀ x₀) v) u w) +
          ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
            (extChartAt I x₀ x₀) u) v w) -
            ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀)
              (extChartAt I x₀ x₀) w) v u)) := by
  exact chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    (g := g) (x₀ := x₀) (cutoff_eventuallyEq_one (n := n) x₀) u v w

/--
Near the anchor, every nearby base point is itself in a neighborhood on which
the cutoff is identically `1`; hence the genuine transported Koszul formula
holds throughout a small anchor neighborhood.
-/
theorem chartChristoffelField_eventually_pairing_eq_chartMetric :
    ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀),
      ∀ u v w : E,
        CovariantDerivative.chartMetric g.inner x₀ z
            ((chartChristoffelField g x₀ z) u v) w =
          (1 / 2 : ℝ) *
            (((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z v) u w) +
              ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z u) v w) -
                ((fderiv ℝ (CovariantDerivative.chartMetric g.inner x₀) z w) v u)) := by
  have hlocal :
      ∀ᶠ z in 𝓝 (extChartAt I x₀ x₀),
        ∀ᶠ z' in 𝓝 z, cutoff (n := n) x₀ z' = 1 :=
    eventually_eventually_nhds.2 (cutoff_eventuallyEq_one (n := n) x₀)
  filter_upwards [hlocal] with z hz u v w
  exact chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    (g := g) (x₀ := x₀) hz u v w

end Coefficients

section Reanchor

/--
The velocity obtained by shifting the chosen `x₀` chart solution to time
`t₀` and reading the resulting state in the `y₀` chart.
-/
def reanchoredVelocity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ) : E :=
  (chartTransitionState x₀ y₀
    (fun s : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + s)) 0).2

/--
Re-anchoring from transported-solution input: if the shifted `x₀` germ,
transported to the `y₀` chart, solves the `y₀` chart geodesic system near
`0`, then it agrees as a manifold-valued germ with the chosen geodesic germ
through `y₀` with the transported velocity.

The source hypothesis is the chart-side part of the double-good-zone
condition; it is exactly what lets the first component of the transported
state pull back to the shifted manifold curve.
-/
theorem shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) (v₀ : E) (t₀ : ℝ)
    (hy₀ : geodesicGermAt g x₀ v₀ t₀ = y₀)
    (hy_source : ∀ᶠ s in 𝓝 (0 : ℝ),
      geodesicGermAt g x₀ v₀ (t₀ + s) ∈ (extChartAt I y₀).source)
    (htransport_solves : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt
        (chartTransitionState x₀ y₀
          (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)))
        (geodesicFlowField (chartChristoffelField g y₀)
          (chartTransitionState x₀ y₀
            (fun r : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) s))
        s) :
    (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s))
      =ᶠ[𝓝 (0 : ℝ)]
    geodesicGermAt g y₀ (reanchoredVelocity g x₀ y₀ v₀ t₀) := by
  let η : ℝ → E × E :=
    chartTransitionState x₀ y₀
      (fun s : ℝ => geodesicGermChartSolution g x₀ v₀ (t₀ + s))
  let v₁ : E := reanchoredVelocity g x₀ y₀ v₀ t₀
  have hv₁ : v₁ = (η 0).2 := rfl
  have hη0 : η 0 = (extChartAt I y₀ y₀, v₁) := by
    have hfst : (η 0).1 = extChartAt I y₀ y₀ := by
      have h := congrArg (fun y : M => extChartAt I y₀ y) hy₀
      simpa [η, chartTransitionState, chartTransition, geodesicGermAt] using h
    have hsnd : (η 0).2 = v₁ := hv₁.symm
    exact Prod.ext hfst hsnd
  have hchosen0 :
      geodesicGermChartSolution g y₀ v₁ 0 = (extChartAt I y₀ y₀, v₁) :=
    (geodesicGermChartSolution_spec g y₀ v₁).1
  have hchosen_solves : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt (geodesicGermChartSolution g y₀ v₁)
        (geodesicFlowField (chartChristoffelField g y₀)
          (geodesicGermChartSolution g y₀ v₁ s)) s := by
    have hε := geodesicGermRadius_pos g y₀ v₁
    have hI :
        Ioo (-(geodesicGermRadius g y₀ v₁))
            (geodesicGermRadius g y₀ v₁) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    exact Filter.eventually_of_mem hI
      (geodesicGermChartSolution_spec g y₀ v₁).2.1
  have hη_solves : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField (chartChristoffelField g y₀) (η s)) s := by
    simpa [η] using htransport_solves
  have hpull :
      (fun s : ℝ => (extChartAt I y₀).symm (η s).1)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => geodesicGermAt g x₀ v₀ (t₀ + s)) := by
    filter_upwards [hy_source] with s hs
    have hleft := (extChartAt I y₀).left_inv hs
    simpa [η, chartTransitionState, chartTransition, geodesicGermAt] using hleft
  have huniq :
      (fun s : ℝ => (extChartAt I y₀).symm (η s).1)
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ =>
        (extChartAt I y₀).symm (geodesicGermChartSolution g y₀ v₁ s).1) :=
    pulledback_geodesic_eventuallyEq_of_chartChristoffelField
      (g := g) (x₀ := y₀) (v₀ := v₁)
      (γ := η) (η := geodesicGermChartSolution g y₀ v₁)
      hη0 hchosen0 hη_solves hchosen_solves
  exact hpull.symm.trans huniq

end Reanchor

end GeodesicTransport
end Poincare
