import Poincare.Global.HdiffInstantiate
import Poincare.Global.DifferentiatedCompat

/-!
# The chart-transition Christoffel law

This module closes the pointwise signed Christoffel transition law from the
concrete differentiated metric pullback and the target/source Koszul pairing
identities.
-/

noncomputable section

open Bundle Filter Set
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
On a local cutoff-one chart overlap, the target chart Christoffel field is the
signed transport of the source chart Christoffel field through the chart
transition.
-/
theorem chartChristoffelField_chartTransitionDeriv_eq_signed_transport_of_eventually_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hzN : ∀ᶠ q in 𝓝 z, q ∈ (extChartAt I x₀).target)
    (hyN : ∀ᶠ q in 𝓝 z,
      (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hχxN : ∀ᶠ q in 𝓝 z, cutoff (n := n) x₀ q = 1)
    (hχyN : ∀ᶠ q in 𝓝 z,
      cutoff (n := n) y₀ (chartTransition x₀ y₀ q) = 1)
    (u v : E) :
    (chartChristoffelField g y₀ (chartTransition x₀ y₀ z))
        (chartTransitionDeriv x₀ y₀ z u)
        (chartTransitionDeriv x₀ y₀ z v) =
      chartTransitionDeriv x₀ y₀ z ((chartChristoffelField g x₀ z) u v) -
        (fderiv ℝ (chartTransitionDeriv x₀ y₀) z u) v := by
  have hz : z ∈ (extChartAt I x₀).target := mem_of_mem_nhds hzN
  have hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source := by
    exact mem_of_mem_nhds
      (x := z)
      (s := {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source})
      hyN
  have hχx : cutoff (n := n) x₀ z = 1 := by
    exact mem_of_mem_nhds
      (x := z) (s := {q : E | cutoff (n := n) x₀ q = 1}) hχxN
  have hχy :
      cutoff (n := n) y₀ (chartTransition x₀ y₀ z) = 1 := by
    exact mem_of_mem_nhds
      (x := z)
      (s := {q : E | cutoff (n := n) y₀ (chartTransition x₀ y₀ q) = 1})
      hχyN
  have hσ : ContDiffAt ℝ 2 (chartTransition (n := n) x₀ y₀) z := by
    have hy_chart :
        (extChartAt I x₀).symm z ∈ (chartAt E y₀).source := by
      rwa [extChartAt_source] at hy
    have houter :
        ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I y₀)
          ((extChartAt I x₀).symm z) :=
      contMDiffAt_extChartAt' hy_chart
    have hinnerWithin :
        ContMDiffWithinAt 𝓘(ℝ, E) I 2 ((extChartAt I x₀).symm)
          (range I) z :=
      contMDiffWithinAt_extChartAt_symm_range x₀ hz
    have hinner :
        ContMDiffAt 𝓘(ℝ, E) I 2 ((extChartAt I x₀).symm) z := by
      simpa [ModelWithCorners.range_eq_univ] using hinnerWithin
    have hcomp :
        ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
          (fun q : E => extChartAt I y₀ ((extChartAt I x₀).symm q)) z := by
      simpa [Function.comp_def] using houter.comp z hinner
    exact contMDiffAt_iff_contDiffAt.mp
      (by simpa [chartTransition] using hcomp)
  have hdiff :
      ∀ e a b : E,
        ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z)
            (chartTransitionDeriv x₀ y₀ z e))
          (chartTransitionDeriv x₀ y₀ z a)
          (chartTransitionDeriv x₀ y₀ z b)) +
          chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
            ((fderiv ℝ (chartTransitionDeriv x₀ y₀) z e) a)
            (chartTransitionDeriv x₀ y₀ z b) +
          chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
            (chartTransitionDeriv x₀ y₀ z a)
            ((fderiv ℝ (chartTransitionDeriv x₀ y₀) z e) b) =
        ((fderiv ℝ (chartGeodesicMetric g x₀) z e) a b) :=
    chartGeodesicMetric_differentiated_pullback_hdiff_of_eventually_cutoff_eq_one
      (g := g) (x₀ := x₀) (y₀ := y₀) (z := z)
      hzN hyN hχxN hχyN
  let D : E →L[ℝ] E := chartTransitionDeriv x₀ y₀ z
  let B : E →L[ℝ] E →L[ℝ] E := fderiv ℝ (chartTransitionDeriv x₀ y₀) z
  let lhs : E :=
    (chartChristoffelField g y₀ (chartTransition x₀ y₀ z)) (D u) (D v)
  let rhs : E :=
    D ((chartChristoffelField g x₀ z) u v) - B u v
  have hDinv : D.IsInvertible := by
    have hDmf :
        chartTransitionDeriv (n := n) x₀ y₀ z =
          chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z :=
      chartTransitionDeriv_eq_chartTransitionMFDeriv
        (x₀ := x₀) (y₀ := y₀) hz hy
    subst D
    rw [hDmf]
    dsimp [chartTransitionMFDeriv]
    exact
      (isInvertible_mfderiv_extChartAt hy).comp
        (isInvertible_mfderivWithin_extChartAt_symm hz)
  have hpair : ∀ w : E,
      chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) lhs (D w) =
        chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) rhs (D w) := by
    intro w
    have htarget :=
      chartChristoffelField_pairing_eq_blendedChartMetric
        (g := g) (x₀ := y₀) (z := chartTransition x₀ y₀ z)
        (D u) (D v) (D w)
    have htransport :=
      chartGeodesicMetric_transportedChristoffel_pairing_eq_of_differentiated_pullback
        (g := g) (x₀ := x₀) (y₀ := y₀) (z := z)
        hz hy hχx hχy hσ hdiff u v w
    simpa [lhs, rhs, D, B] using htarget.trans htransport.symm
  have hnd :
      ∀ a : E,
        (∀ b : E,
          chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) a b = 0) →
          a = 0 := by
    intro a ha
    have hbilin :=
      CovariantDerivative.chartBilin_nondegenerate
        (cutoff (n := n) y₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y p hp => g.inner_pos y (v := p) hp) y₀
        (cutoff_nonneg (n := n) y₀) (cutoff_le_one (n := n) y₀)
        (cutoff_support_invertible (n := n) y₀)
        (chartTransition x₀ y₀ z)
    exact hbilin.1 a (by
      intro b
      simpa [chartGeodesicMetric, CovariantDerivative.chartBilin] using ha b)
  apply sub_eq_zero.mp
  apply hnd
  intro ξ
  obtain ⟨e, he⟩ := hDinv
  have hξ : D (e.symm ξ) = ξ := by
    rw [← he]
    exact e.apply_symm_apply ξ
  have hξpair := hpair (e.symm ξ)
  rw [hξ] at hξpair
  calc
    chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) (lhs - rhs) ξ =
        chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) lhs ξ -
          chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z) rhs ξ := by
      simp
    _ = 0 := by
      rw [hξpair]
      ring

end GeodesicTransport
end Poincare
