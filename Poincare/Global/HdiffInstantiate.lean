import Poincare.Global.PullbackDifferentiate
import Poincare.Global.TransportedCompatibility

/-!
# Concrete chart instantiation of the differentiated pullback law

This module instantiates the abstract differentiated-pullback calculus lemma
with the chart geodesic metrics and chart transition data on a local
cutoff-one overlap.
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
On a local cutoff-one chart overlap, the abstract differentiated-pullback
lemma specializes to the concrete chart geodesic metrics, chart transition,
and chart-transition derivative.
-/
theorem chartGeodesicMetric_differentiated_pullback_hdiff_of_eventually_cutoff_eq_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hzN : ∀ᶠ q in 𝓝 z, q ∈ (extChartAt I x₀).target)
    (hyN : ∀ᶠ q in 𝓝 z,
      (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source)
    (hχxN : ∀ᶠ q in 𝓝 z, cutoff (n := n) x₀ q = 1)
    (hχyN : ∀ᶠ q in 𝓝 z,
      cutoff (n := n) y₀ (chartTransition x₀ y₀ q) = 1) :
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
      ((fderiv ℝ (chartGeodesicMetric g x₀) z e) a b) := by
  have hz : z ∈ (extChartAt I x₀).target := mem_of_mem_nhds hzN
  have hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source := by
    exact mem_of_mem_nhds
      (x := z)
      (s := {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I y₀).source})
      hyN
  have hσC2 : ContDiffAt ℝ 2 (chartTransition (n := n) x₀ y₀) z := by
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
  have hsigma : HasFDerivAt (chartTransition (n := n) x₀ y₀)
      (chartTransitionDeriv x₀ y₀ z) z := by
    simpa [chartTransitionDeriv] using
      (hσC2.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have hDcont : ContDiffAt ℝ 1 (chartTransitionDeriv (n := n) x₀ y₀) z := by
    simpa [chartTransitionDeriv] using
      (hσC2.fderiv_right (m := 1) (by norm_num))
  have hD : HasFDerivAt (chartTransitionDeriv (n := n) x₀ y₀)
      (fderiv ℝ (chartTransitionDeriv x₀ y₀) z) z :=
    (hDcont.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M =>
                TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hG0C2 : ContDiff ℝ 2 (chartGeodesicMetric g x₀) := by
    simpa [chartGeodesicMetric] using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
        htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
        (cutoff_tsupport (n := n) x₀) hg2)
  have hG1C2 : ContDiff ℝ 2 (chartGeodesicMetric g y₀) := by
    simpa [chartGeodesicMetric] using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := n) y₀) (backgroundMetric (n := n)) g.inner y₀
        htwo_add_one_le_top (cutoff_contDiff (n := n) y₀)
        (cutoff_tsupport (n := n) y₀) hg2)
  have hG0 : HasFDerivAt (chartGeodesicMetric g x₀)
      (fderiv ℝ (chartGeodesicMetric g x₀) z) z :=
    (hG0C2.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have hG1 : HasFDerivAt (chartGeodesicMetric g y₀)
      (fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z))
      (chartTransition x₀ y₀ z) :=
    (hG1C2.contDiffAt.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have hpull : ∀ a b : E,
      (fun q : E =>
        chartGeodesicMetric g y₀ (chartTransition x₀ y₀ q)
          (chartTransitionDeriv x₀ y₀ q a)
          (chartTransitionDeriv x₀ y₀ q b)) =ᶠ[𝓝 z]
        (fun q : E => chartGeodesicMetric g x₀ q a b) := by
    intro a b
    filter_upwards [hzN, hyN, hχxN, hχyN] with q hqz hqy hχx hχy
    exact chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one
      (g := g) (x₀ := x₀) (y₀ := y₀) (z := q)
      hqz hqy hχx hχy a b
  exact differentiated_pullback_hdiff_of_eventuallyEq
    (G0 := chartGeodesicMetric g x₀)
    (G1 := chartGeodesicMetric g y₀)
    (sigma := chartTransition x₀ y₀)
    (D := chartTransitionDeriv x₀ y₀)
    hsigma hD hG0 hG1 hpull

end GeodesicTransport
end Poincare
