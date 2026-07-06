import Poincare.Global.GeodesicPathLength
import Poincare.Global.GeodesicReanchor

/-!
# Radial geodesic length bridge

This module records the exact tangent-norm identification for inverse-chart
curves.  The path-length formula and sharp distance bound need the PL flow to
remain in the cutoff-`1` zone, so the PL specialization below keeps that
hypothesis explicit.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal

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
For an inverse-chart curve, the manifold derivative is the inverse-chart
tangent map applied to the chart derivative.
-/
theorem inverseChartCurve_mfderiv_eq_of_hasDerivAt
    (x₀ : M) {z : ℝ → E} {u : E} {s : ℝ}
    (hz : z s ∈ (extChartAt I x₀).target)
    (hzder : HasDerivAt z u s) :
    mfderiv 𝓘(ℝ) I
        (fun r : ℝ => (extChartAt I x₀).symm (z r)) s 1 =
      (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
        (range I) (z s)) u := by
  have hsymm_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) I
        ((extChartAt I x₀).symm) (range I) (z s) :=
    mdifferentiableWithinAt_extChartAt_symm (x := x₀) hz
  have hz_mdiff_within :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ, E) z univ s :=
    hzder.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.mdifferentiableWithinAt
  have hpre : z ⁻¹' range I ∈ 𝓝[univ] s := by
    rw [(closedSmoothModelWithCorners n).range_eq_univ]
    simp
  have hchain :
      mfderivWithin 𝓘(ℝ) I
          (((extChartAt I x₀).symm : E → M) ∘ z) univ s =
        (mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x₀).symm)
          (range I) (z s)).comp
          (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) z univ s) :=
    mfderivWithin_comp_of_preimage_mem_nhdsWithin
      s hsymm_within hz_mdiff_within hpre (uniqueMDiffWithinAt_univ 𝓘(ℝ))
  have hz_apply : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) z univ s 1 = u := by
    rw [mfderivWithin_univ, hzder.hasFDerivAt.hasMFDerivAt.mfderiv]
    change (ContinuousLinearMap.toSpanSingleton ℝ u) (1 : ℝ) = u
    exact ContinuousLinearMap.toSpanSingleton_apply_one (R₁ := ℝ) u
  rw [show (fun r : ℝ => (extChartAt I x₀).symm (z r)) =
      (((extChartAt I x₀).symm : E → M) ∘ z) from rfl]
  rw [← mfderivWithin_univ, hchain, ContinuousLinearMap.comp_apply, hz_apply]

/--
The Riemannian fiber e-norm of the inverse-chart curve velocity is the square
root of the transported chart metric pairing.
-/
theorem inverseChartCurve_enorm_mfderiv_eq_chartMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ℝ → E} {u : E} {s : ℝ}
    (hz : z s ∈ (extChartAt I x₀).target)
    (hzder : HasDerivAt z u s) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ‖mfderiv 𝓘(ℝ) I
        (fun r : ℝ => (extChartAt I x₀).symm (z r)) s 1‖ₑ =
      ENNReal.ofReal
        (Real.sqrt (CovariantDerivative.chartMetric g.inner x₀ (z s) u u)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [← ofReal_norm_eq_enorm]
  congr 1
  rw [norm_eq_sqrt_real_inner]
  congr 1
  rw [ClosedSmoothRiemannianMetric.fiber_inner_eq]
  rw [inverseChartCurve_mfderiv_eq_of_hasDerivAt (x₀ := x₀) hz hzder]
  rw [CovariantDerivative.chartMetric_apply]

/--
On the cutoff-`1` zone, the preceding transported-chart norm identity is the
same identity with the blended chart metric used by the geodesic ODE.
-/
theorem inverseChartCurve_enorm_mfderiv_eq_chartGeodesicMetric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : ℝ → E} {u : E} {s : ℝ}
    (hz : z s ∈ (extChartAt I x₀).target)
    (hcut : cutoff (n := n) x₀ (z s) = 1)
    (hzder : HasDerivAt z u s) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ‖mfderiv 𝓘(ℝ) I
        (fun r : ℝ => (extChartAt I x₀).symm (z r)) s 1‖ₑ =
      ENNReal.ofReal
        (Real.sqrt (chartGeodesicMetric g x₀ (z s) u u)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [inverseChartCurve_enorm_mfderiv_eq_chartMetric
    (g := g) (x₀ := x₀) hz hzder]
  have hmetric :=
    blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
      (g := g) (x₀ := x₀) hcut
  change
    ENNReal.ofReal
        (Real.sqrt (CovariantDerivative.chartMetric g.inner x₀ (z s) u u)) =
      ENNReal.ofReal
        (Real.sqrt
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ (z s) u u))
  rw [hmetric]

/--
PL-flow specialization of the integrand identification on interior times,
with the cutoff-`1` requirement made explicit.
-/
theorem plFlowCurve_enorm_mfderiv_eq_chartGeodesicMetric_of_mem_Ioo
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ε : ℝ} {α : E × E → ℝ → E × E} {v₀ : E}
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαtarget : ∀ t ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) t).1 ∈ (extChartAt I x₀).target)
    {s : ℝ} (hs : s ∈ Ioo (-ε) ε)
    (hcut :
      cutoff (n := n) x₀ (α (extChartAt I x₀ x₀, v₀) s).1 = 1) :
    let c : ℝ → M :=
      fun r => (extChartAt I x₀).symm
        (α (extChartAt I x₀ x₀, v₀) r).1
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ‖mfderiv 𝓘(ℝ) I c s 1‖ₑ =
      ENNReal.ofReal
        (Real.sqrt
          (chartGeodesicMetric g x₀
            (α (extChartAt I x₀ x₀, v₀) s).1
            (α (extChartAt I x₀ x₀, v₀) s).2
            (α (extChartAt I x₀ x₀, v₀) s).2)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  have htarget :
      (α (extChartAt I x₀ x₀, v₀) s).1 ∈ (extChartAt I x₀).target :=
    hαtarget s (Ioo_subset_Icc_self hs)
  have hder :
      HasDerivAt
        (fun r : ℝ => (α (extChartAt I x₀ x₀, v₀) r).1)
        (α (extChartAt I x₀ x₀, v₀) s).2 s :=
    plFlowPosition_hasDerivAt_of_mem_Ioo
      (g := g) (x₀ := x₀) hαder hs
  exact inverseChartCurve_enorm_mfderiv_eq_chartGeodesicMetric
    (g := g) (x₀ := x₀) htarget hcut hder

end GeodesicTransport
end Poincare
