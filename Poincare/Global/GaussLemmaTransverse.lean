import Poincare.Global.GaussLemmaRadial

/-!
# Transverse chart Gauss identity

This module freezes the pointwise transverse Gauss calculation for a
two-parameter chart-geodesic variation.  The named smooth-dependence interface
from `Poincare.Global.GaussLemmaRadial` supplies the common chart-geodesic
family and the ODE in the time variable.  The remaining payload is exactly the
classical smooth-dependence output needed to read off the `s`-derivatives and
commute the mixed derivative:

* `J t = ∂ₛ (Φ (v + s • w) t).1`;
* `K t = ∂ₛ (Φ (v + s • w) t).2`;
* `∂ₜ J t = K t`.

Under that payload, differentiating the metric pairing in `t` and the speed in
`s` gives

`∂ₜ G(γ)(J, γ') = (1 / 2) * ∂ₛ G(γ)(γ', γ')`.

The theorem below is deliberately not an integration theorem.  The final
transverse Gauss statement follows by integrating this scalar ODE on the common
existence interval once the smooth-dependence interface exports the derivative
payload globally on the rectangle.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Derivative in the variation parameter of the chart-geodesic speed scalar.
This is the right-hand side in the transverse Gauss identity.
-/
theorem chart_geodesic_variation_speed_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z v : ℝ → E} {s : ℝ} {J K : E}
    (hz : HasDerivAt z J s) (hv : HasDerivAt v K s)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z s)) :
    HasDerivAt
      (fun σ : ℝ => chartGeodesicMetric g x₀ (z σ) (v σ) (v σ))
      (((fderiv ℝ (chartGeodesicMetric g x₀) (z s)) J) (v s) (v s) +
        chartGeodesicMetric g x₀ (z s) K (v s) +
          chartGeodesicMetric g x₀ (z s) (v s) K) s := by
  have hGpath :
      HasDerivAt
        (fun σ : ℝ => chartGeodesicMetric g x₀ (z σ))
        ((fderiv ℝ (chartGeodesicMetric g x₀) (z s)) J) s := by
    have hcomp :
        HasDerivAt
          ((chartGeodesicMetric g x₀) ∘ z)
          ((fderiv ℝ (chartGeodesicMetric g x₀) (z s)) J) s :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E)
        (f := z) (f' := J) (x := s)
        (l := chartGeodesicMetric g x₀)
        (l' := fderiv ℝ (chartGeodesicMetric g x₀) (z s))
        hGd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hGv :
      HasDerivAt
        (fun σ : ℝ => chartGeodesicMetric g x₀ (z σ) (v σ))
        (((fderiv ℝ (chartGeodesicMetric g x₀) (z s)) J) (v s) +
          chartGeodesicMetric g x₀ (z s) K) s := by
    simpa using hGpath.clm_apply hv
  simpa [ContinuousLinearMap.add_apply] using hGv.clm_apply hv

omit [T2Space M] in
/--
Derivative in time of the transverse metric pairing along a chart geodesic.
The Christoffel pairing identity and symmetry of the metric derivative reduce
the result to half of the variation derivative of the speed.
-/
theorem chart_geodesic_transverse_pairing_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z v J : ℝ → E} {t : ℝ} {K : E}
    (hz : HasDerivAt z (v t) t)
    (hv : HasDerivAt v (-(chartChristoffelField g x₀ (z t)) (v t) (v t)) t)
    (hJ : HasDerivAt J K t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt
      (fun τ : ℝ => chartGeodesicMetric g x₀ (z τ) (J τ) (v τ))
      ((1 / 2 : ℝ) *
        (((fderiv ℝ (chartGeodesicMetric g x₀) (z t)) (J t)) (v t) (v t) +
          chartGeodesicMetric g x₀ (z t) K (v t) +
            chartGeodesicMetric g x₀ (z t) (v t) K)) t := by
  set G := chartGeodesicMetric g x₀
  set Γ : E := (chartChristoffelField g x₀ (z t)) (v t) (v t)
  have hGpath :
      HasDerivAt
        (fun τ : ℝ => G (z τ))
        ((fderiv ℝ G (z t)) (v t)) t := by
    have hcomp :
        HasDerivAt (G ∘ z) ((fderiv ℝ G (z t)) (v t)) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E)
        (f := z) (f' := v t) (x := t)
        (l := G) (l' := fderiv ℝ G (z t)) hGd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hGJ :
      HasDerivAt
        (fun τ : ℝ => G (z τ) (J τ))
        (((fderiv ℝ G (z t)) (v t)) (J t) + G (z t) K) t := by
    simpa using hGpath.clm_apply hJ
  have hraw :
      HasDerivAt
        (fun τ : ℝ => G (z τ) (J τ) (v τ))
        ((((fderiv ℝ G (z t)) (v t)) (J t) + G (z t) K) (v t) +
          G (z t) (J t) (-Γ)) t := by
    simpa [Γ] using hGJ.clm_apply hv
  have hΓpair : G (z t) Γ (J t) =
      (1 / 2 : ℝ) *
        (((fderiv ℝ G (z t)) (v t)) (v t) (J t) +
          ((fderiv ℝ G (z t)) (v t)) (v t) (J t) -
            ((fderiv ℝ G (z t)) (J t)) (v t) (v t)) := by
    have h := chartChristoffelField_pairing_eq_blendedChartMetric
      (g := g) (x₀ := x₀) (z := z t) (u := v t) (v := v t) (w := J t)
    simpa [G, Γ] using h
  have hsymmΓ : G (z t) (J t) Γ = G (z t) Γ (J t) := by
    simpa [G] using chartGeodesicMetric_symm
      (g := g) (x₀ := x₀) (z := z t) (v := J t) (w := Γ)
  have hdsymm : ((fderiv ℝ G (z t)) (v t)) (J t) (v t) =
      ((fderiv ℝ G (z t)) (v t)) (v t) (J t) := by
    exact CovariantDerivative.fderiv_metric_symm G hGd
      (fun y p q => by
        simpa [G] using chartGeodesicMetric_symm (g := g) (x₀ := x₀) y p q)
      (v t) (J t) (v t)
  have hGKV : G (z t) (v t) K = G (z t) K (v t) := by
    simpa [G] using chartGeodesicMetric_symm
      (g := g) (x₀ := x₀) (z := z t) (v := v t) (w := K)
  convert hraw using 1
  simp only [ContinuousLinearMap.add_apply, map_neg]
  rw [hsymmΓ, hΓpair, hdsymm, hGKV]
  ring

omit [T2Space M] in
/--
Pointwise two-parameter transverse Gauss identity.

Here `Φ s t` is the first-order chart geodesic state, `J` is the variation
field `∂ₛ (Φ s t).1`, and `K` is `∂ₛ (Φ s t).2`.  The hypothesis
`HasDerivAt J (K t) t` is the mixed-derivative commutation payload.
-/
theorem chart_geodesic_transverse_variation_identity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {Φ : ℝ → ℝ → E × E} {J K : ℝ → E} {s t : ℝ}
    (ht : HasDerivAt (Φ s)
      (geodesicFlowField (chartChristoffelField g x₀) (Φ s t)) t)
    (hJ : HasDerivAt J (K t) t)
    (hs_pos : HasDerivAt (fun σ : ℝ => (Φ σ t).1) (J t) s)
    (hs_vel : HasDerivAt (fun σ : ℝ => (Φ σ t).2) (K t) s)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (Φ s t).1) :
    ∃ pairDeriv speedDeriv : ℝ,
      HasDerivAt
        (fun τ : ℝ =>
          chartGeodesicMetric g x₀ (Φ s τ).1 (J τ) (Φ s τ).2)
        pairDeriv t ∧
      HasDerivAt
        (fun σ : ℝ =>
          chartGeodesicMetric g x₀ (Φ σ t).1 (Φ σ t).2 (Φ σ t).2)
        speedDeriv s ∧
      pairDeriv = (1 / 2 : ℝ) * speedDeriv := by
  let speedDeriv : ℝ :=
    ((fderiv ℝ (chartGeodesicMetric g x₀) (Φ s t).1) (J t)) (Φ s t).2 (Φ s t).2 +
      chartGeodesicMetric g x₀ (Φ s t).1 (K t) (Φ s t).2 +
        chartGeodesicMetric g x₀ (Φ s t).1 (Φ s t).2 (K t)
  refine ⟨(1 / 2 : ℝ) * speedDeriv, speedDeriv, ?_, ?_, rfl⟩
  · have hz : HasDerivAt (fun τ : ℝ => (Φ s τ).1) (Φ s t).2 t :=
      geodesic_position_hasDerivAt (Γ := chartChristoffelField g x₀) ht
    have hv : HasDerivAt (fun τ : ℝ => (Φ s τ).2)
        (-(chartChristoffelField g x₀ (Φ s t).1) (Φ s t).2 (Φ s t).2) t :=
      geodesic_velocity_hasDerivAt (Γ := chartChristoffelField g x₀) ht
    simpa [speedDeriv] using
      chart_geodesic_transverse_pairing_hasDerivAt
        (g := g) (x₀ := x₀)
        (z := fun τ : ℝ => (Φ s τ).1)
        (v := fun τ : ℝ => (Φ s τ).2)
        (J := J) (t := t) (K := K t) hz hv hJ hGd
  · simpa [speedDeriv] using
      chart_geodesic_variation_speed_hasDerivAt
        (g := g) (x₀ := x₀)
        (z := fun σ : ℝ => (Φ σ t).1)
        (v := fun σ : ℝ => (Φ σ t).2)
        (s := s) (J := J t) (K := K t) hs_pos hs_vel hGd

omit [T2Space M] in
/--
The named smooth-dependence interface supplies the common chart-geodesic family
and the time-ODE part of the transverse identity.  The displayed final
implication records precisely the additional derivative payload that a
quantitative smooth-dependence theorem must export at each `(s, t)`.
-/
theorem chartGeodesicInitialVelocitySmoothDependence_exists_transverse_variation_identity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (hdep : ChartGeodesicInitialVelocitySmoothDependence g x₀) :
    ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : E → ℝ → E × E,
      (∀ v₀ : E, ‖v₀‖ < δ →
        Φ v₀ 0 = (extChartAt I x₀ x₀, v₀)) ∧
      (∀ v₀ : E, ‖v₀‖ < δ →
        ∀ t ∈ Ioo (-ε) ε,
          HasDerivAt (Φ v₀)
            (geodesicFlowField (chartChristoffelField g x₀) (Φ v₀ t)) t) ∧
      ContDiffOn ℝ 2 (Function.uncurry Φ)
        (Metric.ball (0 : E) δ ×ˢ Ioo (-ε) ε) ∧
      ∀ {v w : E} {s t : ℝ} {J K : ℝ → E},
        ‖v + s • w‖ < δ → t ∈ Ioo (-ε) ε →
        HasDerivAt J (K t) t →
        HasDerivAt (fun σ : ℝ => (Φ (v + σ • w) t).1) (J t) s →
        HasDerivAt (fun σ : ℝ => (Φ (v + σ • w) t).2) (K t) s →
        DifferentiableAt ℝ (chartGeodesicMetric g x₀) (Φ (v + s • w) t).1 →
        ∃ pairDeriv speedDeriv : ℝ,
          HasDerivAt
            (fun τ : ℝ =>
              chartGeodesicMetric g x₀ (Φ (v + s • w) τ).1 (J τ)
                (Φ (v + s • w) τ).2)
            pairDeriv t ∧
          HasDerivAt
            (fun σ : ℝ =>
              chartGeodesicMetric g x₀ (Φ (v + σ • w) t).1
                (Φ (v + σ • w) t).2 (Φ (v + σ • w) t).2)
            speedDeriv s ∧
          pairDeriv = (1 / 2 : ℝ) * speedDeriv := by
  rcases hdep with ⟨δ, hδ, ε, hε, Φ, hinit, hode, hsmooth⟩
  refine ⟨δ, hδ, ε, hε, Φ, hinit, hode, hsmooth, ?_⟩
  intro v w s t J K hvst ht hJ hs_pos hs_vel hGd
  exact chart_geodesic_transverse_variation_identity
    (g := g) (x₀ := x₀) (Φ := fun r τ => Φ (v + r • w) τ)
    (J := J) (K := K) (s := s) (t := t)
    (hode (v + s • w) hvst t ht) hJ hs_pos hs_vel hGd

end GeodesicTransport
end Poincare
