import Poincare.Global.BundleDischarge
import Poincare.Global.SpeedGeneric

/-!
# PL norm feed for transverse blocks

This module records the non-vacuous feed from the speed-generic
Picard-Lindelöf norm package into the source and target transverse-transverse
endpoint blocks used by `BundleDischarge`.

It does not construct the `hplNorm` packages.  It shows that once those exact
packages are available at the hosted datum, the transverse blocks land in the
shape consumed by the bundle theorem.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace PLNormFeed

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

omit [T2Space M] in
/-- Source-anchor transverse parts are orthogonal to the radial vector. -/
theorem sourceAnchorChartMetric_transversePart_eq_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (v a : E3) :
    CartanMap.sourceAnchorChartMetric g x₀ v
      (CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x₀) v a) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  exact
    CartanPullback.transversePart_pair_self_left
      (B := CartanMap.sourceAnchorChartMetric g x₀) (v := v) (u := a)
      (CartanMap.sourceAnchorChartMetric_symm g x₀)
      (CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv)

/-- Target-anchor transverse parts are orthogonal to the radial vector. -/
theorem targetAnchorChartMetric_transversePart_eq_zero
    (p₀ : RoundSphere3) (v a : E3) :
    CartanMap.targetAnchorChartMetric p₀ v
      (CartanPullback.transversePart
        (CartanMap.targetAnchorChartMetric p₀) v a) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  exact
    CartanPullback.transversePart_pair_self_left
      (B := CartanMap.targetAnchorChartMetric p₀) (v := v) (u := a)
      (CartanMap.targetAnchorChartMetric_symm p₀)
      (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)

/--
Source transverse-transverse endpoint block obtained from the speed-generic
interval package, after specializing both input slots to transverse parts.
-/
theorem source_transverseTransverse_of_plNorm_feed
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (GeodesicTransport.chartChristoffelField g x₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (GeodesicTransport.chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField g x₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField g x₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField g x₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField g x₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        GeodesicTransport.chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
  have hfeed :=
    SourcePackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT
      hendpoint Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  intro a a'
  exact hfeed
    (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v a)
    (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v a')
    (sourceAnchorChartMetric_transversePart_eq_zero (g := g) (x₀ := x₀) v a)
    (sourceAnchorChartMetric_transversePart_eq_zero (g := g) (x₀ := x₀) v a')

/--
Target transverse-transverse endpoint block obtained from the speed-generic
interval package, after specializing both input slots to transverse parts.
-/
theorem target_transverseTransverse_of_plNorm_feed
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {aLin rLin LipLin KLin : ℝ≥0}
    (hplLinear : ∀ w w' : E3,
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (γ s) ψ)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
    (hΨderWithin : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
      Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
    (hΨ0 : ∀ w : E3, Ψ w 0 = ((0 : E3), T⁻¹ • w))
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) v)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3,
      IsPicardLindelof
        (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
            (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, GeodesicTransport.cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ
        (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
            (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
            (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
            (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
            (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
              (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
                (γ τ).2 (Ψ w τ).1) 0 =
        GeodesicTransport.chartGeodesicMetric roundSphereMetric3 p₀
          (extChartAt I3 p₀ p₀) (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a') := by
  have hfeed :=
    TargetPackage.target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
      (p₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hplLinear hΨderWithin hmem_add hmem_sum hΨ0 hT
      hendpoint Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  intro a a'
  exact hfeed
    (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v a)
    (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v a')
    (targetAnchorChartMetric_transversePart_eq_zero (p₀ := p₀) v a)
    (targetAnchorChartMetric_transversePart_eq_zero (p₀ := p₀) v a')

end PLNormFeed
end Poincare
