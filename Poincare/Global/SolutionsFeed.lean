import Poincare.Global.BoundedPackage
import Poincare.Global.LinearizedAdditivity

/-!
# Solution-based transverse feeds

This module removes the centered linearized Picard-Lindelof package from the
bounded transverse feed.  The centered package was only used to prove that the
solution with summed initial velocity agrees with the sum of the two individual
solutions at the polarization endpoint.  The hosted solution family already
exports that endpoint additivity, so the bounded feed can consume it directly.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SolutionsFeed

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Polarized cutoff-one endpoint pairing from the three quadratic identities and
the endpoint additivity of the solution family.
-/
theorem actual_jacobi_pairing_eq_scalar_of_quadratic_and_endpoint_add
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ Ψw Ψw' Ψadd : ℝ → E3 × E3}
    {w w' : E3} {S t : ℝ}
    (hJadd : (Ψadd t).1 = (Ψw t).1 + (Ψw' t).1)
    (hquad_w :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w)
    (hquad_w' :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψw' τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w')
    (hquad_add :
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψadd τ).1) t =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w')) :
    chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw' t).1 =
      S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w' := by
  have hww :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw t).1 (Ψw t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w w := by
    simpa [JacobiNormSystem.normA] using hquad_w
  have hww' :
      chartGeodesicMetric g x₀ (γ t).1 (Ψw' t).1 (Ψw' t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) w' w' := by
    simpa [JacobiNormSystem.normA] using hquad_w'
  have hadd :
      chartGeodesicMetric g x₀ (γ t).1 (Ψadd t).1 (Ψadd t).1 =
        S * chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (w + w') (w + w') := by
    simpa [JacobiNormSystem.normA] using hquad_add
  exact
    JacobiNormSystem.polarize_endpoint_pairing_of_quadratic
      (B := chartGeodesicMetric g x₀ (γ t).1)
      (A := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀))
      (S := S)
      (fun u v => chartGeodesicMetric_symm (g := g) (x₀ := x₀) (γ t).1 u v)
      (fun u v =>
        chartGeodesicMetric_symm (g := g) (x₀ := x₀) (extChartAt I3 x₀ x₀) u v)
      (w := w) (w' := w') (Jw := (Ψw t).1) (Jw' := (Ψw' t).1)
      (Jadd := (Ψadd t).1) hJadd hww hww' hadd

section Source

variable [T2Space M]

/--
Source transverse-transverse endpoint formula from bounded norm packages and
endpoint additivity, with no centered linearized PL package.
-/
theorem source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
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
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      CartanMap.sourceAnchorChartMetric g x₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') := by
  intro w w' hw hw' hwb hw'b haddb
  have hcutT : cutoff (n := 3) x₀ (γ T).1 = 1 :=
    (hχone T hT).self_of_nhds
  have hquad :
      ∀ z : E3, z ∈ closedBall (0 : E3) (R : ℝ) →
        CartanMap.sourceAnchorChartMetric g x₀ v z = 0 →
          JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ z τ).1) T =
            JacobiNormSystem.speedPinnedScale speed T *
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • z) (T⁻¹ • z) :=
    BoundedPackage.source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_plNorm_on_closedBall
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ)
      (v := v) (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hT Aop hplNorm hAop hγ hΨderAt htarget hχone hspeed
      horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hwadd : CartanMap.sourceAnchorChartMetric g x₀ v (w + w') = 0 := by
    simp [hw, hw']
  have hPairBlended :
      chartGeodesicMetric g x₀ (γ T).1 (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w') :=
    actual_jacobi_pairing_eq_scalar_of_quadratic_and_endpoint_add
      (g := g) (x₀ := x₀) (γ := γ)
      (Ψw := Ψ w) (Ψw' := Ψ w') (Ψadd := Ψ (w + w'))
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := JacobiNormSystem.speedPinnedScale speed T) (t := T)
      (hJadd := hΨadd w w')
      (hquad_w := hquad w hwb hw)
      (hquad_w' := hquad w' hw'b hw')
      (hquad_add := by simpa [smul_add] using hquad (w + w') haddb hwadd)
  have hPairChart :
      CovariantDerivative.chartMetric g.inner x₀ (γ T).1
          (Ψ w T).1 (Ψ w' T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • w) (T⁻¹ • w') :=
    CascadePinned.chartMetric_pairing_eq_pinned_of_blended_pairing
      (g := g) (x₀ := x₀) (z := (γ T).1)
      (J := (Ψ w T).1) (J' := (Ψ w' T).1)
      (w := T⁻¹ • w) (w' := T⁻¹ • w')
      (S := JacobiNormSystem.speedPinnedScale speed T) hcutT hPairBlended
  simpa [hendpoint] using hPairChart

/--
Source transverse block in the exact shape consumed by `BundleDischarge`, built
from endpoint additivity/homogeneity plus bounded norm packages.
-/
theorem source_transverseTransverse_of_solutions_feed
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := g) x₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField g x₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField g x₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) x₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric g.inner x₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric g.inner x₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
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
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1) (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
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
  have hsmall :=
    source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hΨadd hT hendpoint Aop hplNorm hAop hγ hΨderAt
      htarget hχone hspeed horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hext :=
    BoundedPackage.source_transverseTransverse_extend_from_closedBall
      (g := g) (x₀ := x₀) (Ψ := Ψ) (v := v) (T := T) (speed := speed)
      (R := R) hRpos hΨsmul hsmall
  intro a a'
  exact hext
    (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v a)
    (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v a')
    (PLNormFeed.sourceAnchorChartMetric_transversePart_eq_zero (g := g) (x₀ := x₀) v a)
    (PLNormFeed.sourceAnchorChartMetric_transversePart_eq_zero (g := g) (x₀ := x₀) v a')

end Source

section Target

/--
Target transverse-transverse endpoint formula from bounded norm packages and
endpoint additivity, with no centered linearized PL package.
-/
theorem target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w w' : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
      CartanMap.targetAnchorChartMetric p₀ v w' = 0 →
      w ∈ closedBall (0 : E3) (R : ℝ) →
      w' ∈ closedBall (0 : E3) (R : ℝ) →
      w + w' ∈ closedBall (0 : E3) (R : ℝ) →
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
            (Ψ w T).1 (Ψ w' T).1 =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w') := by
  have horthSource : ∀ w : E3,
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0 := by
    intro w hw
    exact horth w (by
      simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw)
  have hsource :=
    source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall
      (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hΨadd hT hendpoint Aop hplNorm hAop hγ hΨderAt
      htarget hχone hspeed horthSource hGd hmemNorm hpinnedmem ha0 hb0 hc0
  intro w w' hw hw' hwb hw'b haddb
  have hws : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw
  have hw's : CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w' = 0 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using hw'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using hsource w w' hws hw's hwb hw'b haddb

/--
Target transverse block in the exact shape consumed by `BundleDischarge`, built
from endpoint additivity/homogeneity plus bounded norm packages.
-/
theorem target_transverseTransverse_of_solutions_feed
    (p₀ : RoundSphere3) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hT : T ∈ Icc tmin tmax)
    (hendpoint :
      (γ T).1 =
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hγ : ∀ s ∈ Icc tmin tmax,
      HasDerivAt γ
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀) (γ s)) s)
    (hΨderAt : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      HasDerivAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (chartChristoffelField roundSphereMetric3 p₀) γ s (Ψ w s)) s)
    (htarget : ∀ s ∈ Icc tmin tmax,
      (γ s).1 ∈ (extChartAt I3 p₀).target)
    (hχone : ∀ s ∈ Icc tmin tmax,
      ∀ᶠ z' in 𝓝 (γ s).1, cutoff (n := 3) p₀ z' = 1)
    (hspeed : ∀ s ∈ Icc tmin tmax,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (γ s).1 (γ s).2 (γ s).2 = speed ^ 2)
    (horth : ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (γ s).1 (Ψ w s).1 (γ s).2 = 0)
    (hGd : ∀ s ∈ Icc tmin tmax,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀) (γ s).1)
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField roundSphereMetric3 p₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
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
  have hsmall :=
    target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_solutions_on_closedBall
      (p₀ := p₀) (γ := γ) (Ψ := Ψ) (v := v)
      (T := T) (tmin := tmin) (tmax := tmax) (speed := speed)
      hspeed_ne hzero hΨadd hT hendpoint Aop hplNorm hAop hγ hΨderAt
      htarget hχone hspeed horth hGd hmemNorm hpinnedmem ha0 hb0 hc0
  have hext :=
    BoundedPackage.target_transverseTransverse_extend_from_closedBall
      (p₀ := p₀) (Ψ := Ψ) (v := v) (T := T) (speed := speed)
      (R := R) hRpos hΨsmul hsmall
  intro a a'
  exact hext
    (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v a)
    (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v a')
    (PLNormFeed.targetAnchorChartMetric_transversePart_eq_zero (p₀ := p₀) v a)
    (PLNormFeed.targetAnchorChartMetric_transversePart_eq_zero (p₀ := p₀) v a')

end Target

end SolutionsFeed
end Poincare
