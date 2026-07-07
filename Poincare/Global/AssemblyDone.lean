import Poincare.Global.GronwallMembership
import Poincare.Global.IsometryComplete
import Poincare.Global.MembershipBound

/-!
# Assembly with Gronwall norm membership

This module feeds the non-circular Gronwall membership into the bounded
transverse solution package.  The existing public solution feed asks for a
fixed-radius norm membership for every direction `w`; the proof below records
the sharper bounded form actually used by the closed-ball polarization step and
then discharges that bounded membership from `GronwallMembership`.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace AssemblyDone

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

section BoundedSource

/--
Bounded source quadratic norm identity with norm memberships required only for
the bounded transverse directions consumed by the polarization argument.
-/
theorem source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_bounded_membership
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E3 × E3} {Ψ : E3 → ℝ → E3 × E3}
    {v : E3} {T tmin tmax speed : ℝ} (hspeed_ne : speed ≠ 0)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0}
    (hpl : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
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
    (hΨ : ∀ w : E3, ∀ s ∈ Icc tmin tmax,
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
    (hmem : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          (JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1) s,
            JacobiNormSystem.normB g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s,
            JacobiNormSystem.normC g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s) ∈
            closedBall ((0 : ℝ), (0 : ℝ),
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
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
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        JacobiNormSystem.normA g x₀
            (fun τ : ℝ => (γ τ).1)
            (fun τ : ℝ => (Ψ w τ).1) T =
          JacobiNormSystem.speedPinnedScale speed T *
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w) := by
  intro w hwb hw
  exact
    SourcePackage.source_normA_eq_speed_pinned_on_cutoff_one_Icc
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ w)
      (tmin := tmin) (tmax := tmax) (speed := speed)
      (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w))
      hspeed_ne hzero Aop (hpl w hwb) hAop hγ (hΨ w) htarget hχone hspeed
      (horth w hw) hGd (hmem w hwb hw) (hpinnedmem w hwb hw)
      (ha0 w) (hb0 w) (hc0 w) hT

/--
Closed-ball source transverse pairing with bounded actual and pinned
norm memberships.
-/
theorem source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_bounded_membership
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
    (hmemNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          (JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1) s,
            JacobiNormSystem.normB g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s,
            JacobiNormSystem.normC g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s) ∈
            closedBall ((0 : ℝ), (0 : ℝ),
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
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
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
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
    source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_bounded_membership
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
    SolutionsFeed.actual_jacobi_pairing_eq_scalar_of_quadratic_and_endpoint_add
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
Source transverse block with bounded norm memberships, extended from the
closed ball by endpoint homogeneity.
-/
theorem source_transverseTransverse_of_solutions_bounded_membership
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
    (hmemNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
          (JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1) s,
            JacobiNormSystem.normB g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ => (Ψ w τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s,
            JacobiNormSystem.normC g x₀
              (fun τ : ℝ => (γ τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
                  (γ τ).2 (Ψ w τ).1) s) ∈
            closedBall ((0 : ℝ), (0 : ℝ),
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc tmin tmax,
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
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (γ τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 + (chartChristoffelField g x₀ (γ τ).1)
              (γ τ).2 (Ψ w τ).1) 0 =
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
    source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_bounded_membership
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

/--
Source transverse block from enriched packages after feeding the actual norm
membership by the a-priori Gronwall estimate.
-/
theorem source_transverseTransverse_of_enriched_gronwall_feed
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := 0) (tmax := T)
        ⟨(0 : ℝ), by exact ⟨le_rfl, le_of_lt hT⟩⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ))
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
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
  have horth :=
    IsometryComplete.source_orthogonal_of_enriched_packages
      (g := g) (x₀ := x₀) (T := T) (ε := ε) (aPkg := aPkg)
      (α := α) (Ψ := Ψ) (v := v) hT hbase hlin
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  rcases hbase with
    ⟨_hα0, _hbaseFull, _hbase0T, hbaseAt, _hmem, _htargetFull,
      htarget0T, _hcutFull, hχ0T, hspeedBase, hendpoint⟩
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hlin with ⟨_hΨ0, _hΨFull, _hΨ0T, hΨAt, _hflow, _hspeedConst⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_of_lt hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨le_of_lt hT, le_rfl⟩
  have hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).2
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).2 = speed ^ 2 := by
    intro s hs
    exact (hspeedBase s hs).trans hanchorSpeed
  have hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀)
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1 := by
    intro s _hs
    exact IsometryComplete.chartGeodesicMetric_differentiableAt g x₀
      (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1
  have hmemNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc (0 : ℝ) T,
          (JacobiNormSystem.normA g x₀
              (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
              (fun τ : ℝ => (Ψ w τ).1) s,
            JacobiNormSystem.normB g x₀
              (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
              (fun τ : ℝ => (Ψ w τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 +
                  (chartChristoffelField g x₀
                    (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                    (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) s,
            JacobiNormSystem.normC g x₀
              (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
              (fun τ : ℝ =>
                (Ψ w τ).2 +
                  (chartChristoffelField g x₀
                    (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                    (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) s) ∈
            closedBall ((0 : ℝ), (0 : ℝ),
              chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                (T⁻¹ • w) (T⁻¹ • w)) radius := by
    intro w hwb hw s hs
    have hradius_w :
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)| * Real.exp (C * T) +
          |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)| ≤ (radius : ℝ) :=
      (GronwallMembership.qcenter_gronwall_radius_le_of_abs_le
        (hqBound w hwb hw)).trans hgronwallRadius
    have hmem :=
      GronwallMembership.normState_mem_closedBall_qcenter_of_radius_ge
        (g := g) hcurv (x₀ := x₀)
        (γ := α (extChartAt I3 x₀ x₀, T⁻¹ • v)) (Ψ := Ψ w)
        (T := T) (speed := speed) (C := C)
        (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w))
        Aop hAop hC hAopNorm (radius := radius) hradius_w
        hbaseAt (hΨAt w) htarget0T hχ0T hspeed (horth w hw) hGd
        (ha0 w) (hb0 w) (hc0 w) s hs
    simpa [GronwallMembership.normState, GronwallMembership.correctedD] using hmem
  have hpinnedmem : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ s ∈ Icc (0 : ℝ) T,
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
                  (T⁻¹ • w) (T⁻¹ • w)) radius := by
    intro w hwb hw s _hs
    exact
      MembershipBound.speedPinned_mem_closedBall_of_radius_ge
        (speed := speed)
        (q := chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w))
        (t := s) (radius := radius) (hpinnedRadius w hwb hw)
  exact
    source_transverseTransverse_of_solutions_bounded_membership
      (g := g) hcurv (x₀ := x₀)
      (γ := α (extChartAt I3 x₀ x₀, T⁻¹ • v)) (Ψ := Ψ)
      (v := v) (T := T) (tmin := 0) (tmax := T) (speed := speed)
      hspeed_ne hzero hΨadd hΨsmul hTmem hendpoint Aop hRpos hplNorm
      hAop hbaseAt hΨAt htarget0T hχ0T hspeed horth hGd hmemNorm
      hpinnedmem ha0 hb0 hc0

end BoundedSource

section Target

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/--
Target transverse block from enriched packages after feeding the actual norm
membership by the a-priori Gronwall estimate.
-/
theorem target_transverseTransverse_of_enriched_gronwall_feed
    (p₀ : RoundSphere3)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := 0) (tmax := T)
        ⟨(0 : ℝ), by exact ⟨le_rfl, le_of_lt hT⟩⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ))
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC roundSphereMetric3 p₀
          (fun τ : ℝ => (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField roundSphereMetric3 p₀
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
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
  have hanchorSpeedSource :
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀
          (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2 := by
    simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
      using hanchorSpeed
  have hqBoundSource : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax := by
    intro w hwb hw
    exact hqBound w hwb
      (by
        simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
          using hw)
  have hpinnedRadiusSource : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric roundSphereMetric3 p₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ) := by
    intro w hwb hw
    exact hpinnedRadius w hwb
      (by
        simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
          using hw)
  have hsource :=
    source_transverseTransverse_of_enriched_gronwall_feed
      (g := roundSphereMetric3) roundSphereMetric3_hasConstantSectionalCurvature_one
      (x₀ := p₀) (T := T) (ε := ε) (speed := speed) (C := C)
      (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeedSource Aop hRpos
      hplNorm hAop hC hAopNorm hqBoundSource hgronwallRadius
      hpinnedRadiusSource ha0 hb0 hc0
  intro a a'
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric]
    using hsource a a'

end Target

end AssemblyDone
end Poincare
