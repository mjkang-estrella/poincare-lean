import Poincare.Global.AccelerationIdentity
import Poincare.Global.HarmonicHosted

/-!
# Cartan isometry assembly attempt

This module performs the next non-vacuous hosted assembly step: the
cutoff-one coordinate acceleration identity is fed into the hosted harmonic
derivative theorem.  The one remaining hypothesis is the explicit algebraic
collapse of the correction-bearing raw acceleration formula to the rescaled
harmonic acceleration required by `HarmonicHosted`.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanTheIsometry

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Hosted harmonic derivative from the cutoff-one acceleration identity.

The hypothesis `haccCollapse` is the exact remaining algebraic bridge: after
`AccelerationIdentity` expands the raw coordinate acceleration into
`-J` plus Christoffel correction terms, those terms must collapse to the
rescaled harmonic acceleration `(speed * speed) • (-J)`.
-/
theorem hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_identity
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E × E} {Φ : E → ℝ → E × E} {w : E}
    {speed ε tmin tmax : ℝ}
    (hτmem : ∀ t ∈ Icc (-ε) ε, speed * t ∈ Icc tmin tmax)
    (hΦharmonic : ∀ τ ∈ Icc tmin tmax,
      HasDerivWithinAt (Φ w)
        (harmonicJacobiOperator (Φ w τ)) (Icc tmin tmax) τ)
    (htarget : ∀ t ∈ Icc (-ε) ε,
      (γ t).1 ∈ (extChartAt I x₀).target)
    (hχone : ∀ t ∈ Icc (-ε) ε,
      ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ t ∈ Icc (-ε) ε,
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
    (horth : ∀ t ∈ Icc (-ε) ε,
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1
        (Φ w (speed * t)).1 (γ t).2 = 0)
    (haccCollapse : ∀ t ∈ Icc (-ε) ε,
      -(Φ w (speed * t)).1 -
          (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) (γ t).1)
            (γ t).2) (γ t).2) (Φ w (speed * t)).1 +
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
          ((GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2)
          (Φ w (speed * t)).1 -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
          (speed • (Φ w (speed * t)).2) -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
          ((speed • (Φ w (speed * t)).2) +
            (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
              (γ t).2 (Φ w (speed * t)).1) =
        (speed * speed) • (-(Φ w (speed * t)).1)) :
    ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (fun τ : ℝ =>
          ((Φ w (speed * τ)).1, speed • (Φ w (speed * τ)).2))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2))
        (Icc (-ε) ε) t := by
  have hacc : ∀ t ∈ Icc (-ε) ε,
      coordinateJacobiAcceleration
          (GeodesicTransport.chartChristoffelField g x₀) (γ t)
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) =
        (speed * speed) • (-(Φ w (speed * t)).1) := by
    intro t ht
    have hraw :=
      AccelerationIdentity.coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state
        (g := g) hcurv (x₀ := x₀) (γ := γ)
        (Ψ := fun τ : ℝ =>
          ((Φ w (speed * τ)).1, speed • (Φ w (speed * τ)).2))
        (t := t) (htarget t ht) (hχone t ht) (hunit t ht)
        (by simpa using horth t ht)
    exact hraw.trans (haccCollapse t ht)
  exact
    HarmonicHosted.hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq
      (g := g) (x₀ := x₀) (γ := γ) (Φ := Φ) (w := w)
      (speed := speed) (ε := ε) (tmin := tmin) (tmax := tmax)
      hτmem hΦharmonic hacc

/--
Source-side Cartan action equation after assembling `hΦderHosted` from the
cutoff-one acceleration identity.

This removes the direct hosted-derivative hypothesis from
`CartanIsometryDone.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique`.
The remaining explicit hypothesis is the correction collapse needed to turn
the M5-rigid-51 raw acceleration identity into the rescaled harmonic
acceleration expected by `HarmonicHosted`.
-/
theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_acceleration_identity
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ : ℝ → E × E} {Ψ Φ : E → ℝ → E × E} {v u : E}
    {ρ speed T ε tmin tmax : ℝ}
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hRadial :
      linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul
          (CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) =
        ρ •
          CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u)
    (hε : 0 < ε) (hspeed : speed ≠ 0) (hT_ne : T ≠ 0)
    {aLin rLin LLin KLin : ℝ≥0}
    (hplLinear : IsPicardLindelof
      (fun t : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E),
        T⁻¹ •
          CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u)
      aLin rLin LLin KLin)
    (hΨ0 :
      Ψ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) 0 =
        ((0 : E),
          T⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u))
    (hΨder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (Ψ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) t))
        (Icc (-ε) ε) t)
    (hΨmem : ∀ t ∈ Icc (-ε) ε,
      Ψ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) t ∈
        closedBall
          ((0 : E),
            T⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) aLin)
    (hΦ0 :
      Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) 0 =
        ((0 : E),
          (speed * T)⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u))
    (hτmemHosted : ∀ t ∈ Icc (-ε) ε, speed * t ∈ Icc tmin tmax)
    (htarget : ∀ t ∈ Icc (-ε) ε,
      (γ t).1 ∈ (extChartAt I x₀).target)
    (hχone : ∀ t ∈ Icc (-ε) ε,
      ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hunit : ∀ t ∈ Icc (-ε) ε,
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
    (horth : ∀ t ∈ Icc (-ε) ε,
      CovariantDerivative.chartMetric g.inner x₀ (γ t).1
        (Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1
        (γ t).2 = 0)
    (haccCollapse : ∀ t ∈ Icc (-ε) ε,
      -(Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1 -
          (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) (γ t).1)
            (γ t).2) (γ t).2)
            (Φ (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1 +
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
          ((GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2)
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1 -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
          (speed •
            (Φ (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).2) -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
          ((speed •
              (Φ (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).2) +
            (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
              (γ t).2
              (Φ (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1) =
        (speed * speed) •
          (-(Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1))
    (hΦmemHosted : ∀ t ∈ Icc (-ε) ε,
      ((Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1,
        speed •
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).2) ∈
        closedBall
          ((0 : E),
            T⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) aLin)
    (hTmem : T ∈ Icc (-ε) ε)
    (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {Ahar Rhar Lhar Khar : ℝ≥0}
    (hplHarmonic : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E × E => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E),
        (speed * T)⁻¹ •
          CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u)
      Ahar Rhar Lhar Khar)
    (hΦharmonic : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt
        (Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u))
        (harmonicJacobiOperator
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) t))
        (Icc tmin tmax) t)
    (hΦmemHarmonic : ∀ t ∈ Icc tmin tmax,
      Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) t ∈
        closedBall
          ((0 : E),
            (speed * T)⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) Ahar)
    (hsinmem : ∀ t ∈ Icc tmin tmax,
      jacobiSinState
          ((speed * T)⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) t ∈
        closedBall
          ((0 : E),
            (speed * T)⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) Ahar)
    (hτmem : speed * T ∈ Icc tmin tmax) :
    linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u =
      CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ
        (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u := by
  have hΦderHosted :
      ∀ t ∈ Icc (-ε) ε,
        HasDerivWithinAt
          (fun τ : ℝ =>
            ((Φ (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * τ)).1,
              speed •
                (Φ (CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * τ)).2))
          (linearizedGeodesicFlowFieldAlong
            (GeodesicTransport.chartChristoffelField g x₀) γ t
            ((Φ (CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).1,
              speed •
                (Φ (CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * t)).2))
          (Icc (-ε) ε) t :=
    hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_identity
      (g := g) hcurv (x₀ := x₀) (γ := γ) (Φ := Φ)
      (w := CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u)
      (speed := speed) (ε := ε) (tmin := tmin) (tmax := tmax)
      hτmemHosted hΦharmonic htarget hχone hunit horth haccCollapse
  exact
    CartanIsometryDone.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ) (Φ := Φ) (v := v) (u := u)
      (ρ := ρ) (speed := speed) (T := T) (ε := ε)
      hadd hsmul hRadial hε hspeed hT_ne hplLinear hΨ0 hΨder hΨmem hΦ0
      hΦderHosted hΦmemHosted hTmem hzero hplHarmonic hΦharmonic
      hΦmemHarmonic hsinmem hτmem

end CartanTheIsometry
end Poincare
