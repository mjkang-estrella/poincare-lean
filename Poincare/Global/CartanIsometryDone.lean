import Poincare.Global.CartanEndpointUnique

/-!
# Cartan isometry final composition boundary

This module performs the available non-vacuous composition after
`CartanEndpointUnique`: the endpoint equality is no longer a standalone
hypothesis for the source action equation.  It is produced by hosted
linearized uniqueness and immediately fed into
`CartanActionEquations.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic`.

The remaining boundary for the requested punctured normal-ball isometry is the
geometric instantiation of the hosted uniqueness hypotheses below, especially
the conversion showing that the time-rescaled harmonic state solves the same
hosted linearized chart-geodesic equation.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanIsometryDone

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Source-side action equation after feeding the hosted endpoint uniqueness
theorem.  Compared to `CartanActionEquations`, this theorem no longer assumes
the endpoint equality directly; it derives it from
`CartanEndpointUnique.hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc`.
-/
theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {Ψ Φ : E → ℝ → E × E} {v u : E}
    {ρ speed T ε : ℝ}
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
    (hΦderHosted : ∀ t ∈ Icc (-ε) ε,
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
        (Icc (-ε) ε) t)
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
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
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
  have hendpoint :
      (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
        (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * T)).1 :=
    CartanEndpointUnique.hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc
      (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ) (Φ := Φ)
      (w := CartanPullback.transversePart
        (CartanMap.sourceAnchorChartMetric g x₀) v u)
      (ε := ε) (T := T) (speed := speed)
      hε hspeed hT_ne hplLinear hΨ0 hΨder hΨmem hΦ0
      hΦderHosted hΦmemHosted hTmem
  exact
    CartanActionEquations.linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
      (g := g) (x₀ := x₀) (Ψ := Ψ) (Φ := Φ) (v := v) (u := u)
      (ρ := ρ) (speed := speed) (T := T)
      hadd hsmul hRadial hendpoint hzero hplHarmonic
      hΦharmonic hΦmemHarmonic hsinmem hΦ0 hτmem

end CartanIsometryDone
end Poincare
