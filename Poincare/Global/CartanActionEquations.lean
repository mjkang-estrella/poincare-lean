import Poincare.Global.CartanScaleGeneric
import Poincare.Global.JacobiOscillator
import Poincare.Global.LinearizedCLM

/-!
# Cartan action equations

This module records one non-vacuous action-equation step for the Cartan
local-isometry route.  It converts the chart-coordinate sine value supplied by
the harmonic Jacobi uniqueness theorem into the radial/transverse action of a
fixed linearized endpoint CLM.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanActionEquations

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Source-side radial/transverse action equation for a linearized endpoint CLM.

The radial action is supplied separately by the ray-law derivative.  The
transverse action is proved here from the chart-coordinate harmonic Jacobi
value at the rescaled time `speed * T`, producing the hosted scale
`sin (speed * T) / (speed * T)`.
-/
theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Ψ Φ : E → ℝ → E × E} {v u : E} {ρ speed T : ℝ}
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
    (hendpoint :
      (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
        (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * T)).1)
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {A R L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E × E => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E),
        (speed * T)⁻¹ •
          CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) A R L K)
    (hΦharmonic : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt
        (Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u))
        (harmonicJacobiOperator
          (Φ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) t))
        (Icc tmin tmax) t)
    (hΦmem : ∀ t ∈ Icc tmin tmax,
      Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) t ∈
        closedBall
          ((0 : E),
            (speed * T)⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) A)
    (hsinmem : ∀ t ∈ Icc tmin tmax,
      jacobiSinState
          ((speed * T)⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u) t ∈
        closedBall
          ((0 : E),
            (speed * T)⁻¹ •
              CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v u) A)
    (hΦ0 :
      Φ (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) 0 =
        ((0 : E),
          (speed * T)⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u))
    (hτmem : speed * T ∈ Icc tmin tmax) :
    linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul u =
      CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ
        (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  let r : E := CartanPullback.radialPart B v u
  let w : E := CartanPullback.transversePart B v u
  let σ : ℝ := CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T
  let D : E →L[ℝ] E := linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul
  have htrans_value : (Ψ w T).1 = σ • w := by
    have hsin :
        (Φ w (speed * T)).1 = Real.sin (speed * T) • ((speed * T)⁻¹ • w) :=
      jacobi_position_eq_sin_smul_on_Icc
        (w := (speed * T)⁻¹ • w) hzero (hpl := hpl) (Ψ := Φ w)
        hΦharmonic hΦmem hsinmem hΦ0 hτmem
    calc
      (Ψ w T).1 = (Φ w (speed * T)).1 := by
        simpa [B, w] using hendpoint
      _ = Real.sin (speed * T) • ((speed * T)⁻¹ • w) := hsin
      _ = σ • w := by
        simp [σ, CartanScaleGeneric.hostedTransverseScaleFromSpeed, div_eq_mul_inv,
          smul_smul]
  have htrans : D w = σ • w := by
    simpa [D] using
      (linearizedEndpointCLM_apply (Ψ := Ψ) T hadd hsmul w).trans htrans_value
  have hradial : D r = ρ • r := by
    simpa [D, B, r] using hRadial
  calc
    D u = D (r + w) := by
      rw [CartanPullback.radialPart_add_transversePart (B := B) (v := v) (u := u)]
    _ = D r + D w := by
      simp
    _ = ρ • r + σ • w := by
      rw [hradial, htrans]
    _ = CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ σ v u := by
      rfl

end CartanActionEquations
end Poincare
