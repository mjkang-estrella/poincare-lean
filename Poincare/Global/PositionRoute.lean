import Poincare.Global.CartanActionEquations

/-!
# Position-only Cartan action route

This module records the part of the Cartan action equation that survives the
raw-coordinate acceleration refutations.  The consumer only needs the position
endpoint of the transverse linearized state.  Any Christoffel correction belongs
in the missing bridge identifying that position with a covariant Jacobi
position, not in a false raw coordinate harmonic equation.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace PositionRoute

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Source-side action equation from the radial action and the transverse position
endpoint alone.  No hosted derivative equation and no raw-coordinate
acceleration collapse is needed at this consumer level.
-/
theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_transverse_position
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Psi : E → ℝ → E × E} {v u : E} {rho speed T : ℝ}
    (hadd : ∀ w w' : E,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Psi (c • w) T).1 = c • (Psi w T).1)
    (hRadial :
      linearizedEndpointCLM (Ψ := Psi) T hadd hsmul
          (CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) =
        rho •
          CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u)
    (hTransverse :
      (Psi (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
        CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T •
          CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) :
    linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u =
      CartanLocalIsometry.sourceScaledNormalVector g x₀ rho
        (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  let radial : E := CartanPullback.radialPart B v u
  let transverse : E := CartanPullback.transversePart B v u
  let sigma : ℝ := CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T
  let D : E →L[ℝ] E := linearizedEndpointCLM (Ψ := Psi) T hadd hsmul
  have htrans : D transverse = sigma • transverse := by
    simpa [D, B, transverse, sigma] using
      (linearizedEndpointCLM_apply (Ψ := Psi) T hadd hsmul transverse).trans
        hTransverse
  have hradial : D radial = rho • radial := by
    simpa [D, B, radial] using hRadial
  calc
    D u = D (radial + transverse) := by
      rw [CartanPullback.radialPart_add_transversePart (B := B) (v := v) (u := u)]
    _ = D radial + D transverse := by
      simp
    _ = rho • radial + sigma • transverse := by
      rw [hradial, htrans]
    _ = CartanLocalIsometry.sourceScaledNormalVector g x₀ rho sigma v u := by
      rfl

/--
Position-route source action equation.  The second state `Jcov` is the
covariant harmonic Jacobi state: its first component is the position and its
second component is the covariant derivative.  The only bridge to the hosted
linearized state is the endpoint position equality `hendpoint`; derivatives are
not identified.
-/
theorem linearizedEndpointCLM_apply_sourceScaledNormalVector_of_covariant_position
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {Psi Jcov : E → ℝ → E × E} {v u : E} {rho speed T : ℝ}
    (hadd : ∀ w w' : E,
      (Psi (w + w') T).1 = (Psi w T).1 + (Psi w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Psi (c • w) T).1 = c • (Psi w T).1)
    (hRadial :
      linearizedEndpointCLM (Ψ := Psi) T hadd hsmul
          (CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) =
        rho •
          CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v u)
    (hendpoint :
      (Psi (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
        (Jcov (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * T)).1)
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {A R L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun psi : E × E => harmonicJacobiOperator psi)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E),
        (speed * T)⁻¹ •
          CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) A R L K)
    (hJcov : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt
        (Jcov (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u))
        (harmonicJacobiOperator
          (Jcov (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v u) t))
        (Icc tmin tmax) t)
    (hJcovmem : ∀ t ∈ Icc tmin tmax,
      Jcov (CartanPullback.transversePart
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
    (hJcov0 :
      Jcov (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x₀) v u) 0 =
        ((0 : E),
          (speed * T)⁻¹ •
            CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v u))
    (hτmem : speed * T ∈ Icc tmin tmax) :
    linearizedEndpointCLM (Ψ := Psi) T hadd hsmul u =
      CartanLocalIsometry.sourceScaledNormalVector g x₀ rho
        (CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T) v u := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  let transverse : E := CartanPullback.transversePart B v u
  let sigma : ℝ := CartanScaleGeneric.hostedTransverseScaleFromSpeed speed T
  have hsin :
      (Jcov transverse (speed * T)).1 =
        Real.sin (speed * T) • ((speed * T)⁻¹ • transverse) := by
    simpa [B, transverse] using
      jacobi_position_eq_sin_smul_on_Icc
        (w := (speed * T)⁻¹ • transverse) hzero (hpl := hpl)
        (Ψ := Jcov transverse) hJcov hJcovmem hsinmem hJcov0 hτmem
  have hTransverse :
      (Psi transverse T).1 = sigma • transverse := by
    calc
      (Psi transverse T).1 = (Jcov transverse (speed * T)).1 := by
        simpa [B, transverse] using hendpoint
      _ = Real.sin (speed * T) • ((speed * T)⁻¹ • transverse) := hsin
      _ = sigma • transverse := by
        simp [sigma, CartanScaleGeneric.hostedTransverseScaleFromSpeed,
          div_eq_mul_inv, smul_smul]
  exact
    linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_transverse_position
      (g := g) (x₀ := x₀) (Psi := Psi) (v := v) (u := u)
      (rho := rho) (speed := speed) (T := T)
      hadd hsmul hRadial (by simpa [B, transverse, sigma] using hTransverse)

end PositionRoute
end Poincare
