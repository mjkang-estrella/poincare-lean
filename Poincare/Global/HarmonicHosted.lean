import Poincare.Global.CartanIsometryDone

/-!
# Hosted harmonic derivative calculus

This module isolates the derivative-calculus part of the hosted harmonic
conversion.  The remaining geometric input is the pointwise coordinate
acceleration identity for the hosted rescaled oscillator.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace HarmonicHosted

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
The hosted time-rescaling of a harmonic Jacobi state has the derivative
required by the hosted linearized chart-geodesic equation, once the pointwise
coordinate acceleration is identified with the rescaled oscillator
acceleration.
-/
theorem hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {Φ : E → ℝ → E × E} {w : E}
    {speed ε tmin tmax : ℝ}
    (hτmem : ∀ t ∈ Icc (-ε) ε, speed * t ∈ Icc tmin tmax)
    (hΦharmonic : ∀ τ ∈ Icc tmin tmax,
      HasDerivWithinAt (Φ w)
        (harmonicJacobiOperator (Φ w τ)) (Icc tmin tmax) τ)
    (hacc : ∀ t ∈ Icc (-ε) ε,
      coordinateJacobiAcceleration
          (GeodesicTransport.chartChristoffelField g x₀) (γ t)
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) =
        (speed * speed) • (-(Φ w (speed * t)).1)) :
    ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (fun τ : ℝ =>
          ((Φ w (speed * τ)).1, speed • (Φ w (speed * τ)).2))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2))
        (Icc (-ε) ε) t := by
  intro t ht
  let S : Set ℝ := Icc (-ε) ε
  let T : Set ℝ := Icc tmin tmax
  let C : ℝ → E × E := fun τ => Φ w (speed * τ)
  have hscale : HasDerivWithinAt (fun τ : ℝ => speed * τ) speed S t := by
    simpa [S, mul_comm] using
      (hasDerivAt_const_mul (x := t) speed).hasDerivWithinAt
  have hmaps : MapsTo (fun τ : ℝ => speed * τ) S T := by
    intro τ hτ
    exact hτmem τ (by simpa [S] using hτ)
  have hC :
      HasDerivWithinAt C
        (speed • harmonicJacobiOperator (Φ w (speed * t))) S t := by
    have hbase := hΦharmonic (speed * t) (hτmem t ht)
    have hcomp := hbase.scomp_of_eq t hscale hmaps rfl
    simpa [C, S, T, smul_eq_mul] using hcomp
  have hfst :
      HasDerivWithinAt (fun τ : ℝ => (C τ).1)
        (speed • (Φ w (speed * t)).2) S t := by
    have h := hC.hasFDerivWithinAt.fst.hasDerivWithinAt
    simpa [C, harmonicJacobiOperator_apply] using h
  have hsnd :
      HasDerivWithinAt (fun τ : ℝ => speed • (C τ).2)
        ((speed * speed) • (-(Φ w (speed * t)).1)) S t := by
    have h := hC.hasFDerivWithinAt.snd.hasDerivWithinAt
    have hscaled := h.const_smul speed
    simpa [C, harmonicJacobiOperator_apply, smul_smul, mul_comm, mul_left_comm,
      mul_assoc] using hscaled
  have hpair :
      HasDerivWithinAt
        (fun τ : ℝ => ((C τ).1, speed • (C τ).2))
        (speed • (Φ w (speed * t)).2,
          (speed * speed) • (-(Φ w (speed * t)).1)) S t :=
    hfst.prodMk hsnd
  have hfield :
      linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) =
        (speed • (Φ w (speed * t)).2,
          (speed * speed) • (-(Φ w (speed * t)).1)) := by
    let Γ : E → E →L[ℝ] E →L[ℝ] E :=
      GeodesicTransport.chartChristoffelField g x₀
    have hΓd : DifferentiableAt ℝ Γ (γ t).1 := by
      simpa [Γ] using
        (GeodesicTransport.chartChristoffelField_contDiffAt_base
          (g := g) (x₀ := x₀) (z := (γ t).1)).differentiableAt (by norm_num)
    have hoperator :
        linearizedGeodesicFlowOperator Γ (γ t) =
          coordinateJacobiFlowOperator Γ (γ t) :=
      linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator
        (Γ := Γ) (base := γ t) hΓd
    simp [Γ, linearizedGeodesicFlowFieldAlong, hoperator,
      coordinateJacobiFlowOperator_apply, hacc t ht]
  rw [hfield]
  simpa [C, S] using hpair

end HarmonicHosted
end Poincare
