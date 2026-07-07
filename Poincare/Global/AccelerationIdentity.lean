import Poincare.Global.JacobiOscillator

/-!
# Acceleration identity

This module isolates the pointwise coordinate form of the covariant Jacobi
oscillator.  The covariant second derivative is expanded into the raw
coordinate acceleration and the Christoffel correction terms.
-/

noncomputable section

open Bundle Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace AccelerationIdentity

universe u

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

/--
The cutoff-one covariant oscillator, unpacked in coordinates.

The corrected covariant second derivative is
`coordinateJacobiAcceleration` plus the Christoffel correction terms with
`D = K + Γ(V,J)`.  Once the covariant oscillator gives `-J`, this identity
solves for the raw coordinate acceleration.
-/
theorem coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t : ℝ}
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, GeodesicTransport.cutoff (n := 3) x₀ z' = 1)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0) :
    coordinateJacobiAcceleration
        (GeodesicTransport.chartChristoffelField g x₀) (γ t) (Ψ t) =
      -(Ψ t).1 -
        (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) (γ t).1)
          (γ t).2) (γ t).2) (Ψ t).1 +
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
          ((GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2)
          (Ψ t).1 -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (Ψ t).2 -
        (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
          ((Ψ t).2 +
            (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
              (γ t).2 (Ψ t).1) := by
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 :=
    GeodesicTransport.chartChristoffelField g x₀
  let z : E3 := (γ t).1
  let V : E3 := (γ t).2
  let J : E3 := (Ψ t).1
  let K : E3 := (Ψ t).2
  have hcov :
      coordinateCovariantJacobiSecond Γ z V J K = -J := by
    simpa [Γ, z, V, J, K] using
      coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := t)
        htarget hχone hunit horth
  have hunpack :
      coordinateJacobiAcceleration Γ (z, V) (J, K) =
        coordinateCovariantJacobiSecond Γ z V J K -
          (((fderiv ℝ Γ z) V) V) J +
          Γ z (Γ z V V) J -
          Γ z V K -
          Γ z V (K + Γ z V J) := by
    simp [coordinateCovariantJacobiSecond]
    abel
  calc
    coordinateJacobiAcceleration
        (GeodesicTransport.chartChristoffelField g x₀) (γ t) (Ψ t) =
        coordinateJacobiAcceleration Γ (z, V) (J, K) := by
          simp [Γ, z, V, J, K]
    _ = coordinateCovariantJacobiSecond Γ z V J K -
          (((fderiv ℝ Γ z) V) V) J +
          Γ z (Γ z V V) J -
          Γ z V K -
          Γ z V (K + Γ z V J) := hunpack
    _ = -J -
          (((fderiv ℝ Γ z) V) V) J +
          Γ z (Γ z V V) J -
          Γ z V K -
          Γ z V (K + Γ z V J) := by rw [hcov]
    _ = -(Ψ t).1 -
          (((fderiv ℝ (GeodesicTransport.chartChristoffelField g x₀) (γ t).1)
            (γ t).2) (γ t).2) (Ψ t).1 +
          (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
            ((GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (γ t).2)
            (Ψ t).1 -
          (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2 (Ψ t).2 -
          (GeodesicTransport.chartChristoffelField g x₀ (γ t).1) (γ t).2
            ((Ψ t).2 +
              (GeodesicTransport.chartChristoffelField g x₀ (γ t).1)
                (γ t).2 (Ψ t).1) := by
          simp [Γ, z, V, J, K]

end AccelerationIdentity
end Poincare
