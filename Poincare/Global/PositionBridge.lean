import Poincare.Global.JacobiNormClose

/-!
# Position bridge boundary

This module isolates the vector-level obstruction at the proposed bridge.  The
corrected coordinate state has the same position component as the hosted
linearized state, but as a plain chart-coordinate curve its derivative is the
covariant-coordinate first-order system with Christoffel correction terms, not
the raw harmonic operator `(J,D) ↦ (D,-J)`.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace PositionBridge

universe u

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

open GeodesicTransport

/--
The hosted chart-linearized state `Ψ = (J,K)` and the corrected covariant
derivative `D = K + Γ(γ)(γ',J)` share the same position component, but the
plain chart-coordinate derivative of `(J,D)` still carries the connection
terms.  Thus the available cutoff-one oscillator facts yield the covariant
coordinate system

`J' = D - Γ(γ)(γ',J)` and `D' = -J - Γ(γ)(γ',D)`.

This is the exact pointwise boundary before any parallel-frame identification
that would turn the covariant-coordinate system into the abstract harmonic
operator consumed by `jacobi_position_eq_sin_smul_on_Icc`.
-/
theorem correctedCoordinateState_hasDerivAt
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) {γ Ψ : ℝ → E3 × E3} {t : ℝ}
    (hγ : HasDerivAt γ
      (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t)
    (hΨ : HasDerivAt Ψ
      (linearizedGeodesicFlowFieldAlong
        (chartChristoffelField g x₀) γ t (Ψ t)) t)
    (htarget : (γ t).1 ∈ (extChartAt I3 x₀).target)
    (hχone : ∀ᶠ z' in 𝓝 (γ t).1, cutoff (n := 3) x₀ z' = 1)
    (hunit : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (γ t).2 (γ t).2 = 1)
    (horth : CovariantDerivative.chartMetric g.inner x₀ (γ t).1 (Ψ t).1 (γ t).2 = 0) :
    let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := chartChristoffelField g x₀
    let z : ℝ → E3 := fun τ => (γ τ).1
    let V : ℝ → E3 := fun τ => (γ τ).2
    let J : ℝ → E3 := fun τ => (Ψ τ).1
    let K : ℝ → E3 := fun τ => (Ψ τ).2
    let D : ℝ → E3 := fun τ => K τ + Γ (z τ) (V τ) (J τ)
    HasDerivAt (fun τ : ℝ => (J τ, D τ))
      (D t - Γ (z t) (V t) (J t), -J t - Γ (z t) (V t) (D t)) t := by
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := chartChristoffelField g x₀
  let z : ℝ → E3 := fun τ => (γ τ).1
  let V : ℝ → E3 := fun τ => (γ τ).2
  let J : ℝ → E3 := fun τ => (Ψ τ).1
  let K : ℝ → E3 := fun τ => (Ψ τ).2
  let D : ℝ → E3 := fun τ => K τ + Γ (z τ) (V τ) (J τ)
  have hz : HasDerivAt z (V t) t := by
    simpa [z, V, Γ] using
      geodesic_position_hasDerivAt
        (Γ := Γ) (γ := γ) (t := t) hγ
  have hV : HasDerivAt V (-(Γ (z t)) (V t) (V t)) t := by
    simpa [z, V, Γ] using
      geodesic_velocity_hasDerivAt
        (Γ := Γ) (γ := γ) (t := t) hγ
  have hJcoord : HasDerivAt J (K t) t := by
    simpa [J, K, Γ] using
      chart_linearized_fst_hasDerivAt
        (g := g) (x₀ := x₀) (γ := γ) (Ψ := Ψ) hΨ
  have hΓd : DifferentiableAt ℝ Γ (z t) := by
    simpa [Γ, z] using
      (chartChristoffelField_contDiffAt_base (g := g) (x₀ := x₀) (z := (γ t).1)
        |>.differentiableAt (by norm_num))
  have hlinearized_eq :
      linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t) =
        coordinateJacobiFlowOperator Γ (γ t) (Ψ t) := by
    have hoperator :
        linearizedGeodesicFlowOperator Γ (γ t) =
          coordinateJacobiFlowOperator Γ (γ t) := by
      simpa [Γ, z] using
        linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator
          (Γ := Γ) (base := γ t) hΓd
    simp [linearizedGeodesicFlowFieldAlong, hoperator]
  have hKcoord :
      HasDerivAt K
        (coordinateJacobiAcceleration Γ (z t, V t) (J t, K t)) t := by
    have hsnd := hΨ.hasFDerivAt.snd.hasDerivAt
    have hsnd_eq :
        (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t)).2 =
          coordinateJacobiAcceleration Γ (z t, V t) (J t, K t) := by
      rw [hlinearized_eq]
      simp [z, V, J, K]
    have hsnd' :
        HasDerivAt K
          (linearizedGeodesicFlowFieldAlong Γ γ t (Ψ t)).2 t := by
      simpa [K, Γ] using hsnd
    convert hsnd' using 1
    exact hsnd_eq.symm
  have hΓpath :
      HasDerivAt (fun τ : ℝ => Γ (z τ)) ((fderiv ℝ Γ (z t)) (V t)) t := by
    have hcomp :
        HasDerivAt (Γ ∘ z) ((fderiv ℝ Γ (z t)) (V t)) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E3)
        (f := z) (f' := V t) (x := t)
        (l := Γ) (l' := fderiv ℝ Γ (z t))
        hΓd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hΓV :
      HasDerivAt (fun τ : ℝ => Γ (z τ) (V τ))
        (((fderiv ℝ Γ (z t)) (V t)) (V t) +
          Γ (z t) (-(Γ (z t)) (V t) (V t))) t := by
    simpa using hΓpath.clm_apply hV
  have hΓVJ :
      HasDerivAt (fun τ : ℝ => Γ (z τ) (V τ) (J τ))
        ((((fderiv ℝ Γ (z t)) (V t)) (V t) +
            Γ (z t) (-(Γ (z t)) (V t) (V t))) (J t) +
          Γ (z t) (V t) (K t)) t := by
    simpa using hΓV.clm_apply hJcoord
  have hDraw :
      HasDerivAt D
        (coordinateJacobiAcceleration Γ (z t, V t) (J t, K t) +
          ((((fderiv ℝ Γ (z t)) (V t)) (V t) +
              Γ (z t) (-(Γ (z t)) (V t) (V t))) (J t) +
            Γ (z t) (V t) (K t))) t := by
    simpa [D] using hKcoord.add hΓVJ
  have hDcov :
      HasDerivAt D
        (coordinateCovariantJacobiSecond Γ (z t) (V t) (J t) (K t) -
          Γ (z t) (V t) (D t)) t := by
    convert hDraw using 1
    simp [D, coordinateCovariantJacobiSecond, map_add, map_neg]
    abel
  have hosc :
      coordinateCovariantJacobiSecond Γ (z t) (V t) (J t) (K t) = -J t := by
    simpa [Γ, z, V, J, K] using
      coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state
        (g := g) hcurv (x₀ := x₀) (γ := γ) (Ψ := Ψ) (t := t)
        htarget hχone hunit horth
  have hD :
      HasDerivAt D ((-J t) - Γ (z t) (V t) (D t)) t := by
    simpa [hosc] using hDcov
  have hJ :
      HasDerivAt J (D t - Γ (z t) (V t) (J t)) t := by
    convert hJcoord using 1
    simp [D]
  simpa [Γ, z, V, J, K, D] using hJ.prodMk hD

end PositionBridge
end Poincare
