import Poincare.Global.CartanExpansionBridge
import Poincare.Global.JacobiOscillator

/-!
# Coefficient evolution for fixed chart vectors

This module records the non-vacuous coefficient-evolution pieces available from
the existing compatibility surface.  The main chart-level identity is the fixed
vector analogue of the constant-speed calculation: the derivative of
`G (z t) w w'` is exactly the two Christoffel pairings obtained by metric
compatibility.

It also pins the scalar ODE suggested by the round-sphere stereographic
coefficient before any source-side use: the explicit conformal factor along a
unit-speed sphere radial chart coefficient is `cos (t / 2) ^ 4`, and it solves
`κ' = -2 tan (t / 2) κ` away from the chart pole.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Metric compatibility in chart coefficients for fixed vectors.  This is the
algebraic endpoint of the Christoffel pairing identity: the directional
derivative of the metric coefficient in direction `v` equals the two
Christoffel pairings with the fixed slots `w` and `w'`.
-/
theorem chartChristoffelField_fixed_pairing_eq_fderiv_metric
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z : E} (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z)
    (v w w' : E) :
    chartGeodesicMetric g x₀ z ((chartChristoffelField g x₀ z) v w) w' +
        chartGeodesicMetric g x₀ z w ((chartChristoffelField g x₀ z) v w') =
      ((fderiv ℝ (chartGeodesicMetric g x₀) z) v) w w' := by
  set G := chartGeodesicMetric g x₀
  set Γ := chartChristoffelField g x₀ z
  have hΓ₁ :
      G z (Γ v w) w' =
        (1 / 2 : ℝ) *
          (((fderiv ℝ G z) w) v w' +
            ((fderiv ℝ G z) v) w w' -
              ((fderiv ℝ G z) w') w v) := by
    have h := chartChristoffelField_pairing_eq_blendedChartMetric
      (g := g) (x₀ := x₀) (z := z) (u := v) (v := w) (w := w')
    simpa [G, Γ] using h
  have hΓ₂ :
      G z (Γ v w') w =
        (1 / 2 : ℝ) *
          (((fderiv ℝ G z) w') v w +
            ((fderiv ℝ G z) v) w' w -
              ((fderiv ℝ G z) w) w' v) := by
    have h := chartChristoffelField_pairing_eq_blendedChartMetric
      (g := g) (x₀ := x₀) (z := z) (u := v) (v := w') (w := w)
    simpa [G, Γ] using h
  have hsymmΓ₂ : G z w (Γ v w') = G z (Γ v w') w := by
    simpa [G, Γ] using
      chartGeodesicMetric_symm (g := g) (x₀ := x₀) z w (Γ v w')
  have hsymm :
      ∀ y p q : E, G y p q = G y q p := by
    intro y p q
    simpa [G] using chartGeodesicMetric_symm (g := g) (x₀ := x₀) y p q
  have hdw : ((fderiv ℝ G z) w) v w' = ((fderiv ℝ G z) w) w' v :=
    CovariantDerivative.fderiv_metric_symm G hGd hsymm w v w'
  have hdw' : ((fderiv ℝ G z) w') v w = ((fderiv ℝ G z) w') w v :=
    CovariantDerivative.fderiv_metric_symm G hGd hsymm w' v w
  have hdv : ((fderiv ℝ G z) v) w' w = ((fderiv ℝ G z) v) w w' :=
    CovariantDerivative.fderiv_metric_symm G hGd hsymm v w' w
  calc
    G z (Γ v w) w' + G z w (Γ v w') =
        G z (Γ v w) w' + G z (Γ v w') w := by rw [hsymmΓ₂]
    _ =
        (1 / 2 : ℝ) *
            (((fderiv ℝ G z) w) v w' +
              ((fderiv ℝ G z) v) w w' -
                ((fderiv ℝ G z) w') w v) +
          (1 / 2 : ℝ) *
            (((fderiv ℝ G z) w') v w +
              ((fderiv ℝ G z) v) w' w -
                ((fderiv ℝ G z) w) w' v) := by rw [hΓ₁, hΓ₂]
    _ = ((fderiv ℝ G z) v) w w' := by
      rw [hdw, hdw', hdv]
      ring

omit [T2Space M] in
/--
Derivative identity for `t ↦ G (z t) w w'` with fixed chart vectors.  The
right-hand side is written in compatibility form, not merely as a Fréchet
derivative.
-/
theorem chart_metric_fixed_pairing_hasDerivAt_compatibility
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {zcurve : ℝ → E} {t : ℝ} {v : E}
    (hz : HasDerivAt zcurve v t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (zcurve t))
    (w w' : E) :
    HasDerivAt
      (fun τ : ℝ => chartGeodesicMetric g x₀ (zcurve τ) w w')
      (chartGeodesicMetric g x₀ (zcurve t)
          ((chartChristoffelField g x₀ (zcurve t)) v w) w' +
        chartGeodesicMetric g x₀ (zcurve t) w
          ((chartChristoffelField g x₀ (zcurve t)) v w')) t := by
  set G := chartGeodesicMetric g x₀
  have hGpath :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ))
        ((fderiv ℝ G (zcurve t)) v) t := by
    have hcomp :
        HasDerivAt (G ∘ zcurve) ((fderiv ℝ G (zcurve t)) v) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E)
        (f := zcurve) (f' := v) (x := t)
        (l := G) (l' := fderiv ℝ G (zcurve t))
        hGd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hw : HasDerivAt (fun _ : ℝ => w) 0 t :=
    hasDerivAt_const t w
  have hw' : HasDerivAt (fun _ : ℝ => w') 0 t :=
    hasDerivAt_const t w'
  have hGw :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ) w)
        (((fderiv ℝ G (zcurve t)) v) w) t := by
    simpa using hGpath.clm_apply hw
  have hraw :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ) w w')
        (((fderiv ℝ G (zcurve t)) v) w w') t := by
    simpa using hGw.clm_apply hw'
  have hcompat :=
    chartChristoffelField_fixed_pairing_eq_fderiv_metric
      (g := g) (x₀ := x₀) (z := zcurve t) hGd v w w'
  convert hraw using 1

end GeodesicTransport

namespace CoefficientEvolution

local notation "E" => ClosedSmoothModel 3

/-- Scalar linear ODE operator `x ↦ a * x`, bundled as a continuous linear map. -/
def scalarLinearODE (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.id ℝ ℝ

@[simp]
theorem scalarLinearODE_apply (a x : ℝ) :
    scalarLinearODE a x = a * x := by
  simp [scalarLinearODE]

/--
Uniqueness for the scalar coefficient ODE on an `Icc`, stated in the same
Picard-Lindelöf style as `GeodesicLinearized.linearODE_solution_uniqueOn_Icc`.
-/
theorem scalar_weight_eq_of_same_ode_on_Icc
    {a : ℝ → ℝ} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {κ₁ κ₂ : ℝ → ℝ} {κ₀ : ℝ} {A r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun t x => scalarLinearODE (a t) x)
      (tmin := tmin) (tmax := tmax) t₀ κ₀ A r L K)
    (hκ₁ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt κ₁ (a t * κ₁ t) (Icc tmin tmax) t)
    (hκ₁mem : ∀ t ∈ Icc tmin tmax, κ₁ t ∈ closedBall κ₀ A)
    (hκ₂ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt κ₂ (a t * κ₂ t) (Icc tmin tmax) t)
    (hκ₂mem : ∀ t ∈ Icc tmin tmax, κ₂ t ∈ closedBall κ₀ A)
    (h₀ : κ₁ t₀ = κ₂ t₀) :
    EqOn κ₁ κ₂ (Icc tmin tmax) :=
  linearODE_solution_uniqueOn_Icc
    (A := fun t => scalarLinearODE (a t))
    (t₀ := t₀) (x₀ := κ₀) (a := A) (r := r) (L := L) (K := K)
    hpl
    (by
      intro t ht
      simpa using hκ₁ t ht)
    hκ₁mem
    (by
      intro t ht
      simpa using hκ₂ t ht)
    hκ₂mem h₀

/--
The pinned scalar weight from the round-sphere stereographic conformal factor
along a radial coefficient `‖z(t)‖ = 2 tan (t / 2)`.
-/
def roundSpherePinnedWeight (t : ℝ) : ℝ :=
  Real.cos (t / 2) ^ 4

/-- The scalar coefficient in the pinned round-sphere weight ODE. -/
def roundSpherePinnedODECoefficient (t : ℝ) : ℝ :=
  -2 * Real.tan (t / 2)

/-- Pinning check: the explicit round-sphere coefficient solves the proposed ODE. -/
theorem roundSpherePinnedWeight_hasDerivAt
    (t : ℝ) :
    HasDerivAt roundSpherePinnedWeight
      (roundSpherePinnedODECoefficient t * roundSpherePinnedWeight t) t := by
  unfold roundSpherePinnedWeight roundSpherePinnedODECoefficient
  have hcos :
      HasDerivAt (fun s : ℝ => Real.cos (s / 2))
        (-(Real.sin (t / 2) * (1 / 2))) t := by
    simpa [one_div, div_eq_mul_inv] using
      (Real.hasDerivAt_cos (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
  have hpow :
      HasDerivAt (fun s : ℝ => Real.cos (s / 2) ^ 4)
        (4 * Real.cos (t / 2) ^ 3 * (-(Real.sin (t / 2) * (1 / 2)))) t := by
    simpa using hcos.pow 4
  convert hpow using 1
  by_cases hcoszero : Real.cos (t / 2) = 0
  · simp [hcoszero]
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hcoszero]
    ring

/--
The stereographic conformal scalar reduces to the pinned `cos^4` coefficient
on the radial chart curve `r = 2 tan (t / 2)`, away from the stereographic pole.
-/
theorem stereographicScalarConformalFactor_two_tan_half
    {t : ℝ} (hcos : Real.cos (t / 2) ≠ 0) :
    CartanExpansionBridge.stereographicScalarConformalFactor
        (2 * Real.tan (t / 2)) =
      roundSpherePinnedWeight t := by
  unfold CartanExpansionBridge.stereographicScalarConformalFactor
    roundSpherePinnedWeight
  rw [Real.tan_eq_sin_div_cos]
  have hpyth : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (t / 2)
  field_simp [hcos]
  nlinarith [sq_nonneg (Real.cos (t / 2))]

end CoefficientEvolution

end Poincare
