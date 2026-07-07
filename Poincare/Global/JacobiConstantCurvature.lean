import Poincare.Global.GeodesicLinearized
import Poincare.Global.ConformalCurvature

/-!
# Constant-curvature Jacobi seed

This file records the chart-level algebra needed for the Cartan metric
comparison step.

Conventions:

* `chartCurvatureOf Γ z u v w` is the repository curvature convention
  `R(u,v)w`.
* `coordinateJacobiAcceleration Γ (z,v) (J,K)` is the plain coordinate
  second derivative `J''` read from the first-order linearized geodesic flow.
  It is not yet the covariant second derivative.
* With the geodesic substitution `v' = -Γ(v,v)`, the covariant second
  derivative is the expression `coordinateCovariantJacobiSecond` below.
  For a symmetric Christoffel field, and the corresponding derivative
  symmetry in the two vector slots, it is exactly `R(v,J)v`.

For the stereographic sphere Christoffel field, `R(v,J)v = -J` under unit speed
and transverse orthogonality for the conformal chart metric.  This is the
oscillator sign consumed by the sine solution at the end of the file.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace NNReal

namespace Poincare

section LinearizedExpansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option synthInstance.maxHeartbeats 1000000 in
/--
The derivative of the first-order geodesic vector field is the expanded
coordinate Jacobi operator.  This identifies the `fderiv`-based
`linearizedGeodesicFlowOperator` with the concrete `DΓ + Γ` formula.
-/
theorem hasFDerivAt_geodesicFlowField_coordinateJacobiFlowOperator
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {base : E × E}
    (hΓ : DifferentiableAt ℝ Γ base.1) :
    HasFDerivAt (geodesicFlowField Γ) (coordinateJacobiFlowOperator Γ base) base := by
  have hp1 : HasFDerivAt (fun p : E × E => p.1) (ContinuousLinearMap.fst ℝ E E) base :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hp2 : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) base :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hΓp : HasFDerivAt (fun p : E × E => Γ p.1)
      ((fderiv ℝ Γ base.1).comp (ContinuousLinearMap.fst ℝ E E)) base := by
    simpa [Function.comp_def] using
      (HasFDerivAt.comp (x := base) (f := fun p : E × E => p.1)
        (g := Γ) (g' := fderiv ℝ Γ base.1) hΓ.hasFDerivAt hp1)
  have hΓpv := hΓp.clm_apply hp2
  have hΓpvv := hΓpv.clm_apply hp2
  have hprod := hp2.prodMk hΓpvv.neg
  convert hprod using 1
  · apply ContinuousLinearMap.ext
    rintro ⟨J, K⟩
    simp [coordinateJacobiFlowOperator]
    abel

/-- Pointwise `fderiv` form of
`hasFDerivAt_geodesicFlowField_coordinateJacobiFlowOperator`. -/
theorem linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {base : E × E}
    (hΓ : DifferentiableAt ℝ Γ base.1) :
    linearizedGeodesicFlowOperator Γ base = coordinateJacobiFlowOperator Γ base := by
  rw [linearizedGeodesicFlowOperator,
    (hasFDerivAt_geodesicFlowField_coordinateJacobiFlowOperator
      (Γ := Γ) (base := base) hΓ).fderiv]

end LinearizedExpansion

section CurvatureLink

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Raw coordinate Jacobi acceleration expressed through the repository curvature
slot `R(v,J)v`, plus the connection correction terms.  This is the chart
calculation before passing from plain `J''` to the covariant second derivative.
-/
theorem coordinateJacobiAcceleration_eq_chartCurvatureOf_remainder
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (z v J K : E) :
    coordinateJacobiAcceleration Γ (z, v) (J, K) =
      chartCurvatureOf Γ z v J v
        - ((fderiv ℝ Γ z) v) J v
        - Γ z v (Γ z J v)
        + Γ z J (Γ z v v)
        - Γ z K v - Γ z v K := by
  simp [coordinateJacobiAcceleration, chartCurvatureOf]
  abel

/--
The covariant second derivative along a geodesic, written in chart coordinates.
The `- Γ z (Γ z v v) J` term is the geodesic substitution `v' = -Γ(v,v)`.
-/
def coordinateCovariantJacobiSecond
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (z v J K : E) : E :=
  coordinateJacobiAcceleration Γ (z, v) (J, K)
    + ((fderiv ℝ Γ z) v) v J
    - Γ z (Γ z v v) J
    + Γ z v K
    + Γ z v (K + Γ z v J)

/--
Under Christoffel symmetry and the matching derivative symmetry, the covariant
Jacobi second derivative is exactly `R(v,J)v` in repository slots.
-/
theorem coordinateCovariantJacobiSecond_eq_chartCurvatureOf
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (z v J K : E)
    (hΓsymm : ∀ a b : E, Γ z a b = Γ z b a)
    (hDsymm : ((fderiv ℝ Γ z) v) v J = ((fderiv ℝ Γ z) v) J v) :
    coordinateCovariantJacobiSecond Γ z v J K =
      chartCurvatureOf Γ z v J v := by
  simp [coordinateCovariantJacobiSecond, coordinateJacobiAcceleration, chartCurvatureOf]
  rw [hDsymm, hΓsymm K v, hΓsymm (Γ z v v) J, hΓsymm v J]
  abel

end CurvatureLink

section ConstantCurvatureContraction

/--
The algebraic KN contraction used by a constant-curvature-one chart identity:
if `v` has unit `G`-length and `J` is transverse to `v`, then the lowered
curvature form `-(1/2) * KN(G,G)(v,J,v,a)` is `-G(J,a)`.
-/
theorem chartTensorKulkarniNomizu_unit_orthogonal_contraction
    {E : Type*} (G : E → E → ℝ) (v J a : E)
    (hvv : G v v = 1) (hJv : G J v = 0) :
    -(1 / 2 : ℝ) * chartTensorKulkarniNomizu G G v J v a = -G J a := by
  simp [chartTensorKulkarniNomizu, hvv, hJv]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Metric-lowered sphere-chart curvature contraction.  This mirrors
`conformalChartMetric_chartCurvatureOf_sphereChristoffel`, specialized to a
unit-speed transverse pair.
-/
theorem conformalChartMetric_chartCurvatureOf_sphereChristoffel_unit_orthogonal
    [FiniteDimensional ℝ E] (z v J a : E)
    (hunit :
      conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z v v = 1)
    (horth :
      conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z J v = 0) :
    conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z
        (chartCurvatureOf (sphereChristoffel (E := E)) z v J v) a =
      -conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z J a := by
  rw [conformalChartMetric_chartCurvatureOf_sphereChristoffel]
  exact chartTensorKulkarniNomizu_unit_orthogonal_contraction
    (G := conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z)
    (v := v) (J := J) (a := a) hunit horth

/--
Vector form of the same sphere-chart contraction: in these curvature slots,
`R(v,J)v = -J` for a unit-speed vector `v` and transverse vector `J`.
-/
theorem chartCurvatureOf_sphereChristoffel_unit_orthogonal
    [FiniteDimensional ℝ E] (z v J : E)
    (hunit :
      conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z v v = 1)
    (horth :
      conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z J v = 0) :
    chartCurvatureOf (sphereChristoffel (E := E)) z v J v = -J := by
  have hunit' : stereoInvFunAuxConformalFactor z * ‖v‖ ^ 2 = 1 := by
    simpa [conformalChartMetricForm] using hunit
  have horth' : stereoInvFunAuxConformalFactor z * inner ℝ J v = 0 := by
    simpa [conformalChartMetricForm] using horth
  apply ext_inner_right ℝ
  intro a
  rw [chartCurvatureOf_sphereChristoffel_eq]
  simp [inner_sub_left, inner_smul_left]
  ring_nf
  rw [horth', hunit']
  ring

end ConstantCurvatureContraction

section SinSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order harmonic oscillator operator `(J,K) ↦ (K,-J)`. -/
def harmonicJacobiOperator : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod (-(ContinuousLinearMap.fst ℝ E E))

@[simp]
theorem harmonicJacobiOperator_apply (ψ : E × E) :
    harmonicJacobiOperator ψ = (ψ.2, -ψ.1) := by
  rfl

/-- The sine/cosine first-order state for `J'' = -J`. -/
def jacobiSinState (w : E) (t : ℝ) : E × E :=
  (Real.sin t • w, Real.cos t • w)

@[simp]
theorem jacobiSinState_zero (w : E) :
    jacobiSinState w 0 = (0, w) := by
  simp [jacobiSinState]

/-- The candidate sine state solves the first-order oscillator system. -/
theorem jacobiSinState_hasDerivAt (w : E) (t : ℝ) :
    HasDerivAt (jacobiSinState w)
      (harmonicJacobiOperator (jacobiSinState w t)) t := by
  have hsin : HasDerivAt (fun τ : ℝ => Real.sin τ • w) (Real.cos t • w) t :=
    (Real.hasDerivAt_sin t).smul_const w
  have hcos : HasDerivAt (fun τ : ℝ => Real.cos τ • w) ((-Real.sin t) • w) t :=
    (Real.hasDerivAt_cos t).smul_const w
  have hprod := hsin.prodMk hcos
  simpa [jacobiSinState] using hprod

/--
Uniqueness wrapper for the sine solution, using the repository's linear-ODE
Picard-Lindelöf uniqueness theorem.  Any first-order solution of `(J,K)' =
(K,-J)` with initial state `(0,w)` agrees with the sine/cosine state on the
PL interval, provided both curves remain in the same closed ball.
-/
theorem jacobiSinState_uniqueOn_Icc
    {tmin tmax : ℝ} (w : E) (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E × E => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩ ((0 : E), w) a r L K)
    {Ψ : ℝ → E × E}
    (hΨ : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ t)) (Icc tmin tmax) t)
    (hΨmem : ∀ t ∈ Icc tmin tmax, Ψ t ∈ closedBall ((0 : E), w) a)
    (hsinmem : ∀ t ∈ Icc tmin tmax, jacobiSinState w t ∈ closedBall ((0 : E), w) a)
    (hΨ0 : Ψ 0 = ((0 : E), w)) :
    EqOn Ψ (jacobiSinState w) (Icc tmin tmax) := by
  refine linearODE_solution_uniqueOn_Icc
    (A := fun _ : ℝ => harmonicJacobiOperator)
    (t₀ := ⟨(0 : ℝ), hzero⟩) (x₀ := ((0 : E), w)) hpl hΨ hΨmem ?_
    hsinmem ?_
  · intro t _ht
    exact (jacobiSinState_hasDerivAt w t).hasDerivWithinAt
  · change Ψ 0 = jacobiSinState w 0
    simp [hΨ0]

end SinSolution

end Poincare
