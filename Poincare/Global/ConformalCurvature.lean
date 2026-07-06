import Poincare.Global.ConformalChristoffel

/-!
# Chart curvature for conformal stereographic sphere coordinates

This module stays at the model-chart level.  The curvature operator below is
the Christoffel-field expansion of the repository convention
`R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y]Z` from
`CovariantDerivative.curvatureOp`.  On constant model vector fields the bracket
term vanishes, and `CovariantDerivative.curvatureOp_modelLeviCivita_extend`
has the same first-two-slot orientation as `chartCurvatureOf`.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Chart-level curvature operator of a Christoffel field.

The slots are `R(u,v)w`; this matches
`CovariantDerivative.curvatureOp cov X Y Z` with `X = u`, `Y = v`, `Z = w`.
-/
def chartCurvatureOf (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (z : E) (u v w : E) : E :=
  (fderiv ℝ Γ z u) v w - (fderiv ℝ Γ z v) u w
    + Γ z u (Γ z v w) - Γ z v (Γ z u w)

/-- Chart-side Kulkarni-Nomizu product with the same slot order as the global API. -/
def chartTensorKulkarniNomizu
    (h k : E → E → ℝ) (u v w a : E) : ℝ :=
  h u w * k v a + h v a * k u w - h u a * k v w - h v w * k u a

/-- The Euclidean four-linear form used by `chartTensorKulkarniNomizu`. -/
def euclideanMetricForm (u v : E) : ℝ :=
  inner ℝ u v

/-- The conformal chart metric as an ordinary bilinear form. -/
def conformalChartMetricForm (f : E → ℝ) (z : E) (u v : E) : ℝ :=
  f z * inner ℝ u v

section SphereChristoffel

variable [FiniteDimensional ℝ E]

/-- The scalar coefficient `2 / (‖z‖² + 4)` in the sphere Christoffel field. -/
def sphereChristoffelCoeff (z : E) : ℝ :=
  2 / (‖z‖ ^ 2 + 4)

/-- Derivative of `sphereChristoffelCoeff`. -/
def sphereChristoffelCoeffFDeriv (z : E) : E →L[ℝ] ℝ :=
  (-4 * ((‖z‖ ^ 2 + 4) ^ 2)⁻¹) • innerSL ℝ z

@[simp] theorem sphereChristoffelCoeffFDeriv_apply (z x : E) :
    sphereChristoffelCoeffFDeriv z x =
      (-4 * ((‖z‖ ^ 2 + 4) ^ 2)⁻¹) * inner ℝ z x := by
  simp [sphereChristoffelCoeffFDeriv, innerSL_apply_apply]

theorem hasFDerivAt_sphereChristoffelCoeff (z : E) :
    HasFDerivAt sphereChristoffelCoeff
      (sphereChristoffelCoeffFDeriv z) z := by
  let r : ℝ := ‖z‖ ^ 2 + 4
  have hr : r ≠ 0 := by
    dsimp [r]
    positivity
  have hnorm :
      HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hsum :
      HasFDerivAt (fun y : E => ‖y‖ ^ 2 + 4) (2 • innerSL ℝ z) z :=
    hnorm.add_const 4
  have hinv :
      HasFDerivAt (fun y : E => (‖y‖ ^ 2 + 4)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(r ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
          (2 • innerSL ℝ z)) z := by
    simpa [r] using (hasFDerivAt_inv hr).comp z hsum
  have hmul := hinv.const_mul (2 : ℝ)
  convert hmul using 1
  · ext x
    simp [sphereChristoffelCoeffFDeriv, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.toSpanSingleton_apply, Function.comp_def,
      innerSL_apply_apply, r]
    ring

theorem fderiv_sphereChristoffelCoeff (z : E) :
    fderiv ℝ sphereChristoffelCoeff z =
      sphereChristoffelCoeffFDeriv z :=
  (hasFDerivAt_sphereChristoffelCoeff z).fderiv

/-- The linear-in-`z` core of the stereographic sphere Christoffel field. -/
def sphereChristoffelCoreFormula (z u v : E) : E :=
  inner ℝ u v • z - inner ℝ z u • v - inner ℝ z v • u

/-- The core as a continuous bilinear map in the last two slots. -/
def sphereChristoffelCore (z : E) : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u v : E => sphereChristoffelCoreFormula z u v)
        (by
          intro u u' v
          simp [sphereChristoffelCoreFormula, inner_add_left, inner_add_right,
            add_smul, sub_eq_add_neg]
          module)
        (by
          intro c u v
          simp [sphereChristoffelCoreFormula, smul_sub, smul_smul,
            inner_smul_left, inner_smul_right, sub_eq_add_neg]
          module)
        (by
          intro u v v'
          simp [sphereChristoffelCoreFormula, inner_add_left, inner_add_right,
            add_smul, sub_eq_add_neg]
          module)
        (by
          intro c u v
          simp [sphereChristoffelCoreFormula, smul_sub, smul_smul,
            inner_smul_left, inner_smul_right, sub_eq_add_neg]
          module))

@[simp] theorem sphereChristoffelCore_apply (z u v : E) :
    sphereChristoffelCore z u v = sphereChristoffelCoreFormula z u v :=
  rfl

/-- `sphereChristoffelCore` is continuous-linear in the base point. -/
def sphereChristoffelCoreLinear :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := sphereChristoffelCore (E := E)
      map_add' := by
        intro z z'
        ext u v
        simp [sphereChristoffelCoreFormula, inner_add_left, add_smul,
          sub_eq_add_neg]
        module
      map_smul' := by
        intro c z
        ext u v
        simp [sphereChristoffelCoreFormula, inner_smul_left, smul_sub,
          smul_smul, sub_eq_add_neg]
        module }

@[simp] theorem sphereChristoffelCoreLinear_apply (z u v : E) :
    sphereChristoffelCoreLinear z u v = sphereChristoffelCoreFormula z u v :=
  rfl

/-- The stereographic sphere Christoffel field. -/
def sphereChristoffel : E → E →L[ℝ] E →L[ℝ] E :=
  (sphereChristoffelCoeff (E := E) : E → ℝ) •
    (sphereChristoffelCoreLinear (E := E) : E → E →L[ℝ] E →L[ℝ] E)

@[simp] theorem sphereChristoffel_apply (z u v : E) :
    sphereChristoffel z u v =
      sphereChristoffelCoeff z • sphereChristoffelCoreFormula z u v := by
  rw [sphereChristoffel]
  change ((sphereChristoffelCoeff z • sphereChristoffelCoreLinear z) u) v =
    sphereChristoffelCoeff z • sphereChristoffelCoreFormula z u v
  simp

/-- The derivative of the stereographic sphere Christoffel field. -/
def sphereChristoffelFDeriv (z : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  sphereChristoffelCoeff z • sphereChristoffelCoreLinear
    + (sphereChristoffelCoeffFDeriv z).smulRight (sphereChristoffelCoreLinear z)

@[simp] theorem sphereChristoffelFDeriv_apply (z x u v : E) :
    sphereChristoffelFDeriv z x u v =
      sphereChristoffelCoeff z • sphereChristoffelCoreFormula x u v
        + sphereChristoffelCoeffFDeriv z x • sphereChristoffelCoreFormula z u v := by
  simp [sphereChristoffelFDeriv]

private instance sphereChristoffelCLMIsBoundedSMul :
    IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] E) :=
  IsBoundedSMul.of_norm_smul_le fun c Γ =>
    ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ)
      (𝕜' := ℝ) c Γ

set_option synthInstance.maxHeartbeats 1000000 in
theorem hasFDerivAt_sphereChristoffel (z : E) :
    HasFDerivAt sphereChristoffel (sphereChristoffelFDeriv z) z := by
  have hcoeff : HasFDerivAt (sphereChristoffelCoeff (E := E) : E → ℝ)
      (sphereChristoffelCoeffFDeriv z) z :=
    hasFDerivAt_sphereChristoffelCoeff (E := E) z
  have hcore : HasFDerivAt
      (sphereChristoffelCoreLinear (E := E) : E → E →L[ℝ] E →L[ℝ] E)
      (sphereChristoffelCoreLinear (E := E)) z :=
    (sphereChristoffelCoreLinear (E := E)).hasFDerivAt
  simpa [sphereChristoffel, sphereChristoffelFDeriv] using
    (hcoeff.smul (F := E →L[ℝ] E →L[ℝ] E) (𝕜' := ℝ) hcore)

theorem fderiv_sphereChristoffel (z : E) :
    fderiv ℝ (sphereChristoffel (E := E)) z =
      sphereChristoffelFDeriv z :=
  (hasFDerivAt_sphereChristoffel (E := E) z).fderiv

/-- Raw vector-valued constant-curvature identity for the stereographic factor. -/
theorem chartCurvatureOf_sphereChristoffel_eq
    (z u v w : E) :
    chartCurvatureOf (sphereChristoffel (E := E)) z u v w =
      stereoInvFunAuxConformalFactor z •
        (inner ℝ v w • u - inner ℝ u w • v) := by
  apply ext_inner_right ℝ
  intro a
  rw [chartCurvatureOf, fderiv_sphereChristoffel]
  simp only [sphereChristoffelFDeriv_apply, sphereChristoffel_apply]
  unfold sphereChristoffelCoeff sphereChristoffelCoeffFDeriv
    sphereChristoffelCoreFormula stereoInvFunAuxConformalFactor
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  have hden4 : 4 + ‖z‖ ^ 2 ≠ 0 := by positivity
  have hsq :
      (16 + ‖z‖ ^ 2 * 8 + ‖z‖ ^ 4)⁻¹ =
        (4 + ‖z‖ ^ 2)⁻¹ ^ 2 := by
    rw [show 16 + ‖z‖ ^ 2 * 8 + ‖z‖ ^ 4 =
        (4 + ‖z‖ ^ 2) ^ 2 by ring]
    rw [← inv_pow]
  field_simp [hden]
  simp [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, smul_add, add_smul, smul_sub,
    sub_smul, smul_smul, sub_eq_add_neg, real_inner_comm]
  ring_nf
  rw [hsq]
  field_simp [hden4, pow_ne_zero 2 hden4]
  ring

/-- Euclidean-lowered form of the chart sphere curvature identity. -/
theorem inner_chartCurvatureOf_sphereChristoffel
    (z u v w a : E) :
    inner ℝ (chartCurvatureOf (sphereChristoffel (E := E)) z u v w) a =
      stereoInvFunAuxConformalFactor z *
        (inner ℝ v w * inner ℝ u a - inner ℝ u w * inner ℝ v a) := by
  rw [chartCurvatureOf_sphereChristoffel_eq]
  simp [inner_sub_left, inner_smul_left, mul_sub, mul_assoc]

/--
Metric-lowered chart analogue of `HasConstantSectionalCurvature3` for the
stereographic conformal factor.  The left side lowers the curvature vector
with `G z = f z • ⟪·,·⟫`, and the right side is `-(1/2)` times the
Kulkarni-Nomizu square of the same chart metric.
-/
theorem conformalChartMetric_chartCurvatureOf_sphereChristoffel
    (z u v w a : E) :
    conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z
        (chartCurvatureOf (sphereChristoffel (E := E)) z u v w) a =
      -(1 / 2 : ℝ) *
        chartTensorKulkarniNomizu
          (conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z)
          (conformalChartMetricForm (stereoInvFunAuxConformalFactor : E → ℝ) z)
          u v w a := by
  rw [conformalChartMetricForm, inner_chartCurvatureOf_sphereChristoffel]
  unfold chartTensorKulkarniNomizu conformalChartMetricForm
  ring

end SphereChristoffel

end Poincare
