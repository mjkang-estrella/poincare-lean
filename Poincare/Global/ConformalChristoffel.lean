import Poincare.Global.RoundSphereChart
import Poincare.ModelChristoffel

/-!
# Christoffel symbols for conformally flat chart metrics

The chart-side one-form in `CovariantDerivative.christoffelOneForm` uses the
section-value slot first and the direction slot second:

`christoffelOneForm G b hb z s v = christoffelAt G z (b z) (hb z) v s`.

Thus the classical symmetric Christoffel bilinear formula is proved below for
`christoffelAt`, and the one-form theorem restates it with this slot flip.
-/

noncomputable section

open CovariantDerivative
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Continuous-linear scaling of the Euclidean inner product bilinear form. -/
def conformalInnerScale :
    ℝ →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)

@[simp] theorem conformalInnerScale_apply (c : ℝ) (v w : E) :
    conformalInnerScale (E := E) c v w = c * inner ℝ v w := by
  rw [conformalInnerScale, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]
  change ((c • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) v) w =
    c * inner ℝ v w
  simp [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- The conformally flat metric coefficient family `G z = f z • innerSL ℝ`. -/
def conformalFlatMetric (f : E → ℝ) :
    E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun z => conformalInnerScale (E := E) (f z)

/-- The bilinear form associated to `conformalFlatMetric f z`. -/
def conformalFlatBilin (f : E → ℝ) (z : E) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w => f z * inner ℝ v w)
    (by
      intro v v' w
      simp [inner_add_left, mul_add])
    (by
      intro c v w
      change f z * inner ℝ (c • v) w = c * (f z * inner ℝ v w)
      rw [inner_smul_left]
      simp
      ring)
    (by
      intro v w w'
      simp [inner_add_right, mul_add])
    (by
      intro c v w
      change f z * inner ℝ v (c • w) = c * (f z * inner ℝ v w)
      rw [inner_smul_right]
      ring)

@[simp] theorem conformalFlatMetric_apply (f : E → ℝ) (z v w : E) :
    conformalFlatMetric f z v w = f z * inner ℝ v w := by
  simp [conformalFlatMetric]

@[simp] theorem conformalFlatBilin_apply (f : E → ℝ) (z v w : E) :
    conformalFlatBilin f z v w = f z * inner ℝ v w :=
  rfl

/-- `f z • inner` is nondegenerate whenever the conformal factor is nonzero. -/
theorem conformalFlatBilin_nondegenerate (f : E → ℝ) (z : E)
    (hf : f z ≠ 0) :
    (conformalFlatBilin f z).Nondegenerate := by
  constructor
  · intro v hv
    have hmul : f z * inner ℝ v v = 0 := hv v
    have hinner : inner ℝ v v = 0 := (mul_eq_zero.mp hmul).resolve_left hf
    exact inner_self_eq_zero.mp hinner
  · intro v hv
    have hmul : f z * inner ℝ v v = 0 := hv v
    have hinner : inner ℝ v v = 0 := (mul_eq_zero.mp hmul).resolve_left hf
    exact inner_self_eq_zero.mp hinner

/-- The vector appearing in the conformal Christoffel formula. -/
def conformalChristoffelFormula (f : E → ℝ) (z gradf u v : E) : E :=
  (fderiv ℝ f z u / (2 * f z)) • v
    + (fderiv ℝ f z v / (2 * f z)) • u
    - (inner ℝ u v / (2 * f z)) • gradf

theorem fderiv_conformalFlatMetric (f : E → ℝ) {z : E}
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (conformalFlatMetric f) z =
      (conformalInnerScale (E := E)).comp (fderiv ℝ f z) := by
  have hscale :
      HasFDerivAt (fun c : ℝ => conformalInnerScale (E := E) c)
        (conformalInnerScale (E := E)) (f z) :=
    (conformalInnerScale (E := E)).hasFDerivAt
  have hcomp :
      HasFDerivAt ((conformalInnerScale (E := E)) ∘ f)
        ((conformalInnerScale (E := E)).comp (fderiv ℝ f z)) z :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := ℝ)
      (G := E →L[ℝ] E →L[ℝ] ℝ) (f := f)
      (f' := fderiv ℝ f z)
      (g := fun c : ℝ => conformalInnerScale (E := E) c)
      (g' := conformalInnerScale (E := E)) z hscale hf.hasFDerivAt
  change fderiv ℝ ((conformalInnerScale (E := E)) ∘ f) z =
    (conformalInnerScale (E := E)).comp (fderiv ℝ f z)
  exact hcomp.fderiv

variable [FiniteDimensional ℝ E]

/--
Classical conformal Christoffel formula for `G z = f z • innerSL ℝ`.

If `gradf` is the Euclidean gradient representative of `Df z`, then
`christoffelAt` is
`Γ(u,v) = (Df u / 2f) v + (Df v / 2f) u - (⟪u,v⟫ / 2f) gradf`.
-/
theorem christoffelAt_conformalFlatMetric
    (f : E → ℝ) {z : E} (hfz : f z ≠ 0)
    (hfd : DifferentiableAt ℝ f z) {gradf : E}
    (hgrad : ∀ w : E, inner ℝ gradf w = fderiv ℝ f z w)
    (u v : E) :
    christoffelAt (conformalFlatMetric f) z (conformalFlatBilin f z)
        (conformalFlatBilin_nondegenerate f z hfz) u v =
      conformalChristoffelFormula f z gradf u v := by
  apply sub_eq_zero.mp
  apply (conformalFlatBilin_nondegenerate f z hfz).1
  intro w
  rw [map_sub]
  change (conformalFlatBilin f z)
        (christoffelAt (conformalFlatMetric f) z (conformalFlatBilin f z)
          (conformalFlatBilin_nondegenerate f z hfz) u v) w
      - (conformalFlatBilin f z) (conformalChristoffelFormula f z gradf u v) w = 0
  rw [b_christoffelAt]
  rw [fderiv_conformalFlatMetric f hfd]
  simp only [conformalFlatBilin_apply, ContinuousLinearMap.comp_apply,
    conformalInnerScale_apply, conformalChristoffelFormula]
  rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
    inner_smul_left, hgrad]
  simp only [RCLike.conj_to_real]
  field_simp [hfz]
  ring_nf

/--
One-form version of `christoffelAt_conformalFlatMetric`.

Convention note: `christoffelOneForm_apply` flips the two vector slots, so the
left-hand side `... s v` is the classical `Γ(v,s)`.
-/
theorem christoffelOneForm_conformalFlatMetric_apply
    (f : E → ℝ) (hfpos : ∀ z : E, 0 < f z) {z : E}
    (hfd : DifferentiableAt ℝ f z) {gradf : E}
    (hgrad : ∀ w : E, inner ℝ gradf w = fderiv ℝ f z w)
    (s v : TangentSpace 𝓘(ℝ, E) z) :
    (christoffelOneForm (conformalFlatMetric f) (conformalFlatBilin f)
        (fun y => conformalFlatBilin_nondegenerate f y
          (ne_of_gt (hfpos y))) z) s v =
      conformalChristoffelFormula f z gradf v s := by
  rw [christoffelOneForm_apply]
  exact christoffelAt_conformalFlatMetric f (ne_of_gt (hfpos z)) hfd hgrad v s

/--
The raw derivative operator for
`stereoInvFunAuxConformalFactor z = 16 / (‖z‖ ^ 2 + 4) ^ 2`.

Pointwise, this operator simplifies to
`u ↦ -64 * ((‖z‖ ^ 2 + 4)⁻¹) ^ 3 * inner ℝ z u`; the raw chain-rule form
is kept as the verified hook for downstream curvature work.
-/
def stereoInvFunAuxConformalFactorFDeriv (z : E) : E →L[ℝ] ℝ :=
  (16 : ℝ) •
    ((ContinuousLinearMap.toSpanSingleton ℝ
        (-(((‖z‖ ^ 2 + 4) ^ 2) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
      ((2 • (‖z‖ ^ 2 + 4) ^ (2 - 1)) • (2 • innerSL ℝ z)))

theorem hasFDerivAt_stereoInvFunAuxConformalFactor (z : E) :
    HasFDerivAt (stereoInvFunAuxConformalFactor : E → ℝ)
      (stereoInvFunAuxConformalFactorFDeriv z) z := by
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
  have hpow :
      HasFDerivAt (fun y : E => (‖y‖ ^ 2 + 4) ^ 2)
        ((2 • (‖z‖ ^ 2 + 4) ^ (2 - 1)) • (2 • innerSL ℝ z)) z :=
    hsum.pow 2
  have hinv :
      HasFDerivAt (fun y : E => ((‖y‖ ^ 2 + 4) ^ 2)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ
            (-(((‖z‖ ^ 2 + 4) ^ 2) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
          ((2 • (‖z‖ ^ 2 + 4) ^ (2 - 1)) • (2 • innerSL ℝ z))) z := by
    simpa using (hasFDerivAt_inv (pow_ne_zero 2 hr)).comp z hpow
  have hmul := hinv.const_mul (16 : ℝ)
  convert hmul using 1

/-- Computed derivative of the stereographic conformal factor. -/
theorem fderiv_stereoInvFunAuxConformalFactor (z : E) :
    fderiv ℝ (stereoInvFunAuxConformalFactor : E → ℝ) z =
      stereoInvFunAuxConformalFactorFDeriv z :=
  (hasFDerivAt_stereoInvFunAuxConformalFactor z).fderiv

end Poincare
