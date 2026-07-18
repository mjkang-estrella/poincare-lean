import Poincare.Global.HeatSemigroupBUCGeneratorEvolution
import Poincare.Global.HeatCauchyFinal
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Positive-time smoothing into the strong `BUC` heat-generator domain

For arbitrary bounded uniformly continuous finite-dimensional vector data,
positive-time heat convolution belongs to the strong generator domain.  The
generator value is the `BUC`-valued convolution with the time derivative of
the Gaussian kernel.

The proof is in the uniform norm.  Spatial translates of a `BUC` datum vary
continuously as `BUC` elements, so the translated-data formula can be read as
a Bochner integral with values in `BUC`.  The time-window Gaussian envelope
from `HeatCauchyFinal` then permits differentiation of this Banach-valued
integral.  This is stronger than pointwise differentiation and supplies the
actual strong-generator graph witness.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction BigOperators

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

section SpatialTranslation

/-- Translation of a `BUC` coefficient in its spatial input. -/
def bucSpatialTranslate (f : BUC) (y : E) : BUC :=
  ⟨(f : E →ᵇ F).compContinuous
      ⟨fun x : E ↦ x - y, continuous_id.sub continuous_const⟩,
    f.property.comp (uniformContinuous_id.sub uniformContinuous_const)⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
@[simp]
theorem bucSpatialTranslate_apply (f : BUC) (y x : E) :
    (bucSpatialTranslate f y : E →ᵇ F) x = (f : E →ᵇ F) (x - y) :=
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Spatial translation does not increase the uniform norm. -/
theorem norm_bucSpatialTranslate_le (f : BUC) (y : E) :
    ‖bucSpatialTranslate f y‖ ≤ ‖f‖ := by
  change ‖(f : E →ᵇ F).compContinuous
      ⟨fun x : E ↦ x - y, continuous_id.sub continuous_const⟩‖ ≤
    ‖(f : E →ᵇ F)‖
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Uniform continuity of the datum is exactly what makes its spatial
translates continuous in the uniform `BUC` norm. -/
theorem uniformContinuous_bucSpatialTranslate (f : BUC) :
    UniformContinuous (bucSpatialTranslate f) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  rcases Metric.uniformContinuous_iff.mp f.property (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro y z hyz
  rw [Subtype.dist_eq, dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [BoundedContinuousFunction.norm_le (half_pos hε).le]
  intro x
  change ‖(f : E →ᵇ F) (x - y) - (f : E →ᵇ F) (x - z)‖ ≤ ε / 2
  rw [← dist_eq_norm]
  exact (hmod (by simpa [sub_eq_add_neg] using hyz)).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Continuity form of `uniformContinuous_bucSpatialTranslate`. -/
theorem continuous_bucSpatialTranslate (f : BUC) :
    Continuous (bucSpatialTranslate f) :=
  (uniformContinuous_bucSpatialTranslate f).continuous

/-- Evaluation of a `BUC` coefficient at a spatial point as a continuous
linear map. -/
noncomputable def bucEvaluationCLM (x : E) : BUC →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (f : E →ᵇ F) x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun f ↦ by
      simpa using
        BoundedContinuousFunction.norm_coe_le_norm (f : E →ᵇ F) x)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
@[simp]
theorem bucEvaluationCLM_apply (x : E) (f : BUC) :
    bucEvaluationCLM (E := E) (F := F) x f = (f : E →ᵇ F) x :=
  rfl

end SpatialTranslation

section KernelDerivative

omit [MeasurableSpace E] [BorelSpace E] in
/-- The time derivative of the Gaussian is even in its spatial variable. -/
theorem deriv_heatKernel_time_neg {t : ℝ} (ht : 0 < t) (y : E) :
    deriv (fun τ : ℝ ↦ heatKernel (E := E) τ (-y)) t =
      deriv (fun τ : ℝ ↦ heatKernel (E := E) τ y) t := by
  rw [deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht (-y),
    deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht y]
  simp [heatKernel]

omit [MeasurableSpace E] [BorelSpace E] in
/-- For fixed positive time, the time derivative of the Gaussian is a
continuous function of the spatial variable. -/
theorem continuous_deriv_heatKernel_time_spatial {t : ℝ} (ht : 0 < t) :
    Continuous (fun y : E ↦
      deriv (fun τ : ℝ ↦ heatKernel (E := E) τ y) t) := by
  have heq : (fun y : E ↦
      deriv (fun τ : ℝ ↦ heatKernel (E := E) τ y) t) =
      fun y : E ↦ heatKernel (E := E) t y *
        (‖y‖ ^ 2 / (4 * t ^ 2) -
          (Module.finrank ℝ E : ℝ) / (2 * t)) := by
    funext y
    exact deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht y
  rw [heq]
  exact (contDiff_heatKernel_spatial (E := E) t).continuous.mul (by fun_prop)

omit [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Uniform time-window domination of the `BUC`-valued differentiated
translated-data integrand.  Crucially, the bound is independent of the
evaluation point of the resulting `BUC` coefficient. -/
theorem norm_deriv_heatKernel_time_smul_bucSpatialTranslate_le_timeWindowEnvelope
    {t τ : ℝ} (ht : 0 < t) (hτ : τ ∈ Set.Icc (t / 2) (2 * t))
    (f : BUC) (y : E) :
    ‖deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) τ •
        bucSpatialTranslate f y‖ ≤
      heatKernelTimeWindowEnvelope (E := E) t
        (heatKernelTimeWindowDominationConstant (E := E) t ‖f‖ 0) 0 y := by
  have hτpos : 0 < τ := (half_pos ht).trans_le hτ.1
  have hscalar :=
    heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope
      (E := E) ht hτ (C := ‖f‖) (f := fun _ : E ↦ ‖f‖)
        (fun _ ↦ by simp) (0 : E) y
  have hscalar' :
      |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) τ| * ‖f‖ ≤
        heatKernelTimeWindowEnvelope (E := E) t
          (heatKernelTimeWindowDominationConstant (E := E) t ‖f‖ 0) 0 y := by
    simpa [zero_sub, deriv_heatKernel_time_neg (E := E) hτpos,
      Real.norm_eq_abs] using hscalar
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (norm_bucSpatialTranslate_le (E := E) (F := F) f y)
      (abs_nonneg _)).trans hscalar'

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- The translated-data heat integrand is Bochner integrable as a
`BUC`-valued function. -/
theorem integrable_heatKernel_smul_bucSpatialTranslate
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    Integrable (fun y : E ↦
      heatKernel (E := E) t y • bucSpatialTranslate f y) volume := by
  have hmeas : AEStronglyMeasurable (fun y : E ↦
      heatKernel (E := E) t y • bucSpatialTranslate f y) volume :=
    ((contDiff_heatKernel_spatial (E := E) t).continuous.smul
      (continuous_bucSpatialTranslate (E := E) (F := F) f)).aestronglyMeasurable
  have hbound : Integrable
      (fun y : E ↦ ‖f‖ * heatKernel (E := E) t y) volume :=
    (heatKernel_integrable (E := E) ht).const_mul ‖f‖
  refine hbound.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hk : 0 ≤ heatKernel (E := E) t y :=
    heatKernel_nonneg (E := E) ht y
  rw [norm_smul, Real.norm_of_nonneg hk]
  calc
    heatKernel (E := E) t y * ‖bucSpatialTranslate f y‖ ≤
        heatKernel (E := E) t y * ‖f‖ :=
      mul_le_mul_of_nonneg_left
        (norm_bucSpatialTranslate_le (E := E) (F := F) f y) hk
    _ = ‖f‖ * heatKernel (E := E) t y := by ring

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- The differentiated translated-data integrand is Bochner integrable in
`BUC` at every positive time. -/
theorem integrable_deriv_heatKernel_time_smul_bucSpatialTranslate
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    Integrable (fun y : E ↦
      deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t •
        bucSpatialTranslate f y) volume := by
  let bound : E → ℝ := fun y ↦
    heatKernelTimeWindowEnvelope (E := E) t
      (heatKernelTimeWindowDominationConstant (E := E) t ‖f‖ 0) 0 y
  have hmeas : AEStronglyMeasurable (fun y : E ↦
      deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t •
        bucSpatialTranslate f y) volume :=
    ((continuous_deriv_heatKernel_time_spatial (E := E) ht).smul
      (continuous_bucSpatialTranslate (E := E) (F := F) f)).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    exact integrable_heatKernelTimeWindowEnvelope (E := E) ht _ 0
  refine hbound.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact
    norm_deriv_heatKernel_time_smul_bucSpatialTranslate_le_timeWindowEnvelope
      (E := E) (F := F) (t := t) (τ := t) ht
        ⟨by linarith, by linarith⟩ f y

/-- The `L¹` norm of the time-differentiated scalar Gaussian kernel. -/
def heatKernelTimeDerivativeL1Norm (t : ℝ) : ℝ :=
  ∫ y : E, |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t|

/-- The absolute value of the time-differentiated Gaussian is integrable at
every positive time. -/
theorem integrable_abs_deriv_heatKernel_time {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : E ↦
      |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t|) volume := by
  let bound : E → ℝ := fun y ↦
    heatKernelTimeWindowEnvelope (E := E) t
      (heatKernelTimeWindowDominationConstant (E := E) t 1 0) 0 y
  have hmeas : AEStronglyMeasurable (fun y : E ↦
      |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t|) volume :=
    (continuous_deriv_heatKernel_time_spatial (E := E) ht).abs.aestronglyMeasurable
  have hbound : Integrable bound volume := by
    exact integrable_heatKernelTimeWindowEnvelope (E := E) ht _ 0
  refine hbound.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hscalar :=
    heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope
      (E := E) (t := t) (τ := t) ht ⟨by linarith, by linarith⟩
        (C := (1 : ℝ)) (f := fun _ : E ↦ (1 : ℝ))
        (fun _ ↦ by simp) (0 : E) y
  simpa [bound, zero_sub, deriv_heatKernel_time_neg (E := E) ht,
    Real.norm_eq_abs] using hscalar

/-- The explicit positive-time strong-generator candidate: convolution with
the time derivative of the heat kernel, formed as a `BUC`-valued integral. -/
def vectorHeatTimeDerivativeBUC (t : ℝ) (f : BUC) : BUC :=
  ∫ y : E, deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t •
    bucSpatialTranslate f y

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Explicit uniform-norm domination of the positive-time generator value by
the `L¹` norm of the differentiated Gaussian. -/
theorem norm_vectorHeatTimeDerivativeBUC_le
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    ‖vectorHeatTimeDerivativeBUC (E := E) (F := F) t f‖ ≤
      heatKernelTimeDerivativeL1Norm (E := E) t * ‖f‖ := by
  have hscalar := integrable_abs_deriv_heatKernel_time (E := E) ht
  have hbound : Integrable (fun y : E ↦
      |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t| * ‖f‖) volume :=
    hscalar.mul_const ‖f‖
  have hnorm :
      ‖∫ y : E,
          deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t •
            bucSpatialTranslate f y‖ ≤
        ∫ y : E,
          |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t| * ‖f‖ :=
    MeasureTheory.norm_integral_le_of_norm_le hbound
      (Filter.Eventually.of_forall fun y ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_bucSpatialTranslate_le (E := E) (F := F) f y) (abs_nonneg _))
  calc
    ‖vectorHeatTimeDerivativeBUC (E := E) (F := F) t f‖ ≤
        ∫ y : E,
          |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) t| * ‖f‖ := by
      simpa [vectorHeatTimeDerivativeBUC] using hnorm
    _ = heatKernelTimeDerivativeL1Norm (E := E) t * ‖f‖ := by
      rw [integral_mul_const]
      rfl

/-- Parabolic scaling of the absolute time derivative of the heat kernel.
The spatial Jacobian contributes `a⁻ⁿ` and the time derivative contributes
the additional factor `(a²)⁻¹`. -/
theorem abs_deriv_heatKernel_time_sq_smul
    (a : ℝ) (ha : 0 < a) (x : E) :
    |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ (a • x)) (a ^ 2)| =
      (a ^ Module.finrank ℝ E)⁻¹ * (a ^ 2)⁻¹ *
        |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ x) 1| := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [deriv_heatKernel_time_eq_heatKernel_mul (E := E) ha2 (a • x),
    deriv_heatKernel_time_eq_heatKernel_mul (E := E) zero_lt_one x,
    heatKernel_sq_smul (E := E) a ha x, norm_smul,
    Real.norm_of_nonneg ha.le]
  have hfactor :
      (a * ‖x‖) ^ 2 / (4 * (a ^ 2) ^ 2) -
          (Module.finrank ℝ E : ℝ) / (2 * a ^ 2) =
        (a ^ 2)⁻¹ *
          (‖x‖ ^ 2 / (4 * (1 : ℝ) ^ 2) -
            (Module.finrank ℝ E : ℝ) / (2 * 1)) := by
    field_simp [ha.ne']
  rw [hfactor]
  simp only [one_pow, mul_one, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos ha _))]
  ring

/-- Exact parabolic scaling of the `L¹` norm of the differentiated Gaussian. -/
theorem heatKernelTimeDerivativeL1Norm_sq
    (a : ℝ) (ha : 0 < a) :
    heatKernelTimeDerivativeL1Norm (E := E) (a ^ 2) =
      (a ^ 2)⁻¹ * heatKernelTimeDerivativeL1Norm (E := E) 1 := by
  let p : ℝ := a ^ Module.finrank ℝ E
  have hp : 0 < p := pow_pos ha _
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E ↦
      |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) (a ^ 2)|)
    a (hR := ha.le)
  have hscaled :
      (∫ x : E,
          |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ (a • x)) (a ^ 2)|) =
        (p⁻¹ * (a ^ 2)⁻¹) *
          heatKernelTimeDerivativeL1Norm (E := E) 1 := by
    rw [show (fun x : E ↦
        |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ (a • x)) (a ^ 2)|) =
      fun x : E ↦ (p⁻¹ * (a ^ 2)⁻¹) *
        |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ x) 1| by
          funext x
          simpa only [p, mul_assoc] using
            abs_deriv_heatKernel_time_sq_smul (E := E) a ha x]
    rw [integral_const_mul]
    rfl
  apply mul_left_cancel₀ (inv_ne_zero hp.ne')
  calc
    p⁻¹ * heatKernelTimeDerivativeL1Norm (E := E) (a ^ 2) =
        ∫ x : E,
          |deriv (fun σ : ℝ ↦ heatKernel (E := E) σ (a • x)) (a ^ 2)| := by
      simpa [heatKernelTimeDerivativeL1Norm, p, smul_eq_mul] using hchange.symm
    _ = (p⁻¹ * (a ^ 2)⁻¹) *
        heatKernelTimeDerivativeL1Norm (E := E) 1 := hscaled
    _ = p⁻¹ * ((a ^ 2)⁻¹ *
        heatKernelTimeDerivativeL1Norm (E := E) 1) := by ring

/-- Positive-time inverse-time scaling of the differentiated Gaussian norm. -/
theorem heatKernelTimeDerivativeL1Norm_eq_inv_mul
    {t : ℝ} (ht : 0 < t) :
    heatKernelTimeDerivativeL1Norm (E := E) t =
      t⁻¹ * heatKernelTimeDerivativeL1Norm (E := E) 1 := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := heatKernelTimeDerivativeL1Norm_sq
    (E := E) (Real.sqrt t) hsqrt
  simpa [Real.sq_sqrt ht.le] using h

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- Honest inverse-time generator smoothing bound, with constant exactly the
`L¹` norm of the time-one differentiated Gaussian. -/
theorem norm_vectorHeatTimeDerivativeBUC_le_inv
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    ‖vectorHeatTimeDerivativeBUC (E := E) (F := F) t f‖ ≤
      (heatKernelTimeDerivativeL1Norm (E := E) 1 / t) * ‖f‖ := by
  rw [div_eq_mul_inv, mul_comm
    (heatKernelTimeDerivativeL1Norm (E := E) 1) t⁻¹]
  rw [← heatKernelTimeDerivativeL1Norm_eq_inv_mul (E := E) ht]
  exact norm_vectorHeatTimeDerivativeBUC_le (E := E) (F := F) ht f

end KernelDerivative

section StrongGeneratorSmoothing

/-- The `BUC`-valued translated-data integral is exactly the positive-time
heat semigroup. -/
theorem integral_heatKernel_smul_bucSpatialTranslate_eq_heatSemigroup
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    (∫ y : E, heatKernel (E := E) t y • bucSpatialTranslate f y) =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) t f := by
  apply Subtype.ext
  ext x
  let L : BUC →L[ℝ] F := bucEvaluationCLM (E := E) (F := F) x
  have hint := integrable_heatKernel_smul_bucSpatialTranslate
    (E := E) (F := F) ht f
  change L (∫ y : E,
      heatKernel (E := E) t y • bucSpatialTranslate f y) =
    (vectorHeatSemigroupBUCExtended (E := E) (F := F) t f :
      E →ᵇ F) x
  calc
    L (∫ y : E,
          heatKernel (E := E) t y • bucSpatialTranslate f y) = ∫ y : E,
          L (heatKernel (E := E) t y • bucSpatialTranslate f y) :=
      (L.integral_comp_comm hint).symm
    _ = ∫ y : E, heatKernel (E := E) t y • (f : E →ᵇ F) (x - y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro y
      rfl
    _ = vectorHeatSolution (E := E) t f x :=
      (vectorHeatSolution_apply_data_translate
        (E := E) (t := t) (fun z : E ↦ (f : E →ᵇ F) z) x).symm
    _ = (vectorHeatSemigroupBUCExtended (E := E) (F := F) t f :
        E →ᵇ F) x := by
      simp [vectorHeatSemigroupBUCExtended, ht, vectorHeatSemigroupBUC]

/-- At every positive time, the heat orbit of arbitrary `BUC` data is
differentiable in the `BUC` norm, with derivative given by the differentiated
Gaussian convolution. -/
theorem vectorHeatSemigroupBUCExtended_hasDerivAt_of_pos
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    HasDerivAt
      (fun τ : ℝ ↦ vectorHeatSemigroupBUCExtended
        (E := E) (F := F) τ f)
      (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) t := by
  let bound : E → ℝ := fun y ↦
    heatKernelTimeWindowEnvelope (E := E) t
      (heatKernelTimeWindowDominationConstant (E := E) t ‖f‖ 0) 0 y
  let s : Set ℝ := Set.Ioo (t / 2) (2 * t)
  have hs : s ∈ 𝓝 t := by
    refine Ioo_mem_nhds ?_ ?_ <;> linarith
  have hF_meas : ∀ᶠ τ in 𝓝 t,
      AEStronglyMeasurable (fun y : E ↦
        heatKernel (E := E) τ y • bucSpatialTranslate f y) volume := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    exact ((contDiff_heatKernel_spatial (E := E) τ).continuous.smul
      (continuous_bucSpatialTranslate (E := E) (F := F) f)).aestronglyMeasurable
  have hF_int : Integrable (fun y : E ↦
      heatKernel (E := E) t y • bucSpatialTranslate f y) volume :=
    integrable_heatKernel_smul_bucSpatialTranslate (E := E) (F := F) ht f
  have hF'_meas : AEStronglyMeasurable (fun y : E ↦
      deriv (fun τ : ℝ ↦ heatKernel (E := E) τ y) t •
        bucSpatialTranslate f y) volume :=
    ((continuous_deriv_heatKernel_time_spatial (E := E) ht).smul
      (continuous_bucSpatialTranslate (E := E) (F := F) f)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ τ ∈ s,
      ‖deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) τ •
        bucSpatialTranslate f y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall ?_
    intro y τ hτ
    exact
      norm_deriv_heatKernel_time_smul_bucSpatialTranslate_le_timeWindowEnvelope
        (E := E) (F := F) ht ⟨hτ.1.le, hτ.2.le⟩ f y
  have hbound_int : Integrable bound volume := by
    exact integrable_heatKernelTimeWindowEnvelope (E := E) ht _ 0
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ τ ∈ s,
      HasDerivAt
        (fun τ : ℝ ↦ heatKernel (E := E) τ y • bucSpatialTranslate f y)
        (deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) τ •
          bucSpatialTranslate f y) τ := by
    refine Filter.Eventually.of_forall ?_
    intro y τ hτ
    have hτpos : 0 < τ := (half_pos ht).trans hτ.1
    have hbase := hasDerivAt_heatKernel_time (E := E) hτpos y
    simpa [deriv_heatKernel_time (E := E) hτpos y] using
      hbase.smul_const (bucSpatialTranslate f y)
  have hraw : HasDerivAt
      (fun τ : ℝ ↦ ∫ y : E,
        heatKernel (E := E) τ y • bucSpatialTranslate f y)
      (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) t := by
    simpa only [vectorHeatTimeDerivativeBUC] using
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun τ y ↦
          heatKernel (E := E) τ y • bucSpatialTranslate f y)
        (F' := fun τ y ↦
          deriv (fun σ : ℝ ↦ heatKernel (E := E) σ y) τ •
            bucSpatialTranslate f y)
        (x₀ := t) (s := s) (bound := bound)
        hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with τ hτ
  exact
    (integral_heatKernel_smul_bucSpatialTranslate_eq_heatSemigroup
      (E := E) (F := F) hτ f).symm

/-- Positive-time heat smoothing constructs the desired strong-generator
graph witness for every `BUC` datum; it is not assumed. -/
theorem vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
    {t : ℝ} (ht : 0 < t) (f : BUC) :
    IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t f)
      (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) := by
  have horbit := vectorHeatSemigroupBUCExtended_hasDerivAt_of_pos
    (E := E) (F := F) ht f
  have hshift : HasDerivAt
      (fun h : ℝ ↦ vectorHeatSemigroupBUCExtended
        (E := E) (F := F) (t + h) f)
      (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) 0 := by
    have hinner : HasDerivAt (fun h : ℝ ↦ t + h) 1 0 := by
      simpa using
        (hasDerivAt_const (0 : ℝ) t).add (hasDerivAt_id (0 : ℝ))
    have horbit' : HasDerivAt
        (fun τ : ℝ ↦ vectorHeatSemigroupBUCExtended
          (E := E) (F := F) τ f)
        (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) (t + 0) := by
      simpa using horbit
    simpa only [Function.comp_def, one_smul] using horbit'.scomp 0 hinner
  have hwithin := hshift.hasDerivWithinAt (s := Set.Ici (0 : ℝ))
  apply hwithin.congr
  · intro h hh
    rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) hh ht.le f]
    rw [add_comm]
  · simp

/-- Linearity of the explicit positive-time generator value in the datum. -/
theorem vectorHeatTimeDerivativeBUC_add
    {t : ℝ} (ht : 0 < t) (f g : BUC) :
    vectorHeatTimeDerivativeBUC (E := E) (F := F) t (f + g) =
      vectorHeatTimeDerivativeBUC (E := E) (F := F) t f +
        vectorHeatTimeDerivativeBUC (E := E) (F := F) t g := by
  have hdirect :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) ht (f + g)
  have hf := vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
    (E := E) (F := F) ht f
  have hg := vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
    (E := E) (F := F) ht g
  have hsum : IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t (f + g))
      (vectorHeatTimeDerivativeBUC (E := E) (F := F) t f +
        vectorHeatTimeDerivativeBUC (E := E) (F := F) t g) := by
    simpa only [IsInBUCHeatGeneratorDomain, map_add] using hf.add hg
  exact hdirect.unique hsum

/-- Scalar linearity of the explicit positive-time generator value. -/
theorem vectorHeatTimeDerivativeBUC_smul
    {t : ℝ} (ht : 0 < t) (c : ℝ) (f : BUC) :
    vectorHeatTimeDerivativeBUC (E := E) (F := F) t (c • f) =
      c • vectorHeatTimeDerivativeBUC (E := E) (F := F) t f := by
  have hdirect :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) ht (c • f)
  have hf := vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
    (E := E) (F := F) ht f
  have hscaled : IsInBUCHeatGeneratorDomain (E := E) (F := F)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F) t (c • f))
      (c • vectorHeatTimeDerivativeBUC (E := E) (F := F) t f) := by
    simpa only [IsInBUCHeatGeneratorDomain, map_smul] using hf.const_smul c
  exact hdirect.unique hscaled

/-- At a fixed positive time, the explicit generator value is a bounded
linear operator on `BUC`. -/
noncomputable def vectorHeatTimeDerivativeBUCCLM
    (t : ℝ) (ht : 0 < t) : BUC →L[ℝ] BUC := by
  let L : BUC →ₗ[ℝ] BUC :=
    { toFun := vectorHeatTimeDerivativeBUC (E := E) (F := F) t
      map_add' := vectorHeatTimeDerivativeBUC_add (E := E) (F := F) ht
      map_smul' := vectorHeatTimeDerivativeBUC_smul (E := E) (F := F) ht }
  exact L.mkContinuous
    (heatKernelTimeDerivativeL1Norm (E := E) t)
    (norm_vectorHeatTimeDerivativeBUC_le (E := E) (F := F) ht)

@[simp]
theorem vectorHeatTimeDerivativeBUCCLM_apply
    (t : ℝ) (ht : 0 < t) (f : BUC) :
    vectorHeatTimeDerivativeBUCCLM (E := E) (F := F) t ht f =
      vectorHeatTimeDerivativeBUC (E := E) (F := F) t f := by
  simp [vectorHeatTimeDerivativeBUCCLM, LinearMap.mkContinuous_apply]

/-- Joint continuity of the positive-time generator family on a half-line
separated from zero, allowing both time and datum to vary. -/
theorem continuousOn_vectorHeatTimeDerivativeBUC_prod_Ici
    {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun p : ℝ × BUC ↦
        vectorHeatTimeDerivativeBUC (E := E) (F := F) p.1 p.2)
      (Set.Ici a ×ˢ Set.univ) := by
  let b : ℝ := a / 2
  have hb : 0 < b := half_pos ha
  let Ab : BUC →L[ℝ] BUC :=
    vectorHeatTimeDerivativeBUCCLM (E := E) (F := F) b hb
  let model : ℝ × BUC → BUC := fun p ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (p.1 - b) (Ab p.2)
  have hmodel : Continuous model := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_fst.sub continuous_const
    · exact Ab.continuous.comp continuous_snd
  apply hmodel.continuousOn.congr
  rintro ⟨t, f⟩ ⟨ht, _hf⟩
  change a ≤ t at ht
  have htpos : 0 < t := ha.trans_le ht
  have htb : 0 ≤ t - b := by
    dsimp [b]
    linarith
  have hbase :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) hb f
  have hprop := hbase.semigroup htb
  have horbit_eq :
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - b)
          (vectorHeatSemigroupBUCExtended (E := E) (F := F) b f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t f := by
    rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) htb hb.le f]
    congr 2
    ring
  rw [horbit_eq] at hprop
  have hdirect :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) htpos f
  simpa only [model, Ab, vectorHeatTimeDerivativeBUCCLM_apply] using
    hdirect.unique hprop

/-- Joint continuity of `(t,f) ↦ A H_t f` on all positive times. -/
theorem continuousOn_vectorHeatTimeDerivativeBUC_prod_Ioi :
    ContinuousOn
      (fun p : ℝ × BUC ↦
        vectorHeatTimeDerivativeBUC (E := E) (F := F) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  intro p hp
  let a : ℝ := p.1 / 2
  have ha : 0 < a := half_pos hp.1
  have hap : a < p.1 := half_lt_self hp.1
  have hlocal := continuousOn_vectorHeatTimeDerivativeBUC_prod_Ici
    (E := E) (F := F) ha
  have hwithin := hlocal p ⟨hap.le, Set.mem_univ p.2⟩
  have hnhds : Set.Ici a ×ˢ Set.univ ∈ 𝓝 p :=
    prod_mem_nhds (Ici_mem_nhds hap) univ_mem
  exact (hwithin.continuousAt hnhds).continuousWithinAt

/-- On every time half-line separated from zero, the explicitly constructed
generator values form a continuous `BUC` path. -/
theorem continuousOn_vectorHeatTimeDerivativeBUC_Ici
    (f : BUC) {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun t : ℝ ↦ vectorHeatTimeDerivativeBUC (E := E) (F := F) t f)
      (Set.Ici a) := by
  let b : ℝ := a / 2
  let Ab : BUC := vectorHeatTimeDerivativeBUC (E := E) (F := F) b f
  let model : ℝ → BUC := fun t ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - b) Ab
  have hb : 0 < b := half_pos ha
  have hmodel : Continuous model := by
    exact (continuous_vectorHeatSemigroupBUCExtended_apply
      (E := E) (F := F) Ab).comp (continuous_id.sub continuous_const)
  apply hmodel.continuousOn.congr
  intro t ht
  have htpos : 0 < t := ha.trans_le ht
  have htb : 0 ≤ t - b := by
    change a ≤ t at ht
    dsimp [b]
    linarith
  have hbase :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) hb f
  have hprop := hbase.semigroup htb
  have horbit_eq :
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - b)
          (vectorHeatSemigroupBUCExtended (E := E) (F := F) b f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t f := by
    rw [vectorHeatSemigroupBUCExtended_add_apply
      (E := E) (F := F) htb hb.le f]
    congr 2
    ring
  rw [horbit_eq] at hprop
  have hdirect :=
    vectorHeatSemigroupBUCExtended_mem_heatGeneratorDomain_of_pos
      (E := E) (F := F) htpos f
  exact hdirect.unique hprop

/-- Compact-positive-interval form of continuity of the constructed
generator-value family. -/
theorem continuousOn_vectorHeatTimeDerivativeBUC_Icc
    (f : BUC) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun t : ℝ ↦ vectorHeatTimeDerivativeBUC (E := E) (F := F) t f)
      (Set.Icc a b) :=
  (continuousOn_vectorHeatTimeDerivativeBUC_Ici
    (E := E) (F := F) f ha).mono fun _ ht ↦ ht.1

end StrongGeneratorSmoothing

end Poincare
