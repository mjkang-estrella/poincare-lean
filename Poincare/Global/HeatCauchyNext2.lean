import Poincare.Global.HeatCauchyUniform
import Poincare.Global.HeatCauchyDirectional
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Uniform second Frechet estimates for the heat Cauchy problem

The first spatial Frechet integral can be differentiated once more only after
its operator-valued derivative has a locally uniform integrable majorant.  This
module supplies that missing estimate.  It first bounds the Hessian operator
norm by the zeroth- and second-order Gaussian factors, and then absorbs both
factors into the closed-ball envelope from `HeatCauchyUniform`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian ContDiff

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Real scalar multiplication is bounded on a bilinear continuous map. -/
theorem norm_real_smul_continuousLinearMap_two_le
    (c : ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖c • H‖ ≤ ‖c‖ * ‖H‖ := by
  have hbound_nonneg : 0 ≤ ‖c‖ * ‖H‖ := mul_nonneg (norm_nonneg c) (norm_nonneg H)
  refine ContinuousLinearMap.opNorm_le_bound _ hbound_nonneg ?_
  intro v
  have hv_nonneg : 0 ≤ (‖c‖ * ‖H‖) * ‖v‖ :=
    mul_nonneg hbound_nonneg (norm_nonneg v)
  refine ContinuousLinearMap.opNorm_le_bound _ hv_nonneg ?_
  intro w
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul]
  calc
    ‖c‖ * ‖H v w‖ ≤ ‖c‖ * (‖H v‖ * ‖w‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm (H v) w) (norm_nonneg c)
    _ ≤ ‖c‖ * ((‖H‖ * ‖v‖) * ‖w‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm H v) (norm_nonneg w))
        (norm_nonneg c)
    _ = ((‖c‖ * ‖H‖) * ‖v‖) * ‖w‖ := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Real scalar multiplication is bounded on a scalar-valued continuous linear map. -/
theorem norm_real_smul_continuousLinearMap_one_le
    (c : ℝ) (L : E →L[ℝ] ℝ) :
    ‖c • L‖ ≤ ‖c‖ * ‖L‖ := by
  have hbound_nonneg : 0 ≤ ‖c‖ * ‖L‖ := mul_nonneg (norm_nonneg c) (norm_nonneg L)
  refine ContinuousLinearMap.opNorm_le_bound _ hbound_nonneg ?_
  intro v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul]
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm L v) (norm_nonneg c))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Full bilinear Hessian formula, obtained from the diagonal formula by polarization. -/
theorem iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination
    {t : ℝ} (ht : t ≠ 0) (u v w : E) :
    iteratedFDeriv ℝ 2 (fun z : E => heatKernel (E := E) t z) u ![v, w] =
      heatKernel (E := E) t u *
        (⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
  let H : E →L[ℝ] E →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) u
  have hdiag (q : E) :
      H q q = heatKernel (E := E) t u *
        (⟪u, q⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖q‖ ^ 2 / (2 * t)) := by
    simpa [H, iteratedFDeriv_two_apply] using
      (iteratedFDeriv_two_heatKernel_apply (E := E) ht u q)
  have hcont : ContDiffAt ℝ ω (fun z : E => heatKernel (E := E) t z) u :=
    (contDiffAt_heatKernel_spatial (E := E) t u).of_le le_top
  have hsymm : H v w = H w v := by
    simpa [H, iteratedFDeriv_two_apply] using
      hcont.isSymmSndFDerivAt_of_omega.iteratedFDeriv_cons (v := v) (w := w)
  have hpolar : 2 * H v w = H (v + w) (v + w) - H v v - H w w := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    rw [hsymm]
    ring
  have hnorm_add :
      ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + 2 * ⟪v, w⟫_ℝ + ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right]
    rw [real_inner_comm w v, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have htwo :
      2 * H v w = 2 * heatKernel (E := E) t u *
        (⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
    rw [hpolar, hdiag, hdiag, hdiag, inner_add_right, hnorm_add]
    field_simp [ht]
    ring
  rw [iteratedFDeriv_two_apply]
  dsimp [H] at htwo ⊢
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/--
The Hessian is the Frechet derivative of the translated first spatial
derivative, including multiplication by a fixed data value.
-/
theorem hasFDerivAt_smul_fderiv_heatKernel_sub
    (t c : ℝ) (x y : E) :
    HasFDerivAt
      (fun z : E => c • fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y))
      (c • fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)) x := by
  have hsmooth :
      ContDiff ℝ 1 (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) :=
    (contDiff_heatKernel_spatial (E := E) t).fderiv_right (by norm_num)
  have houter :
      HasFDerivAt
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u))
        (fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y))
        (x - y) :=
    (hsmooth.differentiable (by norm_num) (x - y)).hasFDerivAt
  have hsub : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x := by
    simpa only [id_eq] using (hasFDerivAt_id (x := x)).sub_const y
  have hcomp := houter.comp x hsub
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_id] using hcomp.const_smul c

omit [MeasurableSpace E] [BorelSpace E] in
/-- Directional scalarization of the translated Hessian derivative. -/
theorem hasFDerivAt_fderiv_heatKernel_sub_apply_mul
    (t c : ℝ) (v x y : E) :
    HasFDerivAt
      (fun z : E =>
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * c)
      ((c • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v) x := by
  have h := (hasFDerivAt_smul_fderiv_heatKernel_sub
    (E := E) t c x y).clm_apply (hasFDerivAt_const v x)
  simpa [smul_eq_mul, mul_comm] using h

/-- Measurability of the bounded-data Hessian integrand. -/
theorem smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable
    (t : ℝ) {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (x : E) :
    AEStronglyMeasurable
      (fun y : E => f y •
        fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y))
      volume := by
  have hhessian :
      ContDiff ℝ 0
        (fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u))) :=
    ((contDiff_heatKernel_spatial (E := E) t).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  have hsub : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
  have hH : AEStronglyMeasurable
      (fun y : E =>
        fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y))
      volume :=
    (hhessian.continuous.comp hsub).aestronglyMeasurable
  exact hf.smul hH

/-- The constant in the locally uniform second-Frechet heat-kernel envelope. -/
def heatKernelSecondSpatialUniformConstant (t C : ℝ) (x₀ : E) (R : ℝ) : ℝ :=
  C * (1 / (4 * t ^ 2) + 1 / (2 * t)) *
    heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)

omit [MeasurableSpace E] [BorelSpace E] in
/--
The Hessian operator norm is controlled by the zeroth- and second-order
Gaussian factors.  This is the operator-valued estimate behind the second
spatial differentiation under the heat integral.
-/
theorem norm_fderiv_fderiv_heatKernel_le_order_two {t : ℝ} (ht : 0 < t) (u : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) u‖ ≤
      heatKernel (E := E) t u *
        (‖u‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by
  let H : E →L[ℝ] E →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) u
  let B : ℝ := heatKernel (E := E) t u *
    (‖u‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
  have hk_nonneg : 0 ≤ heatKernel (E := E) t u :=
    heatKernel_nonneg (E := E) ht u
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ContinuousLinearMap.opNorm_le_bound H hB_nonneg ?_
  intro v
  have hBv_nonneg : 0 ≤ B * ‖v‖ := mul_nonneg hB_nonneg (norm_nonneg v)
  refine ContinuousLinearMap.opNorm_le_bound (H v) hBv_nonneg ?_
  intro w
  have hformula :
      H v w = heatKernel (E := E) t u *
        (⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) := by
    simpa [H, iteratedFDeriv_two_apply] using
      (iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination
        (E := E) ht.ne' u v w)
  have hfirst :
      ‖⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2)‖ ≤
        (‖u‖ ^ 2 / (4 * t ^ 2)) * (‖v‖ * ‖w‖) := by
    rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4 * t ^ 2)]
    have huv := abs_real_inner_le_norm u v
    have huw := abs_real_inner_le_norm u w
    have hmul : |⟪u, v⟫_ℝ| * |⟪u, w⟫_ℝ| ≤
        (‖u‖ * ‖v‖) * (‖u‖ * ‖w‖) :=
      mul_le_mul huv huw (abs_nonneg _) (mul_nonneg (norm_nonneg u) (norm_nonneg v))
    apply (div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 4 * t ^ 2)).trans_eq
    ring
  have hsecond :
      ‖⟪v, w⟫_ℝ / (2 * t)‖ ≤
        (1 / (2 * t)) * (‖v‖ * ‖w‖) := by
    rw [norm_div, Real.norm_eq_abs,
      Real.norm_of_nonneg (by positivity : 0 ≤ 2 * t)]
    have hvw := abs_real_inner_le_norm v w
    apply (div_le_div_of_nonneg_right hvw (by positivity : 0 ≤ 2 * t)).trans_eq
    field_simp [ht.ne']
  rw [hformula, norm_mul, Real.norm_of_nonneg hk_nonneg]
  calc
    heatKernel (E := E) t u *
        ‖⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)‖
        ≤ heatKernel (E := E) t u *
            (‖⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ / (4 * t ^ 2)‖ +
              ‖⟪v, w⟫_ℝ / (2 * t)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk_nonneg
    _ ≤ heatKernel (E := E) t u *
          ((‖u‖ ^ 2 / (4 * t ^ 2)) * (‖v‖ * ‖w‖) +
            (1 / (2 * t)) * (‖v‖ * ‖w‖)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hk_nonneg
    _ = (B * ‖v‖) * ‖w‖ := by
          dsimp [B]
          ring

omit [MeasurableSpace E] [BorelSpace E] in
/--
Uniform closed-ball integrable envelope for a bounded scalar multiple of the
second spatial Frechet derivative of the translated heat kernel.
-/
theorem norm_smul_fderiv_fderiv_heatKernel_sub_le_uniformTranslateEnvelope
    {t R C c : ℝ} (ht : 0 < t) (hR : 0 ≤ R) (hc : ‖c‖ ≤ C)
    {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R) :
    ‖c • fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) (x - y)‖ ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelSecondSpatialUniformConstant (E := E) t C x₀ R) y := by
  have hC_nonneg : 0 ≤ C := (norm_nonneg c).trans hc
  have hessian := norm_fderiv_fderiv_heatKernel_le_order_two (E := E) ht (x - y)
  have hzero := heatKernel_translate_polynomial_le_uniformEnvelope (E := E) ht hR
    (y := y) hx
    (m := 0) (by norm_num)
  have htwo := heatKernel_translate_order_two_le_uniformEnvelope (E := E) ht hR
    (y := y) hx
  have ha_nonneg : 0 ≤ C / (4 * t ^ 2) := by positivity
  have hb_nonneg : 0 ≤ C / (2 * t) := by positivity
  calc
    ‖c • fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) (x - y)‖
        ≤ ‖c‖ * ‖fderiv ℝ (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) (x - y)‖ :=
          norm_real_smul_continuousLinearMap_two_le _ _
    _
        ≤ C * (heatKernel (E := E) t (x - y) *
          (‖x - y‖ ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) := by
            exact mul_le_mul hc hessian
              (norm_nonneg (fderiv ℝ
                (fderiv ℝ (fun z : E => heatKernel (E := E) t z)) (x - y)))
              hC_nonneg
    _ = (C / (4 * t ^ 2)) *
          (‖x - y‖ ^ 2 * heatKernel (E := E) t (x - y)) +
        (C / (2 * t)) * heatKernel (E := E) t (x - y) := by ring
    _ ≤ (C / (4 * t ^ 2)) *
          heatKernelUniformTranslateEnvelope (E := E) t
            (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y +
        (C / (2 * t)) *
          heatKernelUniformTranslateEnvelope (E := E) t
            (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left htwo ha_nonneg)
              (mul_le_mul_of_nonneg_left (by simpa using hzero) hb_nonneg)
    _ = heatKernelUniformTranslateEnvelope (E := E) t
          (heatKernelSecondSpatialUniformConstant (E := E) t C x₀ R) y := by
            simp [heatKernelUniformTranslateEnvelope, heatKernelSecondSpatialUniformConstant]
            ring

/-- The closed-ball second-Frechet envelope is integrable. -/
theorem integrable_heatKernel_secondSpatial_uniformEnvelope {t R C : ℝ}
    (ht : 0 < t) (x₀ : E) :
    Integrable (fun y : E =>
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelSecondSpatialUniformConstant (E := E) t C x₀ R) y) :=
  integrable_heatKernelUniformTranslateEnvelope (E := E) ht _

/-- Integrability of the bounded-data first spatial derivative integrand. -/
theorem integrable_smul_fderiv_heatKernel_sub
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    Integrable (fun y : E => f y •
      fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) volume := by
  let bound : E → ℝ := fun y =>
    C * heatKernelUniformTranslateEnvelope (E := E) t
      ((1 / (2 * t)) *
        heatKernelUniformTranslateConstant (E := E) t ‖x‖) y
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hmeas : AEStronglyMeasurable
      (fun y : E => f y •
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) volume := by
    have hfd : ContDiff ℝ 0
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) :=
      (contDiff_heatKernel_spatial (E := E) t).fderiv_right (m := 0) (by norm_num)
    have hsub : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
    exact hf.smul (hfd.continuous.comp hsub).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    have henv := integrable_heatKernelUniformTranslateEnvelope (E := E) ht
      ((1 / (2 * t)) * heatKernelUniformTranslateConstant (E := E) t ‖x‖)
    simpa [bound] using henv.const_mul C
  refine hbound_int.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hx : x ∈ Metric.closedBall x (0 : ℝ) := by simp
  have hfd := fderiv_heatKernel_norm_le_uniformTranslateEnvelope
    (E := E) ht (R := (0 : ℝ)) (x₀ := x) (x := x) (y := y) (by norm_num) hx
  calc
    ‖f y • fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)‖
        ≤ ‖f y‖ *
            ‖fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)‖ :=
          norm_real_smul_continuousLinearMap_one_le _ _
    _ ≤ C * heatKernelUniformTranslateEnvelope (E := E) t
          ((1 / (2 * t)) * heatKernelUniformTranslateConstant (E := E) t ‖x‖) y :=
      mul_le_mul (hC y) (by simpa using hfd) (norm_nonneg _) hC_nonneg
    _ = bound y := rfl

/-- Integrability of an evaluated bounded-data Hessian integrand. -/
theorem integrable_smul_fderiv_fderiv_heatKernel_sub_flip
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x v : E) :
    Integrable (fun y : E =>
      ((f y • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v))
      volume := by
  let bound : E → ℝ := fun y =>
    heatKernelUniformTranslateEnvelope (E := E) t
      (heatKernelSecondSpatialUniformConstant (E := E) t C x 0) y * ‖v‖
  have hnested := smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable
    (E := E) t hf x
  have hflip : Continuous
      (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip v) := by
    have h₁ : Continuous
        (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    exact ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v).continuous.comp h₁
  have hmeas := hflip.comp_aestronglyMeasurable hnested
  have hbound_int : Integrable bound volume := by
    have henv := integrable_heatKernel_secondSpatial_uniformEnvelope
      (E := E) (R := (0 : ℝ)) (C := C) ht x
    simpa [bound, mul_comm] using henv.const_mul ‖v‖
  refine hbound_int.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hx : x ∈ Metric.closedBall x (0 : ℝ) := by simp
  have hH := norm_smul_fderiv_fderiv_heatKernel_sub_le_uniformTranslateEnvelope
    (E := E) ht (R := (0 : ℝ)) (C := C) (c := f y)
      (by norm_num) (hC y) (x₀ := x) (x := x) (y := y) hx
  calc
    ‖((f y • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)‖
        ≤ ‖(f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ v
    _ = ‖f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)‖ * ‖v‖ := by
          rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ heatKernelUniformTranslateEnvelope (E := E) t
            (heatKernelSecondSpatialUniformConstant (E := E) t C x 0) y * ‖v‖ :=
          mul_le_mul_of_nonneg_right hH (norm_nonneg v)
    _ = bound y := rfl

/-- First spatial Frechet differentiation under the bounded-data heat integral. -/
theorem heatKernel_integral_hasFDerivAt
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    HasFDerivAt
      (fun z : E => ∫ y : E, heatKernel (E := E) t (z - y) * f y)
      (∫ y : E, f y •
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) x := by
  let s : Set E := Metric.closedBall x 1
  let bound : E → ℝ := fun y =>
    C * heatKernelUniformTranslateEnvelope (E := E) t
      ((1 / (2 * t)) *
        heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1)) y
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hs : s ∈ nhds x := Metric.closedBall_mem_nhds x (by norm_num)
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable
        (fun y : E => heatKernel (E := E) t (z - y) * f y) volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have hsub : Continuous (fun y : E => z - y) := continuous_const.sub continuous_id
    exact ((contDiff_heatKernel_spatial (E := E) t).continuous.comp hsub)
      |>.aestronglyMeasurable.mul hf
  have hF_int : Integrable
      (fun y : E => heatKernel (E := E) t (x - y) * f y) volume :=
    (heatKernel_bounded_data_domination (E := E) ht hf hC x).2.2
  have hF'_meas : AEStronglyMeasurable
      (fun y : E => f y •
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) volume := by
    have hfd : ContDiff ℝ 0
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) :=
      (contDiff_heatKernel_spatial (E := E) t).fderiv_right (m := 0) (by norm_num)
    have hsub : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
    exact hf.smul (hfd.continuous.comp hsub).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    have henv := integrable_heatKernelUniformTranslateEnvelope (E := E) ht
      ((1 / (2 * t)) *
        heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1))
    simpa [bound] using henv.const_mul C
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      ‖f y • fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y)‖ ≤
        bound y := by
    refine Filter.Eventually.of_forall ?_
    intro y z hz
    have hfd := fderiv_heatKernel_norm_le_uniformTranslateEnvelope
      (E := E) ht (R := (1 : ℝ)) (x₀ := x) (x := z) (y := y) (by norm_num) hz
    calc
      ‖f y • fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y)‖
          ≤ ‖f y‖ *
              ‖fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y)‖ :=
            norm_real_smul_continuousLinearMap_one_le _ _
      _ ≤ C * heatKernelUniformTranslateEnvelope (E := E) t
            ((1 / (2 * t)) *
              heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1)) y :=
        mul_le_mul (hC y) hfd (norm_nonneg _) hC_nonneg
      _ = bound y := rfl
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      HasFDerivAt
        (fun z : E => heatKernel (E := E) t (z - y) * f y)
        (f y • fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y)) z := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    have hbase := hasFDerivAt_heatKernel_spatial (E := E) ht.ne' (z - y)
    have hsub : HasFDerivAt (fun q : E => q - y) (ContinuousLinearMap.id ℝ E) z := by
      simpa only [id_eq] using (hasFDerivAt_id (x := z)).sub_const y
    have h := (hbase.comp z hsub).mul_const (f y)
    convert h using 1
    · rw [← hbase.fderiv]
      ext w
      simp
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => heatKernel (E := E) t (z - y) * f y)
    (F' := fun z y => f y •
      fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y))
    (x₀ := x) (s := s) (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff

/-- First spatial Frechet derivative formula for the actual heat solution. -/
theorem heatSolution_hasFDerivAt
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    HasFDerivAt (heatSolution (E := E) t f)
      (∫ y : E, f y •
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) x := by
  have h := heatKernel_integral_hasFDerivAt (E := E) ht hf hC x
  convert h using 1
  ext z
  exact heatSolution_apply_swap (E := E) t f z

/-- Evaluation formula for the first spatial Frechet derivative of the heat solution. -/
theorem fderiv_heatSolution_apply
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x v : E) :
    fderiv ℝ (heatSolution (E := E) t f) x v =
      ∫ y : E,
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y) v * f y := by
  rw [(heatSolution_hasFDerivAt (E := E) ht hf hC x).fderiv]
  have hint := integrable_smul_fderiv_heatKernel_sub (E := E) ht hf hC x
  rw [ContinuousLinearMap.integral_apply hint v]
  congr 1
  funext y
  simp [smul_eq_mul, mul_comm]

/--
Directional second spatial differentiation under the heat integral.

The derivative is integrated in the one-level operator space `E →L[ℝ] ℝ`.
This scalarized form retains every Hessian component and avoids imposing an
incompatible Bochner topology on the nested operator bundle.
-/
theorem heatKernel_firstDirectional_integral_hasFDerivAt
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x v : E) :
    HasFDerivAt
      (fun z : E => ∫ y : E,
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * f y)
      (∫ y : E,
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) x := by
  let s : Set E := Metric.closedBall x 1
  let firstEnvelope : E → ℝ := fun y =>
    C * ‖v‖ * heatKernelUniformTranslateEnvelope (E := E) t
      ((1 / (2 * t)) *
        heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1)) y
  let secondEnvelope : E → ℝ := fun y =>
    heatKernelUniformTranslateEnvelope (E := E) t
      (heatKernelSecondSpatialUniformConstant (E := E) t C x 1) y * ‖v‖
  have hC_nonneg : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hs : s ∈ nhds x := by
    exact Metric.closedBall_mem_nhds x (by norm_num)
  have hfirst_meas (z : E) : AEStronglyMeasurable
      (fun y : E =>
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * f y)
      volume := by
    have hfd : ContDiff ℝ 0
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) :=
      (contDiff_heatKernel_spatial (E := E) t).fderiv_right (m := 0) (by norm_num)
    have hsub : Continuous (fun y : E => z - y) := continuous_const.sub continuous_id
    have heval : Continuous (fun L : E →L[ℝ] ℝ => L v) :=
      ((ContinuousLinearMap.apply ℝ ℝ) v).continuous
    have hscalar : Continuous (fun y : E =>
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v) :=
      heval.comp (hfd.continuous.comp hsub)
    exact hscalar.aestronglyMeasurable.mul hf
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable
        (fun y : E =>
          fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * f y)
        volume :=
    Filter.Eventually.of_forall hfirst_meas
  have hfirstEnvelope_int : Integrable firstEnvelope volume := by
    have henv := integrable_heatKernelUniformTranslateEnvelope (E := E) ht
      ((1 / (2 * t)) *
        heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1))
    simpa [firstEnvelope, mul_assoc] using henv.const_mul (C * ‖v‖)
  have hx_closed : x ∈ Metric.closedBall x (1 : ℝ) := by
    simp [Metric.mem_closedBall]
  have hF_int : Integrable
      (fun y : E =>
        fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y) v * f y)
      volume := by
    refine hfirstEnvelope_int.mono' (hfirst_meas x) ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    have hfd := fderiv_heatKernel_norm_le_uniformTranslateEnvelope
      (E := E) ht (R := (1 : ℝ)) (x₀ := x) (x := x) (y := y) (by norm_num) hx_closed
    have happ := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)) v
    calc
      ‖fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y) v * f y‖
          = ‖fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y) v‖ *
              ‖f y‖ := norm_mul _ _
      _ ≤ (‖fderiv ℝ (fun u : E => heatKernel (E := E) t u) (x - y)‖ * ‖v‖) * C := by
        exact mul_le_mul happ (hC y) (norm_nonneg _) (by positivity)
      _ ≤ (heatKernelUniformTranslateEnvelope (E := E) t
              ((1 / (2 * t)) *
                heatKernelUniformTranslateConstant (E := E) t (‖x‖ + 1)) y * ‖v‖) * C := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfd (norm_nonneg v)) hC_nonneg
      _ = firstEnvelope y := by
        dsimp [firstEnvelope]
        ring
  have hF'_meas : AEStronglyMeasurable
      (fun y : E =>
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v))
      volume := by
    have hnested := smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable
      (E := E) t hf x
    have hflip : Continuous
        (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip v) := by
      have h₁ : Continuous
          (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip) :=
        (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
      have h₂ : Continuous (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip v) :=
        ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v).continuous.comp h₁
      exact h₂
    exact hflip.comp_aestronglyMeasurable hnested
  have hsecondEnvelope_int : Integrable secondEnvelope volume := by
    have henv := integrable_heatKernel_secondSpatial_uniformEnvelope
      (E := E) (R := (1 : ℝ)) (C := C) ht x
    simpa [secondEnvelope, mul_comm] using henv.const_mul ‖v‖
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      ‖((f y • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v)‖ ≤
        secondEnvelope y := by
    refine Filter.Eventually.of_forall ?_
    intro y z hz
    have hH := norm_smul_fderiv_fderiv_heatKernel_sub_le_uniformTranslateEnvelope
      (E := E) ht (R := (1 : ℝ)) (C := C) (c := f y)
        (by norm_num) (hC y) (x₀ := x) (x := z) (y := y) hz
    calc
      ‖((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v)‖
          ≤ ‖(f y • fderiv ℝ
              (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ v
      _ = ‖f y • fderiv ℝ
              (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)‖ * ‖v‖ := by
            rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ heatKernelUniformTranslateEnvelope (E := E) t
              (heatKernelSecondSpatialUniformConstant (E := E) t C x 1) y * ‖v‖ :=
            mul_le_mul_of_nonneg_right hH (norm_nonneg v)
      _ = secondEnvelope y := rfl
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      HasFDerivAt
        (fun z : E =>
          fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * f y)
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v) z := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    exact hasFDerivAt_fderiv_heatKernel_sub_apply_mul (E := E) t (f y) v z y
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y =>
      fderiv ℝ (fun u : E => heatKernel (E := E) t u) (z - y) v * f y)
    (F' := fun z y =>
      ((f y • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v))
    (x₀ := x) (s := s) (bound := secondEnvelope)
    hs hF_meas hF_int hF'_meas h_bound hsecondEnvelope_int h_diff

/--
Actual second spatial differentiation of the heat solution after evaluation in
one fixed first direction.  A finite basis of `E` therefore recovers every
component of the Hessian without integrating into the problematic nested
operator topology.
-/
theorem heatSolution_fderiv_apply_hasFDerivAt
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x v : E) :
    HasFDerivAt
      (fun z : E => fderiv ℝ (heatSolution (E := E) t f) z v)
      (∫ y : E,
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) x := by
  have h := heatKernel_firstDirectional_integral_hasFDerivAt
    (E := E) ht hf hC x v
  convert h using 1
  ext z
  exact fderiv_heatSolution_apply (E := E) ht hf hC z v

/-- Continuity of every evaluated Hessian integral. -/
theorem continuous_heatSolution_secondDirectionalField
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (v : E) :
    Continuous (fun z : E =>
      ∫ y : E,
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let bound : E → ℝ := fun y =>
    heatKernelUniformTranslateEnvelope (E := E) t
      (heatKernelSecondSpatialUniformConstant (E := E) t C x 1) y * ‖v‖
  have hflip : Continuous
      (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip v) := by
    have h₁ : Continuous
        (fun H : E →L[ℝ] E →L[ℝ] ℝ => H.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    exact ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v).continuous.comp h₁
  have hF_meas : ∀ᶠ z in nhds x, AEStronglyMeasurable
      (fun y : E =>
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v))
      volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    exact hflip.comp_aestronglyMeasurable
      (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable (E := E) t hf z)
  have h_bound : ∀ᶠ z in nhds x, ∀ᵐ y ∂(volume : Measure E),
      ‖((f y • fderiv ℝ
        (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v)‖ ≤
        bound y := by
    filter_upwards [Metric.closedBall_mem_nhds x (ε := (1 : ℝ)) (by norm_num)] with z hz
    refine Filter.Eventually.of_forall ?_
    intro y
    have hH := norm_smul_fderiv_fderiv_heatKernel_sub_le_uniformTranslateEnvelope
      (E := E) ht (R := (1 : ℝ)) (C := C) (c := f y)
        (by norm_num) (hC y) (x₀ := x) (x := z) (y := y) hz
    calc
      ‖((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v)‖
          ≤ ‖(f y • fderiv ℝ
              (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ v
      _ = ‖f y • fderiv ℝ
              (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)‖ * ‖v‖ := by
            rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ heatKernelUniformTranslateEnvelope (E := E) t
              (heatKernelSecondSpatialUniformConstant (E := E) t C x 1) y * ‖v‖ :=
            mul_le_mul_of_nonneg_right hH (norm_nonneg v)
      _ = bound y := rfl
  have hbound_int : Integrable bound volume := by
    have henv := integrable_heatKernel_secondSpatial_uniformEnvelope
      (E := E) (R := (1 : ℝ)) (C := C) ht x
    simpa [bound, mul_comm] using henv.const_mul ‖v‖
  have h_lim : ∀ᵐ y ∂(volume : Measure E),
      Tendsto
        (fun z : E =>
          ((f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)).flip v))
        (nhds x)
        (nhds ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have hhessian : ContDiff ℝ 0
        (fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u))) :=
      ((contDiff_heatKernel_spatial (E := E) t).fderiv_right
        (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
    have hsub : Continuous (fun z : E => z - y) := continuous_id.sub continuous_const
    have hsmul : Continuous (fun z : E => f y •
        fderiv ℝ (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (z - y)) :=
      continuous_const.smul (hhessian.continuous.comp hsub)
    exact (hflip.comp hsmul).continuousAt
  exact tendsto_integral_filter_of_dominated_convergence
    bound hF_meas h_bound hbound_int h_lim

/-- Each evaluated first derivative of the heat solution is `C¹`. -/
theorem contDiff_one_fderiv_heatSolution_apply
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (v : E) :
    ContDiff ℝ 1 (fun x : E => fderiv ℝ (heatSolution (E := E) t f) x v) := by
  have hdiff : Differentiable ℝ
      (fun x : E => fderiv ℝ (heatSolution (E := E) t f) x v) := fun x =>
    (heatSolution_fderiv_apply_hasFDerivAt (E := E) ht hf hC x v).differentiableAt
  have hfield := continuous_heatSolution_secondDirectionalField (E := E) ht hf hC v
  have happ (w : E) : ContDiff ℝ 0
      (fun x : E => fderiv ℝ
        (fun z : E => fderiv ℝ (heatSolution (E := E) t f) z v) x w) := by
    rw [contDiff_zero]
    have heval : Continuous (fun x : E =>
        (∫ y : E,
          ((f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) w) :=
      ((ContinuousLinearMap.apply ℝ ℝ) w).continuous.comp hfield
    convert heval using 1
    ext x
    rw [(heatSolution_fderiv_apply_hasFDerivAt (E := E) ht hf hC x v).fderiv]
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num]
  exact contDiff_succ_iff_fderiv_apply.mpr
    ⟨hdiff, (fun h => by simp at h), happ⟩

/-- Bounded measurable data produce a twice continuously Frechet-differentiable heat solution. -/
theorem contDiff_two_heatSolution_of_bounded_measurable
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C) :
    ContDiff ℝ 2 (heatSolution (E := E) t f) := by
  have hdiff : Differentiable ℝ (heatSolution (E := E) t f) := fun x =>
    (heatSolution_hasFDerivAt (E := E) ht hf hC x).differentiableAt
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num]
  exact contDiff_succ_iff_fderiv_apply.mpr
    ⟨hdiff, (fun h => by simp at h), contDiff_one_fderiv_heatSolution_apply (E := E) ht hf hC⟩

/-- Diagonal Hessian components commute with the bounded-data heat integral. -/
theorem iteratedFDeriv_two_heatSolution_apply_diagonal
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x v : E) :
    iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![v, v] =
      ∫ y : E,
        iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y) ![v, v] *
          f y := by
  let U : E → ℝ := heatSolution (E := E) t f
  let H : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ U) x
  have hUtwo : ContDiff ℝ 2 U := by
    simpa [U] using contDiff_two_heatSolution_of_bounded_measurable (E := E) ht hf hC
  have hD : HasFDerivAt (fderiv ℝ U) H x := by
    have hDone : ContDiff ℝ 1 (fderiv ℝ U) :=
      hUtwo.fderiv_right (m := 1) (by norm_num)
    exact (hDone.differentiable (by norm_num) x).hasFDerivAt
  have hcalc : HasFDerivAt (fun z : E => fderiv ℝ U z v) (H.flip v) x := by
    have h := hD.clm_apply (hasFDerivAt_const v x)
    simpa [H] using h
  have hgiven : HasFDerivAt (fun z : E => fderiv ℝ U z v)
      (∫ y : E,
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) x := by
    simpa [U] using heatSolution_fderiv_apply_hasFDerivAt (E := E) ht hf hC x v
  have heq : H.flip v =
      ∫ y : E,
        ((f y • fderiv ℝ
          (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v) :=
    hcalc.unique hgiven
  have hint := integrable_smul_fderiv_fderiv_heatKernel_sub_flip
    (E := E) ht hf hC x v
  rw [iteratedFDeriv_two_apply]
  change H v v = _
  calc
    H v v = H.flip v v := rfl
    _ = (∫ y : E,
          ((f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v)) v := by
      rw [heq]
    _ = ∫ y : E,
          ((f y • fderiv ℝ
            (fderiv ℝ (fun u : E => heatKernel (E := E) t u)) (x - y)).flip v) v :=
      ContinuousLinearMap.integral_apply hint v
    _ = ∫ y : E,
          iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y) ![v, v] *
            f y := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro y
      simp [iteratedFDeriv_two_apply, smul_eq_mul, mul_comm]

/-- The spatial Laplacian commutes with the bounded-data heat integral. -/
theorem laplacian_heatSolution_eq_integral_laplacian_heatKernel
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    (Δ fun z : E => heatSolution (E := E) t f z) x =
      ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y := by
  let b := stdOrthonormalBasis ℝ E
  have hdiag (i : Fin (Module.finrank ℝ E)) :
      iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i] =
        ∫ y : E,
          iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y)
              ![b i, b i] * f y :=
    iteratedFDeriv_two_heatSolution_apply_diagonal (E := E) ht hf hC x (b i)
  have hint (i : Fin (Module.finrank ℝ E)) : Integrable
      (fun y : E =>
        iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y)
            ![b i, b i] * f y) volume := by
    have hraw := (integrable_smul_fderiv_fderiv_heatKernel_sub_flip
      (E := E) ht hf hC x (b i)).apply_continuousLinearMap (b i)
    refine hraw.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [iteratedFDeriv_two_apply, smul_eq_mul, mul_comm]
  have hrhs :
      (∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) =
        ∫ y : E, (Δ fun u : E => heatKernel (E := E) t u) (x - y) * f y := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro y
    change (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y =
      (Δ fun u : E => heatKernel (E := E) t u) (x - y) * f y
    rw [laplacian_heatKernel_sub_left (E := E) t x y]
  have hlhs :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∑ i, iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i] := by
    simpa [b] using congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
        (f := heatSolution (E := E) t f)) x
  rw [hrhs]
  rw [hlhs]
  change (∑ i, iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i]) = _
  calc
    (∑ i, iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i]) =
        ∑ i, ∫ y : E,
          iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y)
              ![b i, b i] * f y := by
      exact Finset.sum_congr rfl fun i _hi => hdiag i
    _ = ∫ y : E, ∑ i,
          iteratedFDeriv ℝ 2 (fun u : E => heatKernel (E := E) t u) (x - y)
              ![b i, b i] * f y := by
      symm
      exact integral_finsetSum Finset.univ (fun i _hi => hint i)
    _ = ∫ y : E, (Δ fun u : E => heatKernel (E := E) t u) (x - y) * f y := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp only [Finset.sum_mul]
      rfl
  rfl

/-- The bounded-data heat convolution solves the Euclidean heat equation unconditionally. -/
theorem heatSolution_solves_heatEquation_of_bounded_measurable
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
      (Δ fun z : E => heatSolution (E := E) t f z) x := by
  exact heatSolution_solves_heatEquation_of_spatial_interchange (E := E) ht hf hC
    (laplacian_heatSolution_eq_integral_laplacian_heatKernel (E := E) ht hf hC x)

/-- The full model Cauchy problem, with both differentiation interchanges discharged. -/
theorem heatSolution_model_cauchy_problem
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : Integrable f) (hC : ∀ y, ‖f y‖ ≤ C)
    {x : E} (hcf : ContinuousAt f x) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
        (Δ fun z : E => heatSolution (E := E) t f z) x ∧
      Tendsto (fun τ : ℝ => heatSolution (E := E) τ f x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  exact heatSolution_model_cauchy_problem_of_spatial_interchange (E := E)
    ht hf hC hcf
      (laplacian_heatSolution_eq_integral_laplacian_heatKernel
        (E := E) ht hf.aestronglyMeasurable hC x)

/-- Bounded measurable data produce a continuously Frechet-differentiable heat solution. -/
theorem contDiff_one_heatSolution_of_bounded_measurable
    {t C : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C) :
    ContDiff ℝ 1 (heatSolution (E := E) t f) := by
  have hdiff : Differentiable ℝ (heatSolution (E := E) t f) := by
    intro x
    exact (heatSolution_hasFDerivAt (E := E) ht hf hC x).differentiableAt
  have happ (v : E) :
      ContDiff ℝ 0 (fun x : E => fderiv ℝ (heatSolution (E := E) t f) x v) := by
    rw [contDiff_zero]
    have hdv : Differentiable ℝ
        (fun x : E => fderiv ℝ (heatSolution (E := E) t f) x v) := fun x =>
      (heatSolution_fderiv_apply_hasFDerivAt (E := E) ht hf hC x v).differentiableAt
    exact hdv.continuous
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num]
  exact contDiff_succ_iff_fderiv_apply.mpr
    ⟨hdiff, (fun h => by simp at h), happ⟩

end Measurable

end Poincare
