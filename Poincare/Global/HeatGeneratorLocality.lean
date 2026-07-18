import Poincare.Global.HeatLaplacianZeroTime
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Pointwise locality of the strong `BUC` heat generator

The strong heat generator is defined by convergence in the global uniform
norm, while the Euclidean Laplacian is local.  This file bridges those two
descriptions at a single spatial point.  The analytic input is the Gaussian
off-diagonal estimate: if a bounded scalar datum vanishes near `z`, then its
heat convolution at `z` is `o(t)` as `t ↓ 0`.

The eventual application localizes a scalar coordinate by a smooth compactly
supported cutoff.  Thus only `ContDiffAt ℝ 2` at the tested point is needed;
no global bounds on classical derivatives are assumed.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace Laplacian ContDiff
  BoundedContinuousFunction

namespace Poincare

section GaussianTail

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Ratio of the Gaussian normalization at times `t` and `2t`. -/
def heatKernelTwoTimeGaussianRatio (t : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) /
    (4 * Real.pi * (2 * t)) ^ (-(Module.finrank ℝ E : ℝ) / 2)

/-- The normalization ratio between times `t` and `2t` is independent of
`t`. -/
theorem heatKernelTwoTimeGaussianRatio_eq {t : ℝ} (ht : 0 < t) :
    heatKernelTwoTimeGaussianRatio (E := E) t =
      (2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  unfold heatKernelTwoTimeGaussianRatio
  set p : ℝ := -(Module.finrank ℝ E : ℝ) / 2
  set A : ℝ := (4 * Real.pi * t) ^ p
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have hA : A ≠ 0 := (Real.rpow_pos_of_pos hbase p).ne'
  have hden : (4 * Real.pi * (2 * t)) ^ p = (2 : ℝ) ^ p * A := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring]
    exact Real.mul_rpow (by positivity) hbase.le
  rw [hden]
  change A / ((2 : ℝ) ^ p * A) = _
  calc
    A / ((2 : ℝ) ^ p * A) = 1 / (2 : ℝ) ^ p := by
      field_simp [hA]
    _ = (2 : ℝ) ^ (-p) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp
    _ = (2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
      congr 1
      dsimp [p]
      ring

/-- Splitting the Gaussian exponential in half expresses the time-`t`
kernel through the time-`2t` kernel. -/
theorem heatKernel_eq_twoTimeGaussianRatio_mul {t : ℝ} (ht : 0 < t)
    (y : E) :
    heatKernel (E := E) t y =
      heatKernelTwoTimeGaussianRatio (E := E) t *
        Real.exp (-(‖y‖ ^ 2) / (8 * t)) *
          heatKernel (E := E) (2 * t) y := by
  unfold heatKernel heatKernelTwoTimeGaussianRatio
  set p : ℝ := -(Module.finrank ℝ E : ℝ) / 2
  set A : ℝ := (4 * Real.pi * t) ^ p
  set B : ℝ := (4 * Real.pi * (2 * t)) ^ p
  have hBbase : 0 < 4 * Real.pi * (2 * t) := by positivity
  have hB : B ≠ 0 := (Real.rpow_pos_of_pos hBbase p).ne'
  change A * Real.exp (-(‖y‖ ^ 2) / (4 * t)) =
    A / B * Real.exp (-(‖y‖ ^ 2) / (8 * t)) *
      (B * Real.exp (-(‖y‖ ^ 2) / (4 * (2 * t))))
  rw [show -(‖y‖ ^ 2) / (4 * (2 * t)) =
      -(‖y‖ ^ 2) / (8 * t) by ring]
  let e : ℝ := Real.exp (-(‖y‖ ^ 2) / (8 * t))
  have hproduct : A / B * e * (B * e) = A * (e * e) := by
    field_simp [hB]
    <;> ring
  have hexponent :
      -(‖y‖ ^ 2) / (8 * t) + -(‖y‖ ^ 2) / (8 * t) =
        -(‖y‖ ^ 2) / (4 * t) := by ring
  rw [show Real.exp (-(‖y‖ ^ 2) / (8 * t)) = e by rfl, hproduct,
    ← Real.exp_add, hexponent]

/-- Off a radius-`R` ball, the heat kernel has a uniform exponentially small
factor relative to the mass-one kernel at time `2t`. -/
theorem heatKernel_le_twoTimeGaussian_of_norm_ge {t R : ℝ}
    (ht : 0 < t) (hR : 0 ≤ R) {y : E} (hy : R ≤ ‖y‖) :
    heatKernel (E := E) t y ≤
      (2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-(R ^ 2) / (8 * t)) *
          heatKernel (E := E) (2 * t) y := by
  rw [heatKernel_eq_twoTimeGaussianRatio_mul (E := E) ht,
    heatKernelTwoTimeGaussianRatio_eq (E := E) ht]
  have hsquares : R ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith
  have hexponent :
      -(‖y‖ ^ 2) / (8 * t) ≤ -(R ^ 2) / (8 * t) := by
    exact div_le_div_of_nonneg_right (neg_le_neg hsquares) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (Real.rpow_nonneg (by norm_num) _))
    (heatKernel_nonneg (E := E) (by positivity) y)

/-- The exponentially small off-diagonal factor is `o(t)` at zero. -/
theorem tendsto_exp_neg_radius_sq_div_eight_mul_inv_div_time_zero
    {R : ℝ} (hR : 0 < R) :
    Tendsto
      (fun t : ℝ ↦ Real.exp (-(R ^ 2) / (8 * t)) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let c : ℝ := R ^ 2 / 8
  have hc : 0 < c := by positivity
  have hx : Tendsto (fun t : ℝ ↦ c * t⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_inv_nhdsGT_zero
  have hdecay : Tendsto
      (fun t : ℝ ↦ (c * t⁻¹) ^ (1 : ℕ) * Real.exp (-(c * t⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  have hscaled := hdecay.const_mul (c⁻¹)
  have hscaled' : Tendsto
      (fun t : ℝ ↦ c⁻¹ *
        ((c * t⁻¹) ^ (1 : ℕ) * Real.exp (-(c * t⁻¹))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  have htne : t ≠ 0 := ht0.ne'
  have hcne : c ≠ 0 := hc.ne'
  change c⁻¹ * ((c * t⁻¹) ^ (1 : ℕ) * Real.exp (-(c * t⁻¹))) =
    Real.exp (-(R ^ 2) / (8 * t)) / t
  simp only [pow_one]
  have hcformula : c = R ^ 2 / 8 := rfl
  rw [hcformula]
  field_simp [htne, hcne]
  <;> ring

/-- A bounded uniformly continuous scalar datum which vanishes on a ball
around the tested point contributes `o(t)` to the heat orbit there. -/
theorem tendsto_heatSolution_div_time_zero_of_eq_zero_on_ball
    (f : BoundedUniformContinuousFunction (E := E) (F := ℝ))
    (z : E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ y : E, ‖y‖ < R → (f : E →ᵇ ℝ) (z - y) = 0) :
    Tendsto (fun t : ℝ ↦
      heatSolution (E := E) t (f : E →ᵇ ℝ) z / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let D : ℝ := (2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2)
  let A : ℝ := ‖f‖ * D
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg f) hD
  have hpoint (t : ℝ) (ht : 0 < t) :
      |heatSolution (E := E) t (f : E →ᵇ ℝ) z| ≤
        A * Real.exp (-(R ^ 2) / (8 * t)) := by
    let Q : ℝ := A * Real.exp (-(R ^ 2) / (8 * t))
    let bound : E → ℝ := fun y ↦ Q * heatKernel (E := E) (2 * t) y
    have ht2 : 0 < 2 * t := by positivity
    have hint : Integrable (fun y : E ↦
        heatKernel (E := E) t y * (f : E →ᵇ ℝ) (z - y)) volume := by
      simpa [smul_eq_mul] using
        integrable_heatKernel_smul_bcf_translate
          (E := E) ht (f : E →ᵇ ℝ) z
    have hboundInt : Integrable bound volume := by
      simpa [bound] using
        (heatKernel_integrable (E := E) ht2).const_mul Q
    have hnorm : ‖∫ y : E,
        heatKernel (E := E) t y * (f : E →ᵇ ℝ) (z - y)‖ ≤
          ∫ y : E, bound y := by
      apply MeasureTheory.norm_integral_le_of_norm_le hboundInt
      refine Filter.Eventually.of_forall ?_
      intro y
      by_cases hy : ‖y‖ < R
      · rw [hzero y hy]
        simp only [mul_zero, norm_zero]
        exact mul_nonneg
          (mul_nonneg hA (Real.exp_pos _).le)
          (heatKernel_nonneg (E := E) ht2 y)
      · have hy' : R ≤ ‖y‖ := le_of_not_gt hy
        have hkernel := heatKernel_le_twoTimeGaussian_of_norm_ge
          (E := E) ht hR.le hy'
        have hk : 0 ≤ heatKernel (E := E) t y :=
          heatKernel_nonneg (E := E) ht y
        have hfBound : ‖(f : E →ᵇ ℝ) (z - y)‖ ≤ ‖f‖ :=
          BoundedContinuousFunction.norm_coe_le_norm
            (f : E →ᵇ ℝ) (z - y)
        calc
          ‖heatKernel (E := E) t y * (f : E →ᵇ ℝ) (z - y)‖ =
              heatKernel (E := E) t y * ‖(f : E →ᵇ ℝ) (z - y)‖ := by
                rw [norm_mul, Real.norm_of_nonneg hk]
          _ ≤ heatKernel (E := E) t y * ‖f‖ :=
            mul_le_mul_of_nonneg_left hfBound hk
          _ ≤ (D * Real.exp (-(R ^ 2) / (8 * t)) *
                heatKernel (E := E) (2 * t) y) * ‖f‖ :=
            mul_le_mul_of_nonneg_right hkernel (norm_nonneg f)
          _ = bound y := by
            simp only [bound, Q, A, D]
            ring
    rw [heatSolution_apply]
    calc
      |∫ y : E, heatKernel (E := E) t y * (f : E →ᵇ ℝ) (z - y)| =
          ‖∫ y : E, heatKernel (E := E) t y * (f : E →ᵇ ℝ) (z - y)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y : E, bound y := hnorm
      _ = Q * (∫ y : E, heatKernel (E := E) (2 * t) y) := by
        simp only [bound, integral_const_mul]
      _ = Q := by rw [integral_heatKernel_eq_one (E := E) ht2, mul_one]
      _ = A * Real.exp (-(R ^ 2) / (8 * t)) := rfl
  have hupper : Tendsto
      (fun t : ℝ ↦ A *
        (Real.exp (-(R ^ 2) / (8 * t)) / t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_exp_neg_radius_sq_div_eight_mul_inv_div_time_zero
        hR).const_mul A
  have habs : Tendsto
      (fun t : ℝ ↦
        |heatSolution (E := E) t (f : E →ᵇ ℝ) z / t|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      calc
        |heatSolution (E := E) t (f : E →ᵇ ℝ) z / t| =
            |heatSolution (E := E) t (f : E →ᵇ ℝ) z| / t := by
          rw [abs_div, abs_of_pos ht0]
        _ ≤ (A * Real.exp (-(R ^ 2) / (8 * t))) / t :=
          div_le_div_of_nonneg_right (hpoint t ht0) ht0.le
        _ = A * (Real.exp (-(R ^ 2) / (8 * t)) / t) := by ring
    · exact hupper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

end GaussianTail

section ScalarHeatOrbit

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "ScalarBUC" =>
  BoundedUniformContinuousFunction (E := E) (F := ℝ)

/-- The scalar `BUC` heat orbit, evaluated at one spatial point. -/
def scalarBUCHeatOrbit (f : ScalarBUC) (z : E) : ℝ → ℝ :=
  fun t ↦
    ((vectorHeatSemigroupBUCExtended (E := E) (F := ℝ) t f : ScalarBUC) :
      E →ᵇ ℝ) z

@[simp]
theorem scalarBUCHeatOrbit_zero (f : ScalarBUC) (z : E) :
    scalarBUCHeatOrbit f z 0 = (f : E →ᵇ ℝ) z := by
  simp [scalarBUCHeatOrbit, vectorHeatSemigroupBUCExtended]

/-- At positive time the scalar `BUC` orbit is the usual scalar heat
convolution. -/
theorem scalarBUCHeatOrbit_eq_heatSolution (f : ScalarBUC) (z : E)
    {t : ℝ} (ht : 0 < t) :
    scalarBUCHeatOrbit f z t =
      heatSolution (E := E) t (f : E →ᵇ ℝ) z := by
  rw [scalarBUCHeatOrbit, vectorHeatSemigroupBUCExtended, dif_pos ht,
    vectorHeatSemigroupBUCLM_apply]
  change vectorHeatSolution (E := E) t (f : E →ᵇ ℝ) z = _
  rw [vectorHeatSolution_apply_data_translate, heatSolution_apply]
  simp only [smul_eq_mul]

/-- Evaluation at a fixed point preserves continuity of a scalar `BUC` heat
orbit. -/
theorem continuous_scalarBUCHeatOrbit (f : ScalarBUC) (z : E) :
    Continuous (scalarBUCHeatOrbit f z) := by
  let evalLinear : ScalarBUC →ₗ[ℝ] ℝ :=
    { toFun := fun g ↦ (g : E →ᵇ ℝ) z
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eval : ScalarBUC →L[ℝ] ℝ :=
    LinearMap.mkContinuous evalLinear 1 (fun g ↦ by
      change |(g : E →ᵇ ℝ) z| ≤ 1 * ‖g‖
      simpa using BoundedContinuousFunction.norm_coe_le_norm
        (g : E →ᵇ ℝ) z)
  exact eval.continuous.comp
    (continuous_vectorHeatSemigroupBUCExtended_apply
      (E := E) (F := ℝ) f)

/-- At positive time, the derivative of an evaluated scalar `BUC` heat orbit
is its spatial Laplacian. -/
theorem scalarBUCHeatOrbit_hasDerivAt_laplacian
    (f : ScalarBUC) (z : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (scalarBUCHeatOrbit f z)
      ((Δ fun y : E ↦ heatSolution (E := E) t (f : E →ᵇ ℝ) y) z) t := by
  have hfmeas : AEStronglyMeasurable ((f : E →ᵇ ℝ) : E → ℝ) volume :=
    (f : E →ᵇ ℝ).continuous.aestronglyMeasurable
  have hfbound : ∀ y : E, ‖(f : E →ᵇ ℝ) y‖ ≤ ‖f‖ := by
    intro y
    exact BoundedContinuousFunction.norm_coe_le_norm (f : E →ᵇ ℝ) y
  have hdiff : DifferentiableAt ℝ
      (fun τ : ℝ ↦ heatSolution (E := E) τ (f : E →ᵇ ℝ) z) t := by
    have hvec := vectorHeatSolution_time_differentiableAt
      (E := E) (F := ℝ) ht hfmeas hfbound z
    have heq :
        (fun τ : ℝ ↦ heatSolution (E := E) τ (f : E →ᵇ ℝ) z) =ᶠ[nhds t]
          (fun τ : ℝ ↦ vectorHeatSolution (E := E) τ
            (f : E →ᵇ ℝ) z) := by
      filter_upwards [eventually_gt_nhds ht] with τ hτ
      rw [vectorHeatSolution_apply_data_translate, heatSolution_apply]
      simp only [smul_eq_mul]
    exact hvec.congr_of_eventuallyEq heq
  have hpde := heatSolution_solves_heatEquation_of_bounded_measurable
    (E := E) ht hfmeas hfbound z
  have hheat : HasDerivAt
      (fun τ : ℝ ↦ heatSolution (E := E) τ (f : E →ᵇ ℝ) z)
      ((Δ fun y : E ↦ heatSolution (E := E) t (f : E →ᵇ ℝ) y) z) t := by
    rw [← hpde]
    exact hdiff.hasDerivAt
  have horbit : scalarBUCHeatOrbit f z =ᶠ[nhds t]
      (fun τ : ℝ ↦ heatSolution (E := E) τ (f : E →ᵇ ℝ) z) := by
    filter_upwards [eventually_gt_nhds ht] with τ hτ
    exact scalarBUCHeatOrbit_eq_heatSolution (E := E) f z hτ
  exact hheat.congr_of_eventuallyEq horbit

/-- A globally `C²` scalar `BUC` datum whose first two derivatives are
bounded has the expected classical right heat trace, provided its Laplacian
is represented by another scalar `BUC` datum. -/
theorem scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_bounded_derivatives
    (f lapf : ScalarBUC) (z : E)
    (hf : ContDiff ℝ 2 ((f : E →ᵇ ℝ) : E → ℝ))
    {C₁ C₂ : ℝ}
    (hC₁ : ∀ y : E, ‖fderiv ℝ ((f : E →ᵇ ℝ) : E → ℝ) y‖ ≤ C₁)
    (hC₂ : ∀ y : E,
      ‖fderiv ℝ (fderiv ℝ ((f : E →ᵇ ℝ) : E → ℝ)) y‖ ≤ C₂)
    (hlap : ∀ y : E, (lapf : E →ᵇ ℝ) y =
      (Δ ((f : E →ᵇ ℝ) : E → ℝ)) y) :
    HasDerivWithinAt (scalarBUCHeatOrbit f z) ((lapf : E →ᵇ ℝ) z)
      (Set.Ici 0) 0 := by
  let orbitF : ℝ → ℝ := scalarBUCHeatOrbit f z
  let orbitLap : ℝ → ℝ := scalarBUCHeatOrbit lapf z
  have horbitF : Continuous orbitF := continuous_scalarBUCHeatOrbit f z
  have horbitLap : Continuous orbitLap := continuous_scalarBUCHeatOrbit lapf z
  have hC₀ : ∀ y : E, ‖(f : E →ᵇ ℝ) y‖ ≤ ‖f‖ := by
    intro y
    exact BoundedContinuousFunction.norm_coe_le_norm (f : E →ᵇ ℝ) y
  have hpositive : ∀ t : ℝ, 0 < t → HasDerivAt orbitF (orbitLap t) t := by
    intro t ht
    have h := scalarBUCHeatOrbit_hasDerivAt_laplacian (E := E) f z ht
    rw [laplacian_heatSolution_eq_heatSolution_laplacian_of_bounded_derivatives
      (E := E) ht hf hC₀ hC₁ hC₂ z] at h
    have hlapfun :
        (fun y : E ↦ (Δ ((f : E →ᵇ ℝ) : E → ℝ)) y) =
          ((lapf : E →ᵇ ℝ) : E → ℝ) := by
      funext y
      exact (hlap y).symm
    rw [hlapfun, ← scalarBUCHeatOrbit_eq_heatSolution (E := E) lapf z ht] at h
    exact h
  have hzero := hasDerivWithinAt_zero_of_continuous_derivative_on_Ioi
    orbitF orbitLap horbitF horbitLap hpositive
  simpa [orbitF, orbitLap] using hzero

/-- If a scalar `BUC` datum vanishes near the tested point, its evaluated
heat orbit has zero right derivative at time zero. -/
theorem scalarBUCHeatOrbit_hasDerivWithinAt_zero_of_eq_zero_on_ball
    (f : ScalarBUC) (z : E) {R : ℝ} (hR : 0 < R)
    (hzero : ∀ y : E, ‖y‖ < R → (f : E →ᵇ ℝ) (z - y) = 0) :
    HasDerivWithinAt (scalarBUCHeatOrbit f z) 0 (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have htail := tendsto_heatSolution_div_time_zero_of_eq_zero_on_ball
    (E := E) f z hR hzero
  have hz : (f : E →ᵇ ℝ) z = 0 := by
    have := hzero 0 (by simpa using hR)
    simpa using this
  rw [Set.Ici_diff_left]
  apply htail.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  rw [slope_def_field, sub_zero,
    scalarBUCHeatOrbit_eq_heatSolution (E := E) f z ht0,
    scalarBUCHeatOrbit_zero, hz, sub_zero]

/-- Germ equality at the tested point is enough for two evaluated scalar heat
orbits to have the same right derivative at time zero. -/
theorem scalarBUCHeatOrbit_sub_hasDerivWithinAt_zero_of_eventuallyEq
    (f q : ScalarBUC) (z : E)
    (hlocal : ((f : E →ᵇ ℝ) : E → ℝ) =ᶠ[nhds z]
      ((q : E →ᵇ ℝ) : E → ℝ)) :
    HasDerivWithinAt (scalarBUCHeatOrbit (f - q) z) 0
      (Set.Ici 0) 0 := by
  have hset : {x : E | (f : E →ᵇ ℝ) x = (q : E →ᵇ ℝ) x} ∈
      nhds z := hlocal
  rcases Metric.mem_nhds_iff.mp hset with ⟨R, hR, hball⟩
  apply scalarBUCHeatOrbit_hasDerivWithinAt_zero_of_eq_zero_on_ball
    (E := E) (f - q) z hR
  intro y hy
  change (f : E →ᵇ ℝ) (z - y) - (q : E →ᵇ ℝ) (z - y) = 0
  apply sub_eq_zero.mpr
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  simpa using hy

/-- A scalar `BUC` germ which is `C²` at `z` has a globally `C²`, compactly
supported `BUC` representative with the same germ. -/
theorem exists_compactlySupported_scalarBUC_eventuallyEq_of_contDiffAt_two
    (f : ScalarBUC) (z : E)
    (hf : ContDiffAt ℝ 2 ((f : E →ᵇ ℝ) : E → ℝ) z) :
    ∃ q : ScalarBUC,
      ContDiff ℝ 2 ((q : E →ᵇ ℝ) : E → ℝ) ∧
      HasCompactSupport ((q : E →ᵇ ℝ) : E → ℝ) ∧
      ((q : E →ᵇ ℝ) : E → ℝ) =ᶠ[nhds z]
        ((f : E →ᵇ ℝ) : E → ℝ) := by
  let fraw : E → ℝ := ((f : E →ᵇ ℝ) : E → ℝ)
  have hlocal : ∀ᶠ y in nhds z, ContDiffAt ℝ 2 fraw y := by
    simpa [fraw] using hf.eventually (by norm_num : (2 : ℕ∞) ≠ ∞)
  rcases Metric.mem_nhds_iff.mp hlocal with ⟨R, hR, hball⟩
  let χ : ContDiffBump z :=
    { rIn := R / 4
      rOut := R / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let qraw : E → ℝ := fun y ↦ χ y * fraw y
  have hχsupport : tsupport (χ : E → ℝ) ⊆ Metric.ball z R := by
    intro y hy
    rw [χ.tsupport_eq, Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    dsimp [χ] at hy
    linarith
  have hqAt : ∀ y : E, ContDiffAt ℝ 2 qraw y := by
    intro y
    by_cases hy : y ∈ tsupport (χ : E → ℝ)
    · exact χ.contDiffAt.mul (hball (hχsupport hy))
    · have hχzero : (χ : E → ℝ) =ᶠ[nhds y] (fun _ ↦ 0) := by
        simpa using (notMem_tsupport_iff_eventuallyEq.mp hy)
      have hqzero : qraw =ᶠ[nhds y] (fun _ ↦ 0) := by
        filter_upwards [hχzero] with x hx
        simp [qraw, hx]
      exact (contDiffAt_const (x := y) (c := (0 : ℝ))).congr_of_eventuallyEq hqzero
  have hqContDiff : ContDiff ℝ 2 qraw := contDiff_iff_contDiffAt.mpr hqAt
  have hqcompact : HasCompactSupport qraw := by
    exact χ.hasCompactSupport.mul_right
  have hqcontinuous : Continuous qraw := hqContDiff.continuous
  let qBCF : E →ᵇ ℝ :=
    ofCompactSupport qraw hqcontinuous hqcompact
  let q : ScalarBUC :=
    ⟨qBCF, hqcompact.uniformContinuous_of_continuous hqcontinuous⟩
  have hqLocalRaw : qraw =ᶠ[nhds z] fraw := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    simp [qraw, hy]
  refine ⟨q, ?_, ?_, ?_⟩
  · change ContDiff ℝ 2 qraw
    exact hqContDiff
  · change HasCompactSupport qraw
    exact hqcompact
  · change qraw =ᶠ[nhds z] fraw
    exact hqLocalRaw

/-- The first Frechet derivative of a compactly supported global `C¹` scalar
datum is bounded. -/
theorem exists_fderiv_bound_of_contDiff_one_compactSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : E → F} (hq : ContDiff ℝ 1 q)
    (hqcompact : HasCompactSupport q) :
    ∃ C₁ : ℝ, ∀ y : E, ‖fderiv ℝ q y‖ ≤ C₁ := by
  have hfdcontinuous : Continuous (fderiv ℝ q) :=
    (hq.fderiv_right (m := 0) (by norm_num)).continuous
  have hfdcompact : HasCompactSupport (fderiv ℝ q) :=
    hqcompact.fderiv (𝕜 := ℝ)
  exact hfdcontinuous.bounded_above_of_compact_support hfdcompact

/-- The first Frechet derivative of a compactly supported global `C²` scalar
datum is bounded. -/
theorem exists_fderiv_bound_of_contDiff_two_compactSupport
    {q : E → ℝ} (hq : ContDiff ℝ 2 q)
    (hqcompact : HasCompactSupport q) :
    ∃ C₁ : ℝ, ∀ y : E, ‖fderiv ℝ q y‖ ≤ C₁ := by
  exact exists_fderiv_bound_of_contDiff_one_compactSupport
    (hq.of_le (by norm_num)) hqcompact

set_option maxHeartbeats 800000 in
/-- The second Frechet derivative of a compactly supported global `C²`
scalar datum is bounded. -/
theorem exists_second_fderiv_bound_of_contDiff_two_compactSupport
    {q : E → ℝ} (hq : ContDiff ℝ 2 q)
    (hqcompact : HasCompactSupport q) :
    ∃ C₂ : ℝ, ∀ y : E,
      ‖fderiv ℝ (fderiv ℝ q) y‖ ≤ C₂ := by
  have hqone : ContDiff ℝ 1 (fderiv ℝ q) :=
    hq.fderiv_right (m := 1) (by norm_num)
  exact exists_fderiv_bound_of_contDiff_one_compactSupport
    hqone (hqcompact.fderiv (𝕜 := ℝ))

set_option maxHeartbeats 800000 in
/-- The classical Laplacian of a compactly supported global `C²` scalar
`BUC` datum has a canonical scalar `BUC` representative. -/
theorem exists_scalarBUC_laplacian_of_contDiff_two_compactSupport
    (q : ScalarBUC)
    (hq : ContDiff ℝ 2 ((q : E →ᵇ ℝ) : E → ℝ))
    (hqcompact : HasCompactSupport ((q : E →ᵇ ℝ) : E → ℝ)) :
    ∃ lapq : ScalarBUC, ∀ y : E,
      (lapq : E →ᵇ ℝ) y =
        (Δ ((q : E →ᵇ ℝ) : E → ℝ)) y := by
  let qraw : E → ℝ := ((q : E →ᵇ ℝ) : E → ℝ)
  have hqContDiff : ContDiff ℝ 2 qraw := by simpa [qraw] using hq
  have hqcompact' : HasCompactSupport qraw := by simpa [qraw] using hqcompact
  have hqone : ContDiff ℝ 1 (fderiv ℝ qraw) :=
    hqContDiff.fderiv_right (m := 1) (by norm_num)
  have hfddcontinuous : Continuous (fderiv ℝ (fderiv ℝ qraw)) :=
    (hqone.fderiv_right (m := 0) (by norm_num)).continuous
  let lapraw : E → ℝ := fun y ↦ (Δ qraw) y
  have hlapcontinuous : Continuous lapraw := by
    unfold lapraw
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    apply continuous_finset_sum
    intro i _hi
    simp_rw [iteratedFDeriv_two_apply]
    exact (hfddcontinuous.clm_apply continuous_const).clm_apply continuous_const
  have hlapcompact : HasCompactSupport lapraw := by
    have hsupp : Function.support lapraw ⊆ tsupport qraw := by
      intro y hy
      by_contra hyt
      have hqzero : qraw =ᶠ[nhds y] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp hyt
      have hlapzeroAt :=
        (InnerProductSpace.laplacian_congr_nhds hqzero).eq_of_nhds
      have hzero : lapraw y = 0 := by
        simpa [lapraw] using hlapzeroAt
      exact hy hzero
    exact hqcompact'.of_isClosed_subset (isClosed_tsupport _) <|
      closure_minimal hsupp (isClosed_tsupport _)
  let lapBCF : E →ᵇ ℝ :=
    ofCompactSupport lapraw hlapcontinuous hlapcompact
  let lapq : ScalarBUC :=
    ⟨lapBCF, hlapcompact.uniformContinuous_of_continuous hlapcontinuous⟩
  refine ⟨lapq, ?_⟩
  intro y
  change lapraw y = (Δ qraw) y
  rfl

/-- The compactly supported global `C²` core has its classical one-sided
heat trace without separately assuming global derivative bounds. -/
theorem scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_compactSupport
    (q : ScalarBUC) (z : E)
    (hq : ContDiff ℝ 2 ((q : E →ᵇ ℝ) : E → ℝ))
    (hqcompact : HasCompactSupport ((q : E →ᵇ ℝ) : E → ℝ)) :
    HasDerivWithinAt (scalarBUCHeatOrbit q z)
      ((Δ ((q : E →ᵇ ℝ) : E → ℝ)) z) (Set.Ici 0) 0 := by
  rcases exists_fderiv_bound_of_contDiff_two_compactSupport
    (E := E) hq hqcompact with ⟨C₁, hC₁⟩
  rcases exists_second_fderiv_bound_of_contDiff_two_compactSupport
    (E := E) hq hqcompact with ⟨C₂, hC₂⟩
  rcases exists_scalarBUC_laplacian_of_contDiff_two_compactSupport
    (E := E) q hq hqcompact with ⟨lapq, hlapq⟩
  have htrace :=
    scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_bounded_derivatives
      (E := E) q lapq z hq hC₁ hC₂ hlapq
  simpa [hlapq z] using htrace

/-- A scalar `BUC` datum which is merely `C²` at the tested point has the
classical one-sided heat trace there.  The proof localizes by a compactly
supported smooth cutoff, applies the bounded global classical core to the
localized datum, and removes the cutoff with the Gaussian tail estimate. -/
theorem scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
    (f : ScalarBUC) (z : E)
    (hf : ContDiffAt ℝ 2 ((f : E →ᵇ ℝ) : E → ℝ) z) :
    HasDerivWithinAt (scalarBUCHeatOrbit f z)
      ((Δ ((f : E →ᵇ ℝ) : E → ℝ)) z) (Set.Ici 0) 0 := by
  rcases exists_compactlySupported_scalarBUC_eventuallyEq_of_contDiffAt_two
    (E := E) f z hf with ⟨q, hq, hqcompact, hqLocal⟩
  have hqTrace :=
    scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_compactSupport
      (E := E) q z hq hqcompact
  have htailTrace : HasDerivWithinAt
      (scalarBUCHeatOrbit (f - q) z) 0 (Set.Ici 0) 0 :=
    scalarBUCHeatOrbit_sub_hasDerivWithinAt_zero_of_eventuallyEq
      (E := E) f q z hqLocal.symm
  have hsum := hqTrace.add htailTrace
  have horbitDecomp :
      scalarBUCHeatOrbit q z + scalarBUCHeatOrbit (f - q) z =
        scalarBUCHeatOrbit f z := by
    funext t
    have hdecomp : q + (f - q) = f := by abel
    change
      ((((vectorHeatSemigroupBUCExtended (E := E) (F := ℝ) t q) +
          vectorHeatSemigroupBUCExtended (E := E) (F := ℝ) t (f - q) :
          ScalarBUC) : E →ᵇ ℝ) z) = _
    rw [← map_add, hdecomp]
    rfl
  rw [horbitDecomp] at hsum
  have hlapAt :=
    (InnerProductSpace.laplacian_congr_nhds hqLocal).eq_of_nhds
  have hlapz : (Δ ((q : E →ᵇ ℝ) : E → ℝ)) z =
      (Δ ((f : E →ᵇ ℝ) : E → ℝ)) z := by
    exact hlapAt
  rw [add_zero, hlapz] at hsum
  exact hsum

end ScalarHeatOrbit

end Poincare
