import Poincare.Global.HeatRegularizedPicard
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Bounded uniformly continuous spatial heat space

`C_b(E,F)` is too large for strong continuity of the heat semigroup at zero.
This module defines its closed subspace of uniformly continuous functions and
proves that positive-time heat convolution preserves that subspace.  It also
reduces strong continuity for Lipschitz data to the scalar first Gaussian
moment, isolating a single explicit analytic estimate.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Uniformly continuous elements of `C_b(E,F)` form a linear subspace. -/
def boundedUniformContinuousSubmodule : Submodule ℝ (E →ᵇ F) where
  carrier := {f | UniformContinuous (f : E → F)}
  zero_mem' := uniformContinuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c _f hf := hf.const_smul c

/-- Bounded uniformly continuous Banach-valued functions. -/
abbrev BoundedUniformContinuousFunction :=
  boundedUniformContinuousSubmodule (E := E) (F := F)

/-- The uniformly continuous subspace is closed in the uniform norm. -/
theorem isClosed_boundedUniformContinuousSubmodule :
    IsClosed (boundedUniformContinuousSubmodule (E := E) (F := F) : Set (E →ᵇ F)) := by
  apply IsSeqClosed.isClosed
  intro fseq f hseq hlim
  have hunif : TendstoUniformly (fun n ↦ (fseq n : E → F)) (f : E → F) atTop :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp hlim
  exact hunif.uniformContinuous (Frequently.of_forall hseq)

/-- `BUC(E,F)` is complete for complete `F`. -/
noncomputable instance boundedUniformContinuousFunction_completeSpace
    [CompleteSpace F] : CompleteSpace (BoundedUniformContinuousFunction (E := E) (F := F)) :=
  isClosed_boundedUniformContinuousSubmodule (E := E) (F := F) |>.completeSpace_coe

/-- Alternate convolution formula with the Gaussian centered at zero and the
data translated by `x`. -/
theorem vectorHeatSolution_apply_data_translate
    {t : ℝ} (f : E → F) (x : E) :
    vectorHeatSolution (E := E) t f x =
      ∫ y : E, heatKernel (E := E) t y • f (x - y) := by
  rw [vectorHeatSolution]
  have h := integral_sub_left_eq_self
    (fun y : E ↦ heatKernel (E := E) t y • f (x - y)) volume x
  simpa using h

/-- The translated-data heat integrand is integrable for bounded continuous
data. -/
theorem integrable_heatKernel_smul_bcf_translate
    {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) (x : E) :
    Integrable (fun y : E ↦ heatKernel (E := E) t y • f (x - y)) volume := by
  have hker := heatKernel_integrable (E := E) ht
  have hshift_meas : AEStronglyMeasurable (fun y : E ↦ f (x - y)) volume :=
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hshift_top : MemLp (fun y : E ↦ f (x - y)) ⊤ volume :=
    memLp_top_of_bound hshift_meas ‖f‖
      (Filter.Eventually.of_forall fun y ↦
        BoundedContinuousFunction.norm_coe_le_norm f (x - y))
  exact hker.smul_of_top_left hshift_top

/-- Positive-time heat convolution preserves uniform continuity. -/
theorem uniformContinuous_vectorHeatSolution_bcf
    {t : ℝ} (ht : 0 < t) (f : E →ᵇ F)
    (hf : UniformContinuous (f : E → F)) :
    UniformContinuous (vectorHeatSolution (E := E) t f) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  rcases Metric.uniformContinuous_iff.mp hf (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hmod⟩
  refine ⟨δ, hδ, ?_⟩
  intro x x' hxx
  rw [dist_eq_norm, vectorHeatSolution_apply_data_translate,
    vectorHeatSolution_apply_data_translate]
  have hxint := integrable_heatKernel_smul_bcf_translate (E := E) ht f x
  have hx'int := integrable_heatKernel_smul_bcf_translate (E := E) ht f x'
  rw [← integral_sub hxint hx'int]
  let bound : E → ℝ := fun y ↦ (ε / 2) * heatKernel (E := E) t y
  have hbound_int : Integrable bound volume :=
    (heatKernel_integrable (E := E) ht).const_mul (ε / 2)
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hbound_int
    (Filter.Eventually.of_forall fun y ↦ by
      have hk_nonneg : 0 ≤ heatKernel (E := E) t y :=
        heatKernel_nonneg (E := E) ht y
      have hxy : ‖f (x - y) - f (x' - y)‖ < ε / 2 := by
        rw [← dist_eq_norm]
        apply hmod
        simpa [dist_eq_norm] using hxx
      calc
        ‖heatKernel (E := E) t y • f (x - y) -
            heatKernel (E := E) t y • f (x' - y)‖ =
            heatKernel (E := E) t y * ‖f (x - y) - f (x' - y)‖ := by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg hk_nonneg]
        _ ≤ heatKernel (E := E) t y * (ε / 2) :=
          mul_le_mul_of_nonneg_left hxy.le hk_nonneg
        _ = bound y := by simp [bound, mul_comm])
  calc
    ‖∫ y : E, heatKernel (E := E) t y • f (x - y) -
        heatKernel (E := E) t y • f (x' - y)‖
        ≤ ∫ y : E, bound y := hnorm
    _ = (ε / 2) * (∫ y : E, heatKernel (E := E) t y) := by
      simp [bound, integral_const_mul]
    _ = ε / 2 := by rw [integral_heatKernel_eq_one (E := E) ht, mul_one]
    _ < ε := half_lt_self hε

/-- The heat operator on `C_b` restricts to the complete `BUC` subspace. -/
def vectorHeatSemigroupBUC {t : ℝ} (ht : 0 < t) :
    BoundedUniformContinuousFunction (E := E) (F := F) →
      BoundedUniformContinuousFunction (E := E) (F := F) :=
  fun f ↦ ⟨vectorHeatSemigroupCLM (E := E) (F := F) ht (f : E →ᵇ F),
    uniformContinuous_vectorHeatSolution_bcf (E := E) ht (f : E →ᵇ F) f.property⟩

/-- Scalar first moment of the positive-time heat kernel. -/
def heatKernelFirstMoment (t : ℝ) : ℝ :=
  ∫ y : E, ‖y‖ * heatKernel (E := E) t y

/-- Parabolic scaling of the heat kernel.  This form, with time `a²`, avoids
any choice of square root and is the convenient input to Haar scaling. -/
theorem heatKernel_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    heatKernel (E := E) (a ^ 2) (a • x) =
      (a ^ Module.finrank ℝ E)⁻¹ * heatKernel (E := E) 1 x := by
  unfold heatKernel
  have hfourpi : 0 ≤ 4 * Real.pi := by positivity
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  rw [show 4 * Real.pi * a ^ 2 = (4 * Real.pi) * (a ^ 2) by ring,
    Real.mul_rpow hfourpi ha2]
  have hscale :
      (a ^ 2 : ℝ) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
        (a ^ Module.finrank ℝ E)⁻¹ := by
    rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
    ring_nf
    rw [Real.rpow_neg ha.le, Real.rpow_natCast]
    exact (inv_pow a (Module.finrank ℝ E)).symm
  rw [hscale, norm_smul, Real.norm_of_nonneg ha.le]
  have hexponent : -(a * ‖x‖) ^ 2 / (4 * a ^ 2) = -(‖x‖ ^ 2) / 4 := by
    field_simp [ha.ne']
  rw [hexponent]
  ring

/-- The first heat-kernel moment has exactly parabolic order one. -/
theorem heatKernelFirstMoment_sq (a : ℝ) (ha : 0 < a) :
    heatKernelFirstMoment (E := E) (a ^ 2) =
      a * heatKernelFirstMoment (E := E) 1 := by
  let p : ℝ := a ^ Module.finrank ℝ E
  have hp : 0 < p := pow_pos ha _
  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E ↦ ‖y‖ * heatKernel (E := E) (a ^ 2) y) a (hR := ha.le)
  have hleft :
      (∫ x : E, ‖a • x‖ * heatKernel (E := E) (a ^ 2) (a • x)) =
        (a * p⁻¹) * heatKernelFirstMoment (E := E) 1 := by
    rw [show (fun x : E ↦ ‖a • x‖ * heatKernel (E := E) (a ^ 2) (a • x)) =
        fun x : E ↦ (a * p⁻¹) * (‖x‖ * heatKernel (E := E) 1 x) by
      funext x
      rw [norm_smul, Real.norm_of_nonneg ha.le,
        heatKernel_sq_smul (E := E) a ha x]
      simp only [p]
      ring]
    rw [integral_const_mul]
    rfl
  apply mul_left_cancel₀ (inv_ne_zero hp.ne')
  calc
    p⁻¹ * heatKernelFirstMoment (E := E) (a ^ 2) =
        ∫ x : E, ‖a • x‖ * heatKernel (E := E) (a ^ 2) (a • x) := by
      simpa [heatKernelFirstMoment, p, smul_eq_mul] using hchange.symm
    _ = (a * p⁻¹) * heatKernelFirstMoment (E := E) 1 := hleft
    _ = p⁻¹ * (a * heatKernelFirstMoment (E := E) 1) := by ring

/-- Square-root form of the first-moment scaling law. -/
theorem heatKernelFirstMoment_eq_sqrt {t : ℝ} (ht : 0 < t) :
    heatKernelFirstMoment (E := E) t =
      Real.sqrt t * heatKernelFirstMoment (E := E) 1 := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h := heatKernelFirstMoment_sq (E := E) (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt ht.le] at h
  exact h

/-- Lipschitz data converge uniformly under the heat semigroup, with error
controlled by the first Gaussian moment. -/
theorem norm_vectorHeatSemigroup_sub_le_lipschitz_firstMoment
    {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) (K : NNReal)
    (hf : LipschitzWith K (f : E → F)) :
    ‖vectorHeatSolutionBCF (E := E) ht f - f‖ ≤
      (K : ℝ) * heatKernelFirstMoment (E := E) t := by
  apply (BoundedContinuousFunction.norm_le
    (f := vectorHeatSolutionBCF (E := E) ht f - f)
    (mul_nonneg K.property (by
      exact integral_nonneg fun y ↦ mul_nonneg (norm_nonneg y)
        (heatKernel_nonneg (E := E) ht y)))).mpr
  intro x
  rw [BoundedContinuousFunction.sub_apply, vectorHeatSolutionBCF_apply,
    vectorHeatSolution_apply_data_translate]
  have hmass := integral_heatKernel_eq_one (E := E) ht
  have hfconst : Integrable (fun y : E ↦ heatKernel (E := E) t y • f x) :=
    (heatKernel_integrable (E := E) ht).smul_const (f x)
  have hfx : f x = ∫ y : E, heatKernel (E := E) t y • f x := by
    rw [integral_smul_const, hmass, one_smul]
  rw [hfx]
  have hmain := integrable_heatKernel_smul_bcf_translate (E := E) ht f x
  rw [← integral_sub hmain hfconst]
  let bound : E → ℝ := fun y ↦
    (K : ℝ) * (‖y‖ * heatKernel (E := E) t y)
  have hmoment_int : Integrable (fun y : E ↦
      ‖y‖ * heatKernel (E := E) t y) := by
    have henv := integrable_one_add_norm_sq_mul_heatKernel_sub_left
      (E := E) ht 0
    have hmeas : AEStronglyMeasurable
        (fun y : E ↦ ‖y‖ * heatKernel (E := E) t y) volume := by
      exact (continuous_norm.mul
        (contDiff_heatKernel_spatial (E := E) t).continuous).aestronglyMeasurable
    refine henv.mono' hmeas ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    have hk := heatKernel_nonneg (E := E) ht y
    have hkeven : heatKernel (E := E) t (-y) = heatKernel (E := E) t y := by
      simp [heatKernel]
    rw [zero_sub, hkeven]
    calc
      ‖‖y‖ * heatKernel (E := E) t y‖ = ‖y‖ * heatKernel (E := E) t y := by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg y) hk)]
      _ ≤ (1 + ‖y‖ ^ 2) * heatKernel (E := E) t y := by
        gcongr
        nlinarith [sq_nonneg (‖y‖ - 1)]
  have hbound_int : Integrable bound := hmoment_int.const_mul (K : ℝ)
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hbound_int
    (Filter.Eventually.of_forall fun y ↦ by
      have hk_nonneg := heatKernel_nonneg (E := E) ht y
      have hlip : ‖f (x - y) - f x‖ ≤ (K : ℝ) * ‖y‖ := by
        rw [← dist_eq_norm]
        have := hf.dist_le_mul (x - y) x
        simpa [dist_eq_norm] using this
      calc
        ‖heatKernel (E := E) t y • f (x - y) -
            heatKernel (E := E) t y • f x‖ =
            heatKernel (E := E) t y * ‖f (x - y) - f x‖ := by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg hk_nonneg]
        _ ≤ heatKernel (E := E) t y * ((K : ℝ) * ‖y‖) :=
          mul_le_mul_of_nonneg_left hlip hk_nonneg
        _ = bound y := by simp [bound]; ring)
  calc
    ‖∫ y : E, heatKernel (E := E) t y • f (x - y) -
        heatKernel (E := E) t y • f x‖
        ≤ ∫ y : E, bound y := hnorm
    _ = (K : ℝ) * heatKernelFirstMoment (E := E) t := by
      simp [bound, heatKernelFirstMoment, integral_const_mul]

/-- The sole remaining scalar estimate for strong continuity on the Lipschitz
subclass. -/
def HeatKernelFirstMomentTendsToZero : Prop :=
  Tendsto (fun t : ℝ ↦ heatKernelFirstMoment (E := E) t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- The first Gaussian moment vanishes at zero positive time. -/
theorem heatKernelFirstMoment_tendsto_zero :
    HeatKernelFirstMomentTendsToZero (E := E) := by
  have hsqrt : Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hfull : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds (Real.sqrt 0)) :=
      Real.continuous_sqrt.continuousAt.tendsto
    simpa using hfull.mono_left inf_le_left
  have hscaled := hsqrt.mul_const (heatKernelFirstMoment (E := E) 1)
  have heq :
      (fun t : ℝ ↦ Real.sqrt t * heatKernelFirstMoment (E := E) 1) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
        (fun t : ℝ ↦ heatKernelFirstMoment (E := E) t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heatKernelFirstMoment_eq_sqrt (E := E) (Set.mem_Ioi.mp ht)).symm
  simpa [HeatKernelFirstMomentTendsToZero] using hscaled.congr' heq

/-- Lipschitz data converge to their initial value in the uniform norm.  The
piecewise definition merely gives the expression a value away from the
positive-time filter on which the assertion lives. -/
theorem tendsto_norm_vectorHeatSemigroup_sub_of_lipschitz
    (f : E →ᵇ F) (K : NNReal) (hf : LipschitzWith K (f : E → F)) :
    Tendsto
      (fun t : ℝ ↦ if ht : 0 < t then
        ‖vectorHeatSemigroupCLM (E := E) (F := F) ht f - f‖ else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ by
      split_ifs
      · positivity
      · exact le_rfl
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [dif_pos (Set.mem_Ioi.mp ht)]
    exact norm_vectorHeatSemigroup_sub_le_lipschitz_firstMoment
      (E := E) (F := F) (Set.mem_Ioi.mp ht) f K hf
  · have h := (heatKernelFirstMoment_tendsto_zero (E := E)).const_mul (K : ℝ)
    simpa [HeatKernelFirstMomentTendsToZero] using h

/-- The abstract zero-time Duhamel frontier is discharged whenever the
nonlinearity takes values in the Lipschitz subclass. -/
theorem heatSemigroupStrongContinuityAtZeroOn_of_lipschitz
    (N : (E →ᵇ F) → (E →ᵇ F))
    (hNlip : ∀ z : E →ᵇ F, ∃ K : NNReal,
      LipschitzWith K (N z : E → F)) :
    HeatSemigroupStrongContinuityAtZeroOn (E := E) (F := F) N := by
  intro z η hη
  rcases hNlip z with ⟨K, hK⟩
  have htend := tendsto_norm_vectorHeatSemigroup_sub_of_lipschitz
    (E := E) (F := F) (N z) K hK
  rw [Metric.tendsto_nhdsWithin_nhds] at htend
  rcases htend η hη with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have h := hclose (Set.mem_Ioi.mpr ht) (by
    simpa [Real.dist_eq, abs_of_pos ht] using htδ)
  simpa [dif_pos ht, Real.dist_eq] using h

end Poincare
