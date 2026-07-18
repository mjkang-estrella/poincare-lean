import Poincare.Global.HeatCauchyNext2

/-!
# Finite-dimensional vector-valued heat Cauchy problem

The scalar heat Cauchy theorem is enough for finite-dimensional targets.  A
Bochner-valued heat convolution is first shown to commute with every continuous
linear coordinate.  The canonical finite basis then reconstructs the vector
solution from finitely many scalar heat solutions, transferring positive-time
`C²` spatial regularity, the heat equation, and the Cauchy trace componentwise.

This is the form needed for local Ricci--DeTurck arguments: a metric tensor in
coordinates is finite-dimensional vector-valued data, while every component is
governed by the scalar Gaussian estimates.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian ContDiff

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- Bochner heat convolution of finite-dimensional vector-valued data. -/
def vectorHeatSolution (t : ℝ) (f : E → F) (x : E) : F :=
  ∫ y : E, heatKernel (E := E) t (x - y) • f y

omit [FiniteDimensional ℝ F] in
/-- A bounded strongly measurable vector field has an integrable positive-time
heat-convolution integrand. -/
theorem integrable_heatKernel_smul_vectorData
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    Integrable (fun y : E ↦ heatKernel (E := E) t (x - y) • f y) volume := by
  have hker : Integrable (fun y : E ↦ heatKernel (E := E) t (x - y)) :=
    heatKernel_integrable_sub_left (E := E) ht x
  have hmeas : AEStronglyMeasurable
      (fun y : E ↦ heatKernel (E := E) t (x - y) • f y) volume := by
    have hkcont : Continuous (fun y : E ↦ heatKernel (E := E) t (x - y)) :=
      (contDiff_heatKernel_spatial (E := E) t).continuous.comp
        (continuous_const.sub continuous_id)
    exact hkcont.aestronglyMeasurable.smul hf
  refine (hker.const_mul C).mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hk_nonneg : 0 ≤ heatKernel (E := E) t (x - y) :=
    heatKernel_nonneg (E := E) ht (x - y)
  calc
    ‖heatKernel (E := E) t (x - y) • f y‖
        = heatKernel (E := E) t (x - y) * ‖f y‖ := by
          rw [norm_smul, Real.norm_of_nonneg hk_nonneg]
    _ ≤ heatKernel (E := E) t (x - y) * C :=
      mul_le_mul_of_nonneg_left (hC y) hk_nonneg
    _ = C * heatKernel (E := E) t (x - y) := by ring

/-- Continuous linear coordinates commute with the Bochner heat convolution. -/
theorem vectorHeatSolution_apply_continuousLinearMap
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (L : F →L[ℝ] ℝ) (x : E) :
    L (vectorHeatSolution (E := E) t f x) =
      heatSolution (E := E) t (fun y ↦ L (f y)) x := by
  have hint := integrable_heatKernel_smul_vectorData (E := E) ht hf hC x
  rw [vectorHeatSolution, ← L.integral_comp_comm hint]
  rw [heatSolution_apply_swap]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro y
  simp [smul_eq_mul]

/-- The canonical finite-dimensional coordinates of the vector heat solution
are precisely the scalar heat solutions of the coordinate data. -/
theorem vectorHeatSolution_finBasis_coord
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (i : Fin (Module.finrank ℝ F)) (x : E) :
    (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) t f x) =
      heatSolution (E := E) t
        (fun y ↦ (Module.finBasis ℝ F).coord i (f y)) x := by
  exact vectorHeatSolution_apply_continuousLinearMap (E := E) ht hf hC
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)) x

/-- Finite-basis reconstruction of the vector heat convolution from scalar
heat solutions. -/
theorem vectorHeatSolution_eq_sum_finBasis
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C) :
    vectorHeatSolution (E := E) t f = fun x ↦
      ∑ i, heatSolution (E := E) t
        (fun y ↦ (Module.finBasis ℝ F).coord i (f y)) x •
          (Module.finBasis ℝ F) i := by
  funext x
  conv_lhs => rw [← (Module.finBasis ℝ F).sum_repr
    (vectorHeatSolution (E := E) t f x)]
  apply Finset.sum_congr rfl
  intro i _hi
  change (Module.finBasis ℝ F).coord i
      (vectorHeatSolution (E := E) t f x) • (Module.finBasis ℝ F) i = _
  rw [vectorHeatSolution_finBasis_coord (E := E) ht hf hC i x]

/-- Positive-time vector heat convolution is twice continuously Frechet
differentiable in the spatial variable. -/
theorem contDiff_two_vectorHeatSolution_of_bounded_measurable
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C) :
    ContDiff ℝ 2 (vectorHeatSolution (E := E) t f) := by
  rw [vectorHeatSolution_eq_sum_finBasis (E := E) ht hf hC]
  apply ContDiff.sum
  intro i _hi
  have hcoord_meas : AEStronglyMeasurable
      (fun y : E ↦ (Module.finBasis ℝ F).coord i (f y)) volume :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)).continuous
      |>.comp_aestronglyMeasurable hf
  have hcoord_bound : ∀ y : E,
      ‖(Module.finBasis ℝ F).coord i (f y)‖ ≤
        ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)‖ * C := by
    intro y
    change ‖(LinearMap.toContinuousLinearMap
      ((Module.finBasis ℝ F).coord i)) (f y)‖ ≤ _
    calc
      ‖(LinearMap.toContinuousLinearMap
          ((Module.finBasis ℝ F).coord i)) (f y)‖ ≤
          ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)‖ * ‖f y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)‖ * C :=
        mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
  exact (contDiff_two_heatSolution_of_bounded_measurable
    (E := E) ht hcoord_meas hcoord_bound).smul_const ((Module.finBasis ℝ F) i)

/-- Every finite-basis component of the vector heat convolution satisfies the
positive-time heat equation. -/
theorem vectorHeatSolution_finBasis_coord_solves_heatEquation
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (i : Fin (Module.finrank ℝ F)) (x : E) :
    deriv (fun τ : ℝ ↦
      (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) τ f x)) t =
      (Δ fun z : E ↦
        (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) t f z)) x := by
  let L : F →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)
  have hcoord_meas : AEStronglyMeasurable (fun y : E ↦ L (f y)) volume :=
    L.continuous.comp_aestronglyMeasurable hf
  have hcoord_bound : ∀ y : E, ‖L (f y)‖ ≤ ‖L‖ * C := by
    intro y
    exact (ContinuousLinearMap.le_opNorm L (f y)).trans
      (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg L))
  have htime : Filter.EventuallyEq (nhds t)
      (fun τ : ℝ ↦ L (vectorHeatSolution (E := E) τ f x))
      (fun τ : ℝ ↦ heatSolution (E := E) τ (fun y ↦ L (f y)) x) := by
    filter_upwards [eventually_gt_nhds ht] with τ hτ
    exact vectorHeatSolution_apply_continuousLinearMap (E := E) hτ hf hC L x
  have hspace :
      (fun z : E ↦ L (vectorHeatSolution (E := E) t f z)) =
        heatSolution (E := E) t (fun y ↦ L (f y)) := by
    funext z
    exact vectorHeatSolution_apply_continuousLinearMap (E := E) ht hf hC L z
  change deriv (fun τ : ℝ ↦ L (vectorHeatSolution (E := E) τ f x)) t =
    (Δ fun z : E ↦ L (vectorHeatSolution (E := E) t f z)) x
  rw [Filter.EventuallyEq.deriv_eq htime, hspace]
  exact heatSolution_solves_heatEquation_of_bounded_measurable
    (E := E) ht hcoord_meas hcoord_bound x

/-- Componentwise finite-dimensional Cauchy problem for integrable bounded data.
The conclusion contains both the positive-time heat equation and recovery of
the initial vector coordinate at every continuity point. -/
theorem vectorHeatSolution_finBasis_coord_model_cauchy_problem
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : Integrable f) (hC : ∀ y, ‖f y‖ ≤ C)
    {x : E} (hcf : ContinuousAt f x)
    (i : Fin (Module.finrank ℝ F)) :
    deriv (fun τ : ℝ ↦
      (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) τ f x)) t =
        (Δ fun z : E ↦
          (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) t f z)) x ∧
      Tendsto (fun τ : ℝ ↦
        (Module.finBasis ℝ F).coord i (vectorHeatSolution (E := E) τ f x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((Module.finBasis ℝ F).coord i (f x))) := by
  let L : F →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)
  have hcoord_int : Integrable (fun y : E ↦ L (f y)) :=
    L.integrable_comp hf
  have hcoord_bound : ∀ y : E, ‖L (f y)‖ ≤ ‖L‖ * C := by
    intro y
    exact (ContinuousLinearMap.le_opNorm L (f y)).trans
      (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg L))
  have hcoord_cont : ContinuousAt (fun y : E ↦ L (f y)) x :=
    L.continuous.continuousAt.comp hcf
  have hscalar := heatSolution_model_cauchy_problem
    (E := E) ht hcoord_int hcoord_bound hcoord_cont
  have hpde := vectorHeatSolution_finBasis_coord_solves_heatEquation
    (E := E) ht hf.aestronglyMeasurable hC i x
  refine ⟨hpde, ?_⟩
  apply hscalar.2.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (vectorHeatSolution_apply_continuousLinearMap
    (E := E) hτ hf.aestronglyMeasurable hC L x).symm

/-- The componentwise Cauchy traces reconstruct convergence in the actual
finite-dimensional target norm. -/
theorem vectorHeatSolution_tendsto_zero_of_integrable_bounded
    {f : E → F} (hf : Integrable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    {x : E} (hcf : ContinuousAt f x) :
    Tendsto (fun τ : ℝ ↦ vectorHeatSolution (E := E) τ f x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)) := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have hcoords : Tendsto
      (fun τ : ℝ ↦ e (vectorHeatSolution (E := E) τ f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (e (f x))) := by
    rw [tendsto_pi_nhds]
    intro i
    have hi := (vectorHeatSolution_finBasis_coord_model_cauchy_problem
      (E := E) (F := F) (t := 1) (C := C) (by norm_num) hf hC hcf i).2
    simpa [e, Module.Basis.equivFun_apply, Module.Basis.coord_apply] using hi
  have hback := e.symm.continuous.continuousAt.tendsto.comp hcoords
  simpa [Function.comp_def] using hback

/-- At positive time the finite-dimensional vector heat convolution is
differentiable as a target-valued function of time. -/
theorem vectorHeatSolution_time_differentiableAt
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    DifferentiableAt ℝ (fun τ : ℝ ↦ vectorHeatSolution (E := E) τ f x) t := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have hcoord (i : Fin (Module.finrank ℝ F)) : DifferentiableAt ℝ
      (fun τ : ℝ ↦ e (vectorHeatSolution (E := E) τ f x) i) t := by
    let L : F →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord i)
    have hcoord_meas : AEStronglyMeasurable (fun y : E ↦ L (f y)) volume :=
      L.continuous.comp_aestronglyMeasurable hf
    have hcoord_bound : ∀ y : E, ‖L (f y)‖ ≤ ‖L‖ * C := by
      intro y
      exact (ContinuousLinearMap.le_opNorm L (f y)).trans
        (mul_le_mul_of_nonneg_left (hC y) (norm_nonneg L))
    have hs := heatKernel_time_deriv_integral_hasDerivAt
      (E := E) ht hcoord_meas hcoord_bound x
    have heq : Filter.EventuallyEq (nhds t)
        (fun τ : ℝ ↦ e (vectorHeatSolution (E := E) τ f x) i)
        (fun τ : ℝ ↦ ∫ y : E,
          heatKernel (E := E) τ (x - y) * L (f y)) := by
      filter_upwards [eventually_gt_nhds ht] with τ hτ
      calc
        e (vectorHeatSolution (E := E) τ f x) i =
            L (vectorHeatSolution (E := E) τ f x) := by
          simp [e, L, Module.Basis.equivFun_apply, Module.Basis.coord_apply]
        _ = heatSolution (E := E) τ (fun y ↦ L (f y)) x :=
          vectorHeatSolution_apply_continuousLinearMap (E := E) hτ hf hC L x
        _ = ∫ y : E, heatKernel (E := E) τ (x - y) * L (f y) :=
          heatSolution_apply_swap (E := E) τ (fun y ↦ L (f y)) x
    exact (hs.congr_of_eventuallyEq heq).differentiableAt
  have hediff : DifferentiableAt ℝ
      (fun τ : ℝ ↦ e (vectorHeatSolution (E := E) τ f x)) t :=
    differentiableAt_pi.mpr hcoord
  have hback := e.symm.differentiableAt.comp t hediff
  simpa [Function.comp_def] using hback

/-- Coordinate-free positive-time heat equation for finite-dimensional
vector-valued bounded measurable data. -/
theorem vectorHeatSolution_solves_heatEquation_of_bounded_measurable
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    deriv (fun τ : ℝ ↦ vectorHeatSolution (E := E) τ f x) t =
      (Δ fun z : E ↦ vectorHeatSolution (E := E) t f z) x := by
  let b := Module.finBasis ℝ F
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    b.equivFun.toContinuousLinearEquiv
  let Utime : ℝ → F := fun τ ↦ vectorHeatSolution (E := E) τ f x
  let Uspace : E → F := vectorHeatSolution (E := E) t f
  have htime : DifferentiableAt ℝ Utime t := by
    simpa [Utime] using vectorHeatSolution_time_differentiableAt
      (E := E) (F := F) ht hf hC x
  have hspace : ContDiff ℝ 2 Uspace := by
    simpa [Uspace] using contDiff_two_vectorHeatSolution_of_bounded_measurable
      (E := E) (F := F) ht hf hC
  apply e.injective
  funext i
  let L : F →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (b.coord i)
  have htime_coord : HasDerivAt (fun τ : ℝ ↦ L (Utime τ))
      (L (deriv Utime t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t htime.hasDerivAt
  have hspace_coord :
      (Δ (L ∘ Uspace)) x = L ((Δ Uspace) x) := by
    simpa [Function.comp_def] using
      hspace.contDiffAt.laplacian_CLM_comp_left (l := L)
  change L (deriv Utime t) = L ((Δ Uspace) x)
  rw [← htime_coord.deriv, ← hspace_coord]
  simpa [L, b, Utime, Uspace, Function.comp_def] using
    vectorHeatSolution_finBasis_coord_solves_heatEquation
      (E := E) (F := F) ht hf hC i x

end Measurable

end Poincare
