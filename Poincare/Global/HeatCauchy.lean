import Poincare.Global.HeatApproxIdentity
import Poincare.Global.HeatKernelPDEn
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Heat-kernel Cauchy problem interface

This file records the verified interface needed to pass from the certified
heat kernel to the model linear Cauchy problem.

The full theorem for bounded continuous initial data needs two analytic
interchange lemmas that are not yet available in this repository:

* differentiating `τ ↦ ∫ y, heatKernel τ (x - y) * f y` under the integral;
* moving the spatial Laplacian through the same convolution integral.

We keep those as explicit hypotheses in the packaged theorem below, prove the
kernel-side translation needed to combine them, and isolate the basic
bounded-data Gaussian domination already available from the existing kernel
integrability API.
-/

noncomputable section

open MeasureTheory Filter
open scoped Convolution Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- A positive-time heat kernel remains integrable after the translation `y ↦ x - y`. -/
theorem heatKernel_integrable_sub_left {t : ℝ} (ht : 0 < t) (x : E) :
    Integrable (fun y : E => heatKernel (E := E) t (x - y)) := by
  exact (heatKernel_integrable (E := E) ht).comp_sub_left x

/--
Basic bounded-data domination for the heat-kernel convolution integrand in
the symmetric `x - y` form.

This is the verified domination seed: bounded measurable data are dominated by
the translated heat kernel, and the translated heat kernel is integrable.
-/
theorem heatKernel_bounded_data_domination {t : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (x : E) :
    (∀ y : E, ‖heatKernel (E := E) t (x - y) * f y‖ ≤
        C * heatKernel (E := E) t (x - y)) ∧
      Integrable (fun y : E => C * heatKernel (E := E) t (x - y)) ∧
      Integrable (fun y : E => heatKernel (E := E) t (x - y) * f y) := by
  have hker : Integrable (fun y : E => heatKernel (E := E) t (x - y)) :=
    heatKernel_integrable_sub_left (E := E) ht x
  have hf_top : MemLp f ⊤ (volume : Measure E) := by
    exact memLp_top_of_bound hf C (Filter.Eventually.of_forall hC)
  refine ⟨?_, hker.const_mul C, ?_⟩
  · intro y
    have hk_nonneg : 0 ≤ heatKernel (E := E) t (x - y) :=
      heatKernel_nonneg (E := E) ht (x - y)
    calc
      ‖heatKernel (E := E) t (x - y) * f y‖ =
          ‖heatKernel (E := E) t (x - y)‖ * ‖f y‖ := norm_mul _ _
      _ = heatKernel (E := E) t (x - y) * ‖f y‖ := by
          rw [Real.norm_of_nonneg hk_nonneg]
      _ ≤ heatKernel (E := E) t (x - y) * C :=
          mul_le_mul_of_nonneg_left (hC y) hk_nonneg
      _ = C * heatKernel (E := E) t (x - y) := by ring
  · simpa [smul_eq_mul] using hker.smul_of_top_left hf_top

end Measurable

/-- The Laplacian of a spatial translate is the translated Laplacian. -/
theorem laplacian_heatKernel_sub_left (t : ℝ) (x y : E) :
    (Δ fun z : E => heatKernel (E := E) t (z - y)) x =
      (Δ fun z : E => heatKernel (E := E) t z) (x - y) := by
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_sub]

/-- The kernel heat equation after translating the spatial variable by `y`. -/
theorem heatKernel_sub_left_heatEquation_laplacian {t : ℝ} (ht : 0 < t) (x y : E) :
    deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t =
      (Δ fun z : E => heatKernel (E := E) t (z - y)) x := by
  rw [heatKernel_heatEquation_laplacian (E := E) ht (x - y)]
  exact (laplacian_heatKernel_sub_left (E := E) t x y).symm

section Cauchy

variable [MeasurableSpace E] [BorelSpace E]

/--
Time differentiation under the heat convolution, expressed as a `deriv`
equality once the corresponding parametric integral `HasDerivAt` fact is
available.
-/
theorem deriv_heatSolution_eq_integral_of_hasDerivAt_integral {t : ℝ} {f : E → ℝ} {x : E}
    (hderiv :
      HasDerivAt
        (fun τ : ℝ => ∫ y : E, heatKernel (E := E) τ (x - y) * f y)
        (∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) t) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
      ∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y := by
  have hfun :
      (fun τ : ℝ => heatSolution (E := E) τ f x) =
        fun τ : ℝ => ∫ y : E, heatKernel (E := E) τ (x - y) * f y := by
    funext τ
    exact heatSolution_apply_swap (E := E) τ f x
  rw [hfun]
  exact hderiv.deriv

/--
Spatial Laplacian under the heat convolution, converted to the time-derivative
integrand using the translated kernel heat equation.
-/
theorem laplacian_heatSolution_eq_integral_deriv_of_spatial_interchange {t : ℝ} (ht : 0 < t)
    (f : E → ℝ) (x : E)
    (hlap :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) :
    (Δ fun z : E => heatSolution (E := E) t f z) x =
      ∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y := by
  rw [hlap]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro y
  change (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y =
    deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y
  rw [← heatKernel_sub_left_heatEquation_laplacian (E := E) ht x y]

/--
Conditional heat-equation theorem for the heat convolution.

The two hypotheses are exactly the missing analytic interchange results:
time differentiation under the integral and spatial Laplacian under the
integral.  Once those are supplied, the certified kernel PDE proves the model
heat equation for `heatSolution`.
-/
theorem heatSolution_solves_heatEquation_of_differentiation_under_integral {t : ℝ}
    (ht : 0 < t) {f : E → ℝ} {x : E}
    (htime :
      HasDerivAt
        (fun τ : ℝ => ∫ y : E, heatKernel (E := E) τ (x - y) * f y)
        (∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) t)
    (hlap :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
      (Δ fun z : E => heatSolution (E := E) t f z) x := by
  rw [deriv_heatSolution_eq_integral_of_hasDerivAt_integral (E := E) htime]
  exact (laplacian_heatSolution_eq_integral_deriv_of_spatial_interchange
    (E := E) ht f x hlap).symm

/--
Packaged conditional model Cauchy theorem: positive-time heat equation plus
the already-proved recovery of continuous integrable initial data as `t → 0+`.
-/
theorem heatSolution_model_cauchy_problem_of_differentiation_under_integral {t : ℝ}
    (ht : 0 < t) {f : E → ℝ} (hf : Integrable f) {x : E} (hcf : ContinuousAt f x)
    (htime :
      HasDerivAt
        (fun τ : ℝ => ∫ y : E, heatKernel (E := E) τ (x - y) * f y)
        (∫ y : E, deriv (fun τ : ℝ => heatKernel (E := E) τ (x - y)) t * f y) t)
    (hlap :
      (Δ fun z : E => heatSolution (E := E) t f z) x =
        ∫ y : E, (Δ fun z : E => heatKernel (E := E) t (z - y)) x * f y) :
    deriv (fun τ : ℝ => heatSolution (E := E) τ f x) t =
        (Δ fun z : E => heatSolution (E := E) t f z) x ∧
      Tendsto (fun τ : ℝ => heatSolution (E := E) τ f x)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  exact ⟨heatSolution_solves_heatEquation_of_differentiation_under_integral
      (E := E) ht htime hlap,
    tendsto_heatSolution_nhdsGT_zero (E := E) hf hcf⟩

end Cauchy

end Poincare
