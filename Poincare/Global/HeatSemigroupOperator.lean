import Poincare.Global.DuhamelContraction
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Positive-time vector heat operator on bounded continuous fields

The finite-dimensional vector heat convolution is bundled here as a continuous
linear operator on `C_b(E,F)`.  Positivity and unit mass of the Gaussian show
that its operator norm is at most one.  This is the spatial Banach-space
propagator needed by the Duhamel contraction package.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The translated positive-time heat kernel still has total mass one. -/
theorem integral_heatKernel_sub_left_eq_one {t : ℝ} (ht : 0 < t) (x : E) :
    ∫ y : E, heatKernel (E := E) t (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun y : E ↦ heatKernel (E := E) t y) volume x]
  exact integral_heatKernel_eq_one (E := E) ht

omit [FiniteDimensional ℝ F] in
/-- Positive-time vector heat convolution does not increase the uniform norm
of bounded continuous data. -/
theorem norm_vectorHeatSolution_le_bcf
    {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) (x : E) :
    ‖vectorHeatSolution (E := E) t f x‖ ≤ ‖f‖ := by
  have hker : Integrable (fun y : E ↦ heatKernel (E := E) t (x - y)) :=
    heatKernel_integrable_sub_left (E := E) ht x
  have hbound_int : Integrable
      (fun y : E ↦ ‖f‖ * heatKernel (E := E) t (x - y)) :=
    hker.const_mul ‖f‖
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hbound_int
    (Filter.Eventually.of_forall fun y ↦ by
      have hk_nonneg : 0 ≤ heatKernel (E := E) t (x - y) :=
        heatKernel_nonneg (E := E) ht (x - y)
      calc
        ‖heatKernel (E := E) t (x - y) • f y‖ =
            heatKernel (E := E) t (x - y) * ‖f y‖ := by
          rw [norm_smul, Real.norm_of_nonneg hk_nonneg]
        _ ≤ heatKernel (E := E) t (x - y) * ‖f‖ :=
          mul_le_mul_of_nonneg_left
            (BoundedContinuousFunction.norm_coe_le_norm f y) hk_nonneg
        _ = ‖f‖ * heatKernel (E := E) t (x - y) := by ring)
  rw [vectorHeatSolution]
  calc
    ‖∫ y : E, heatKernel (E := E) t (x - y) • f y‖
        ≤ ∫ y : E, ‖f‖ * heatKernel (E := E) t (x - y) := hnorm
    _ = ‖f‖ * (∫ y : E, heatKernel (E := E) t (x - y)) := by
      rw [integral_const_mul]
    _ = ‖f‖ := by rw [integral_heatKernel_sub_left_eq_one (E := E) ht x, mul_one]

/-- Positive-time vector heat convolution as a bounded continuous spatial
field. -/
def vectorHeatSolutionBCF {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (vectorHeatSolution (E := E) t f)
    (contDiff_two_vectorHeatSolution_of_bounded_measurable
      (E := E) (F := F) ht f.continuous.aestronglyMeasurable
        (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm f y)).continuous
    ‖f‖
    (norm_vectorHeatSolution_le_bcf (E := E) ht f)

@[simp]
theorem vectorHeatSolutionBCF_apply {t : ℝ} (ht : 0 < t)
    (f : E →ᵇ F) (x : E) :
    vectorHeatSolutionBCF (E := E) ht f x = vectorHeatSolution (E := E) t f x :=
  rfl

/-- The bundled positive-time heat operator is norm-nonexpanding. -/
theorem norm_vectorHeatSolutionBCF_le {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) :
    ‖vectorHeatSolutionBCF (E := E) ht f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    _ (norm_nonneg f) (norm_vectorHeatSolution_le_bcf (E := E) ht f)

/-- Additivity of the positive-time vector heat operator. -/
theorem vectorHeatSolutionBCF_add {t : ℝ} (ht : 0 < t) (f g : E →ᵇ F) :
    vectorHeatSolutionBCF (E := E) ht (f + g) =
      vectorHeatSolutionBCF (E := E) ht f + vectorHeatSolutionBCF (E := E) ht g := by
  ext x
  simp only [vectorHeatSolutionBCF_apply, BoundedContinuousFunction.add_apply]
  rw [vectorHeatSolution]
  have hf := integrable_heatKernel_smul_vectorData (E := E) ht
    f.continuous.aestronglyMeasurable
    (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm f y) x
  have hg := integrable_heatKernel_smul_vectorData (E := E) ht
    g.continuous.aestronglyMeasurable
    (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm g y) x
  simp_rw [BoundedContinuousFunction.add_apply, smul_add]
  exact integral_add hf hg

/-- Homogeneity of the positive-time vector heat operator. -/
theorem vectorHeatSolutionBCF_smul {t : ℝ} (ht : 0 < t)
    (c : ℝ) (f : E →ᵇ F) :
    vectorHeatSolutionBCF (E := E) ht (c • f) =
      c • vectorHeatSolutionBCF (E := E) ht f := by
  ext x
  simp only [vectorHeatSolutionBCF_apply, BoundedContinuousFunction.smul_apply]
  rw [vectorHeatSolution]
  rw [vectorHeatSolution]
  rw [← integral_smul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro y
  simp only [BoundedContinuousFunction.smul_apply]
  rw [smul_smul, smul_smul, mul_comm c]

/-- The positive-time vector heat convolution as a linear map on `C_b(E,F)`. -/
def vectorHeatSemigroupLinearMap {t : ℝ} (ht : 0 < t) :
    (E →ᵇ F) →ₗ[ℝ] (E →ᵇ F) where
  toFun := vectorHeatSolutionBCF (E := E) ht
  map_add' := vectorHeatSolutionBCF_add (E := E) ht
  map_smul' := vectorHeatSolutionBCF_smul (E := E) ht

/-- The positive-time vector heat convolution as a continuous linear map. -/
def vectorHeatSemigroupCLM {t : ℝ} (ht : 0 < t) :
    (E →ᵇ F) →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous (vectorHeatSemigroupLinearMap (E := E) ht) 1
    (fun f ↦ by simpa using norm_vectorHeatSolutionBCF_le (E := E) ht f)

@[simp]
theorem vectorHeatSemigroupCLM_apply {t : ℝ} (ht : 0 < t) (f : E →ᵇ F) :
    vectorHeatSemigroupCLM (E := E) ht f = vectorHeatSolutionBCF (E := E) ht f :=
  rfl

/-- The positive-time heat semigroup operator norm is at most one. -/
theorem norm_vectorHeatSemigroupCLM_le_one {t : ℝ} (ht : 0 < t) :
    ‖vectorHeatSemigroupCLM (E := E) (F := F) ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro f
  simpa using norm_vectorHeatSolutionBCF_le (E := E) ht f

end Poincare
