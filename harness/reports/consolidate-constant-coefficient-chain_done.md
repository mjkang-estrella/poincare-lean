# Constant-coefficient chain consolidation

Date: 2026-09-15
Branch: `worker/consolidate-constant-coefficient-chain`
Base commit: `6b8d0c3d51c8ad95019277dce709ab52a5a028f5`

## Result

Consolidated the ten modules into `Poincare.Global.ParabolicConstantCoefficient`.
All ten original bodies are byte-identical after removing their imports and
leading blank lines. No declaration, statement, proof, or namespace was edited.
The new module has nine deduplicated external imports. The supplied module order
is a valid dependency order; no external dependency imports back into the chain.

Each body has an outer anonymous section and an explicit closing `end` for its
original file-ending `noncomputable section`. This preserves file-local options,
open namespaces, and local instances. Repeated local notations were already in
distinct namespace scopes and are retained in those scopes to preserve the bodies.
They do not overlap. The source contains no new mathematical declarations.

All ten original modules remain as an import and a one-line compatibility comment.
The task's narrower file scope leaves `HANDOFF.md` and frozen contracts unchanged.
This is a worker result awaiting independent orchestrator review, not acceptance.

## Verification

- Catalog declarations checked: **142**.
- Identical original fully qualified names and printed types: **142**.
- Named declarations with exactly `[propext, Classical.choice, Quot.sound]`: **142**.
- Module-wide gate declarations checked: **151**, with no nonstandard dependencies.
- Unchanged original source bodies: **10 of 10**.

The baseline probe ran successfully before any source edits, using all ten imports,
`pp.fullNames true`, and `format.width 200`. The same scratch probe ran after the
root build. `cmp` returned 0. Both complete outputs have SHA-256
`097b69b0620591a14713b3cf1babfacae7d7512f77cd8e20e94ef71099c1e1a1`.

Actual command results:

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/consolidation-check.lean
BASE_CHECK_EXIT=0
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicConstantCoefficient.lean
FOCUSED_EXIT=0
```

The focused compiler produced no output.

```text
LEAN_NUM_THREADS=1 lake build Poincare
ROOT_BUILD_EXIT=0
Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [4201/4202] Built Poincare (2.4s)
Build completed successfully (4202 jobs).
```

The build replayed existing linter warnings. The complete local build log is
`/tmp/consolidation-root-build.log`.

```text
LEAN_NUM_THREADS=1 harness/gate.sh . Poincare.Global.ParabolicConstantCoefficient
GATE_EXIT=0
=== GATE: forbidden tokens in Poincare/Global/ParabolicConstantCoefficient.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.ParabolicConstantCoefficient ===
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompleteSpace F] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (2839 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=151 nonstandard=[]
=== GATE: PASS ===

LEAN_NUM_THREADS=1 lake env lean /tmp/consolidation-check.lean
AFTER_CHECK_EXIT=0
LEAN_NUM_THREADS=1 lake env lean /tmp/consolidation-axioms.lean
NAMED_DEPENDENCY_EXIT=0
cmp /tmp/consolidation-base-check.log /tmp/consolidation-after-check.log
TYPE_COMPARISON_EXIT=0
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicConstantCoefficient.lean
TOKEN_SCAN_EXIT=1
```

The token scan produced no output; exit 1 means no matches.

```text
git diff --check
DIFF_CHECK_EXIT=0
BODY_PRESERVATION: 10/10 byte-identical after removing imports and leading blank lines
NAMED_DEPENDENCIES_CHECKED=142
EXACT_REQUIRED_DEPENDENCIES=142
EXCEPTIONS=[]
```

An initial scratch probe used the unsupported option `pp.width` and exited 1:

```text
/tmp/consolidation-check.lean:12:0: error: Unknown option `pp.width`
```

It was corrected to `format.width` and rerun successfully before source edits.
The initial output is preserved at `/tmp/consolidation-base-check-initial.log`.
No proof compilation failed.

## Compatibility stubs

All ten stubs can be deleted later, once no branch imports them. None was deleted.

- `Poincare.Global.DuhamelParabolicHolderSeminorm`
- `Poincare.Global.DuhamelSolutionOperatorBound`
- `Poincare.Global.DuhamelSolutionOperatorCLM`
- `Poincare.Global.HeatDuhamelHeatEquation`
- `Poincare.Global.HeatDuhamelHessianDifferentiation`
- `Poincare.Global.HeatDuhamelHessianSpatialHolder`
- `Poincare.Global.HeatDuhamelHessianTimeHolder`
- `Poincare.Global.HeatDuhamelSpatialHolderHessian`
- `Poincare.Global.HeatKernelHessianMoments`
- `Poincare.Global.MovingLimitLeibniz`

## Handoff

First action for the orchestrator:
`LEAN_NUM_THREADS=1 harness/gate.sh . Poincare.Global.ParabolicConstantCoefficient`.
Independently review the body-preserving diff against the recorded base and rerun
the root build and exact declaration probe before integration.

## Exact declaration probe

```lean
import Poincare.Global.DuhamelParabolicHolderSeminorm
import Poincare.Global.DuhamelSolutionOperatorBound
import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.HeatDuhamelHeatEquation
import Poincare.Global.HeatDuhamelHessianDifferentiation
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelSpatialHolderHessian
import Poincare.Global.HeatKernelHessianMoments
import Poincare.Global.MovingLimitLeibniz
set_option pp.fullNames true
set_option format.width 200
#check Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
#check Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian
#check Poincare.DuhamelSolutionOperatorBound.abs_trace_le
#check Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_bound
#check Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_holder
#check Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_bound
#check Poincare.DuhamelSolutionOperatorBound.duhamel_value_time_estimates
#check Poincare.DuhamelSolutionOperatorBound.holder_of_bounded_lipschitz
#check Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_spatial_holder
#check Poincare.DuhamelSolutionOperatorBound.duhamel_value_parabolic_holder
#check Poincare.DuhamelSolutionOperatorBound.gradient_heatSolution_sub_bound
#check Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_reversed
#check Poincare.DuhamelSolutionOperatorBound.norm_integral_inverse_sqrt_le
#check Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_time_holder_of_le
#check Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_parabolic_holder
#check Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound
#check Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound
#check Poincare.ParabolicSolutionGraph.Graph.ext_of_u
#check Poincare.DuhamelSolutionOperatorCLM.boundConstant
#check Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec
#check Poincare.DuhamelSolutionOperatorCLM.duhamelGraph
#check Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec
#check Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add
#check Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul
#check Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap
#check Poincare.DuhamelSolutionOperatorCLM.duhamelOperator
#check Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u
#check Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le
#check Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves
#check Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
#check Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian
#check Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian
#check Poincare.HeatDuhamelHeatEquation.laplacian_duhamel_eq_integral
#check Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand
#check Poincare.HeatDuhamelHeatEquation.heatSolution_sq
#check Poincare.HeatDuhamelHeatEquation.continuousOn_rescaled_heat_integral
#check Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension
#check Poincare.HeatDuhamelHeatEquation.tendsto_heat_integrand_diagonal
#check Poincare.HeatDuhamelHeatEquation.duhamel_time_derivative_integral
#check Poincare.HeatDuhamelHeatEquation.duhamel_zero
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_eq
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul
#check Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_integral
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral
#check Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le
#check Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_pos
#check Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq
#check Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time
#check Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant
#check Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time
#check Poincare.HeatDuhamelHessianDifferentiation.continuous_kernel_pos
#check Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time
#check Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel
#check Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient
#check Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian
#check Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral
#check Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel
#check Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound
#check Poincare.HeatDuhamelHessianSpatialHolder.third_apply
#check Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le
#check Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one
#check Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq
#check Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral
#check Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound
#check Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le
#check Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le
#check Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq
#check Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le
#check Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral
#check Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral
#check Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation
#check Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation
#check Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far
#check Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le
#check Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le
#check Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder
#check Poincare.HeatDuhamelHessianTimeHolder.euclideanForm
#check Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor
#check Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time
#check Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le
#check Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv
#check Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one
#check Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul
#check Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul
#check Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq
#check Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv
#check Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral
#check Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound
#check Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound
#check Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le
#check Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le
#check Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos
#check Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv
#check Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le
#check Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference
#check Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le
#check Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le
#check Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le
#check Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder
#check Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub
#check Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral
#check Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral_sub
#check Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_sub_smul_hessian
#check Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_cancelled_integral
#check Poincare.HeatDuhamelSpatialHolderHessian.integrable_cancelled_hessian
#check Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integrand_le
#check Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integral_le
#check Poincare.HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound
#check Poincare.HeatDuhamelSpatialHolderHessian.intervalIntegrable_hessian_majorant
#check Poincare.HeatDuhamelSpatialHolderHessian.integral_hessian_majorant
#check Poincare.HeatDuhamelSpatialHolderHessian.continuous_hessian_pos
#check Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time
#check Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le
#check Poincare.HeatKernelHessianMoments.hessian_sq_smul
#check Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
#check Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
#check Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
#check Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
#check Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
#check Poincare.HeatKernelHessianMoments.weighted_hessian_integral
#check Poincare.HeatKernelHessianMoments.integrable_hessian
#check Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero
#check Poincare.HeatKernelHessianMoments.hessian_moments
#check Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants
#check Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc
#check Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants
#check Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison
#check Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound
#check Poincare.MovingLimitLeibniz.abs_rpow_sub_le
#check Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le
#check Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow
#check Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound
#check Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit
#check Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound
#check Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation
```

## Complete identical baseline and final type output

Both runs returned the following exact output:

```text
Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                              ∀ q ∈ Poincare.ParabolicHolder.cylinder T,
                                ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
                                  C * K * Poincare.ParabolicHolder.parabolicDist p q ^ α
Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                              (fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K)
Poincare.DuhamelSolutionOperatorBound.abs_trace_le
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ) :
  |∑ i, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)| ≤ 3 * ‖A‖
Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_bound (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t ∈ Set.Icc 0 T,
                              ∀ (x : Poincare.ClosedSmoothModel 3),
                                HasDerivWithinAt (fun r => u r x) (f (t, x) + Laplacian.laplacian (u t) x) (Set.Icc 0 T)
                                    t ∧
                                  |f (t, x) + Laplacian.laplacian (u t) x| ≤ M + 3 * C * K * t ^ (α / 2)
Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                              (fun p => f p + Laplacian.laplacian (u p.1) p.2) (K + 3 * C * K)
Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Poincare.ParabolicHolder.cylinder T))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  ‖fderiv ℝ (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z) x‖ ≤
    (2 * M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖fderiv ℝ (Poincare.heatKernel 1) y‖) * √t
Poincare.DuhamelSolutionOperatorBound.duhamel_value_time_estimates (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            (∀ t ∈ Set.Icc 0 T,
                                ∀ (x : Poincare.ClosedSmoothModel 3), |u t x| ≤ t * (M + 3 * C * K * T ^ (α / 2))) ∧
                              ∀ t ∈ Set.Icc 0 T,
                                ∀ s ∈ Set.Icc 0 T,
                                  ∀ (x : Poincare.ClosedSmoothModel 3),
                                    |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α / 2)) * |t - s|
Poincare.DuhamelSolutionOperatorBound.holder_of_bounded_lipschitz.{u_1} {F : Type u_1} [NormedAddCommGroup F]
  {α A B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {g : Poincare.ClosedSmoothModel 3 → F}
  (hg : ∀ (x : Poincare.ClosedSmoothModel 3), ‖g x‖ ≤ A)
  (hlip : ∀ (x y : Poincare.ClosedSmoothModel 3), ‖g x - g y‖ ≤ B * ‖x - y‖) (x y : Poincare.ClosedSmoothModel 3) :
  ‖g x - g y‖ ≤ (2 * A + B) * ‖x - y‖ ^ α
Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_spatial_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3),
                                ‖fderiv ℝ (u t) x - fderiv ℝ (u t) y‖ ≤ C * (M + K) * ‖x - y‖ ^ α
Poincare.DuhamelSolutionOperatorBound.duhamel_value_parabolic_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                              (fun p => ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2)
                              (C * (M + K))
Poincare.DuhamelSolutionOperatorBound.gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
  {f g : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hg : MeasureTheory.AEStronglyMeasurable g MeasureTheory.MeasureSpace.volume)
  (hfM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (hgN : ∀ (y : Poincare.ClosedSmoothModel 3), ‖g y‖ ≤ N)
  (hL : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y - g y‖ ≤ L) (x : Poincare.ClosedSmoothModel 3) :
  ‖fderiv ℝ (Poincare.heatSolution t f) x - fderiv ℝ (Poincare.heatSolution t g) x‖ ≤
    (L * ∫ (y : Poincare.ClosedSmoothModel 3), ‖fderiv ℝ (Poincare.heatKernel 1) y‖) * t ^ (-(1 / 2))
Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Poincare.ParabolicHolder.cylinder T))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z) x =
    ∫ (s : ℝ) in 0..t, fderiv ℝ (Poincare.heatSolution s fun y => f (t - s, y)) x
Poincare.DuhamelSolutionOperatorBound.norm_integral_inverse_sqrt_le.{u_1} {F : Type u_1} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A) {g : ℝ → F}
  (hg : ∀ r ∈ Set.Ioo a b, ‖g r‖ ≤ A * r ^ (-(1 / 2))) : ‖∫ (r : ℝ) in a..b, g r‖ ≤ 2 * A * √(b - a)
Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_time_holder_of_le {α T s t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (hT1 : T ≤ 1) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) (hst : s ≤ t) (hM : 0 ≤ M) (hK : 0 ≤ K)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Poincare.ParabolicHolder.cylinder T))
  (hfM : ∀ r ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (r, y)| ≤ M)
  (hfK : Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K)
  (x : Poincare.ClosedSmoothModel 3) :
  have u := fun r z => ∫ (v : ℝ) in 0..r, Poincare.heatSolution (r - v) (fun y => f (v, y)) z;
  ‖fderiv ℝ (u t) x - fderiv ℝ (u s) x‖ ≤
    (2 * ∫ (y : Poincare.ClosedSmoothModel 3), ‖fderiv ℝ (Poincare.heatKernel 1) y‖) * (M + K) * (t - s) ^ (α / 2)
Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_parabolic_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Poincare.ParabolicHolder.cylinder T) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K →
                            Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                              (fun p =>
                                fderiv ℝ
                                  (fun z => ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) z)
                                  p.2)
                              (C * (M + K))
Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound.{u_1} {F : Type u_1} [NormedAddCommGroup F]
  {α T K : ℝ} (hα : 0 < α) {g : ℝ × Poincare.ClosedSmoothModel 3 → F}
  (hg : Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) g K) :
  ContinuousOn g (Poincare.ParabolicHolder.cylinder T)
Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                  ∃ G,
                    (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                        ↑(WithLp.fst ↑G.u) p =
                          ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                      ‖G‖ ≤ C * ‖f‖
Poincare.ParabolicSolutionGraph.Graph.ext_of_u.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (hT : 0 < T) {G H : Poincare.ParabolicSolutionGraph.Graph α T} (hu : G.u = H.u) : G = H
Poincare.DuhamelSolutionOperatorCLM.boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ
Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
  0 < Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 ∧
    ∀ (T : ℝ),
      0 < T →
        T ≤ 1 →
          ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
            ∃ G,
              (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                  ↑(WithLp.fst ↑G.u) p =
                    ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                ‖G‖ ≤ Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖
Poincare.DuhamelSolutionOperatorCLM.duhamelGraph (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (f : Poincare.ParabolicHolder.Y α T ℝ) : Poincare.ParabolicSolutionGraph.Graph α T
Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (f : Poincare.ParabolicHolder.Y α T ℝ) :
  (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
      ↑(WithLp.fst ↑(Poincare.DuhamelSolutionOperatorCLM.duhamelGraph α T hα hα1 hT hT1 f).u) p =
        ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
    ‖Poincare.DuhamelSolutionOperatorCLM.duhamelGraph α T hα hα1 hT hT1 f‖ ≤
      Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖
Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add {α T t : ℝ} (hα : 0 < α) (ht : t ∈ Set.Icc 0 T)
  (f g : Poincare.ParabolicHolder.Y α T ℝ) (x : Poincare.ClosedSmoothModel 3) :
  ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑(f + g)) (s, y)) x =
    (∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) x) +
      ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑g) (s, y)) x
Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul {α T t : ℝ} (c : ℝ) (f : Poincare.ParabolicHolder.Y α T ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑(c • f)) (s, y)) x =
    c • ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) x
Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
  Poincare.ParabolicHolder.Y α T ℝ →ₗ[ℝ] Poincare.ParabolicSolutionGraph.Graph α T
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
  Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (f : Poincare.ParabolicHolder.Y α T ℝ) (p : ℝ × Poincare.ClosedSmoothModel 3) :
  p ∈ Poincare.ParabolicHolder.cylinder T →
    ↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).u) p =
      ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
  ∃ C,
    0 < C ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), ‖Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1‖ ≤ C
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
  (hT1 : T ≤ 1) (f : Poincare.ParabolicHolder.Y α T ℝ) (t : ℝ) :
  t ∈ Set.Icc 0 T →
    ∀ (x : Poincare.ClosedSmoothModel 3),
      ↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ut) (t, x) =
        ↑(WithLp.fst ↑f) (t, x) +
          ∑ i,
            ((↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ddu) (t, x))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
              ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace (g : Poincare.ClosedSmoothModel 3 → ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  Laplacian.laplacian g x =
    ∑ i, ((fderiv ℝ (fderiv ℝ g) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  IntervalIntegrable (fun s => fderiv ℝ (fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y))) x)
    MeasureTheory.MeasureSpace.volume 0 t
Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  IntervalIntegrable (fun s => Laplacian.laplacian (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
    MeasureTheory.MeasureSpace.volume 0 t
Poincare.HeatDuhamelHeatEquation.laplacian_duhamel_eq_integral {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  Laplacian.laplacian (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z) x =
    ∫ (s : ℝ) in 0..t, Laplacian.laplacian (Poincare.heatSolution (t - s) fun y => f (s, y)) x
Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Set.Icc 0 T) (hst : s < t)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ r ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (r, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  HasDerivAt (fun r => Poincare.heatSolution (r - s) (fun y => f (s, y)) x)
    (Laplacian.laplacian (Poincare.heatSolution (t - s) fun y => f (s, y)) x) t
Poincare.HeatDuhamelHeatEquation.heatSolution_sq (a : ℝ) (ha : 0 < a) (g : Poincare.ClosedSmoothModel 3 → ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  Poincare.heatSolution (a ^ 2) g x = ∫ (y : Poincare.ClosedSmoothModel 3), Poincare.heatKernel 1 y * g (x - a • y)
Poincare.HeatDuhamelHeatEquation.continuousOn_rescaled_heat_integral {T M : ℝ}
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  ContinuousOn (fun p => ∫ (y : Poincare.ClosedSmoothModel 3), Poincare.heatKernel 1 y * f (p.2, x - √p.1 • y))
    (Set.univ ×ˢ Set.Icc 0 T)
Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension {T M : ℝ}
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  ContinuousOn (fun p => if p.1 = 0 then f (p.2, x) else Poincare.heatSolution p.1 (fun y => f (p.2, y)) x)
    (Set.Ici 0 ×ˢ Set.Icc 0 T)
Poincare.HeatDuhamelHeatEquation.tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  Filter.Tendsto (fun s => Poincare.heatSolution (t - s) (fun y => f (s, y)) x) (nhdsWithin t (Set.Ico 0 t))
    (nhds (f (t, x)))
Poincare.HeatDuhamelHeatEquation.duhamel_time_derivative_integral {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  IntervalIntegrable (fun s => deriv (fun r => Poincare.heatSolution (r - s) (fun y => f (s, y)) x) t)
      MeasureTheory.MeasureSpace.volume 0 t ∧
    ∫ (s : ℝ) in 0..t, deriv (fun r => Poincare.heatSolution (r - s) (fun y => f (s, y)) x) t =
      Laplacian.laplacian (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z) x
Poincare.HeatDuhamelHeatEquation.duhamel_zero (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ)
  (x : Poincare.ClosedSmoothModel 3) : ∫ (s : ℝ) in 0..0, Poincare.heatSolution (0 - s) (fun y => f (s, y)) x = 0
Poincare.HeatDuhamelHessianDifferentiation.gradient_eq {t : ℝ} (ht : t ≠ 0) (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t x =
    (Poincare.heatKernel t x * -(1 / (2 * t))) • (innerSL ℝ) x
Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul (a : ℝ) (ha : 0 < a) (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) (a ^ 2) (a • x) =
    ((a ^ 3)⁻¹ * a⁻¹) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 x
Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient {t : ℝ} (ht : 0 < t) :
  MeasureTheory.Integrable ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq (a : ℝ) (ha : 0 < a) :
  ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) (a ^ 2) y‖ =
    a⁻¹ * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖
Poincare.HeatDuhamelHessianDifferentiation.gradient_integral {t : ℝ} (ht : 0 < t) :
  ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y‖ =
    (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
      t ^ (-(1 / 2))
Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (Poincare.heatSolution t f) x =
    ∫ (y : Poincare.ClosedSmoothModel 3), f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y
Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  ‖fderiv ℝ (Poincare.heatSolution t f) x‖ ≤
    (M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
      t ^ (-(1 / 2))
Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_pos :
  Continuous fun p => (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) (↑p.1) p.2
Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq (a : ℝ) (ha : 0 < a)
  (f : Poincare.ClosedSmoothModel 3 → ℝ) (x : Poincare.ClosedSmoothModel 3) :
  ∫ (y : Poincare.ClosedSmoothModel 3),
      f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) (a ^ 2) y =
    a⁻¹ •
      ∫ (y : Poincare.ClosedSmoothModel 3),
        f (x - a • y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y
Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) :
  Continuous fun p => fderiv ℝ (Poincare.heatSolution (t - ↑p.1) fun y => f (↑p.1, y)) p.2
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant (t A : ℝ) :
  IntervalIntegrable (fun s => A * (t - s) ^ (-(1 / 2))) MeasureTheory.MeasureSpace.volume 0 t
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time {T t M : ℝ}
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  IntervalIntegrable (fun s => fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
    MeasureTheory.MeasureSpace.volume 0 t
Poincare.HeatDuhamelHessianDifferentiation.continuous_kernel_pos : Continuous fun p => Poincare.heatKernel (↑p.1) p.2
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  IntervalIntegrable (fun s => Poincare.heatSolution (t - s) (fun y => f (s, y)) x) MeasureTheory.MeasureSpace.volume 0
    t
Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Set.Icc 0 T)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  HasFDerivAt (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z)
    (∫ (s : ℝ) in 0..t, fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x) x
Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  HasFDerivAt (fun z => ∫ (s : ℝ) in 0..t, fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) z)
    (∫ (s : ℝ) in 0..t,
      ∫ (y : Poincare.ClosedSmoothModel 3),
        (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y)
    x
Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
  Continuous fun x =>
    ∫ (s : ℝ) in 0..t,
      ∫ (y : Poincare.ClosedSmoothModel 3),
        (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y
Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z) x =
    ∫ (s : ℝ) in 0..t,
      ∫ (y : Poincare.ClosedSmoothModel 3),
        (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y
Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
  ContDiff ℝ 2 fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z
Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            (∀ (x : Poincare.ClosedSmoothModel 3), u 0 x = 0) ∧
                              ∀ t ∈ Set.Icc 0 T,
                                ∀ (x : Poincare.ClosedSmoothModel 3),
                                  ContDiff ℝ 2 (u t) ∧
                                    MeasureTheory.IntegrableOn
                                        (fun s =>
                                          ∫ (y : Poincare.ClosedSmoothModel 3),
                                            (f (s, x - y) - f (s, x)) •
                                              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                (t - s) y)
                                        (Set.Ioo 0 t) MeasureTheory.MeasureSpace.volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : Poincare.ClosedSmoothModel 3),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2)
Poincare.HeatDuhamelHessianSpatialHolder.third_apply {t : ℝ} (ht : t ≠ 0) (x u v w : Poincare.ClosedSmoothModel 3) :
  ((((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t x) u) v) w =
    Poincare.heatKernel t x *
      (-(Inner.inner ℝ x u * Inner.inner ℝ x v * Inner.inner ℝ x w) / (8 * t ^ 3) +
        (Inner.inner ℝ u v * Inner.inner ℝ x w + Inner.inner ℝ x v * Inner.inner ℝ u w +
            Inner.inner ℝ x u * Inner.inner ℝ v w) /
          (4 * t ^ 2))
Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le (x : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x‖ ≤
    Poincare.heatKernel 1 x * (‖x‖ ^ 3 / 8 + 3 * ‖x‖ / 4)
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
  MeasureTheory.Integrable
    (fun x =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x‖ * ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul (a : ℝ) (ha : 0 < a) (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) (a ^ 2) (a • x) =
    ((a ^ 3)⁻¹ * (a ^ 3)⁻¹) •
      (fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) (a ^ 2) (a • x)‖ *
      ‖a • x‖ ^ α =
    (a ^ 3)⁻¹ * (a ^ 3)⁻¹ * a ^ α *
      (‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x‖ * ‖x‖ ^ α)
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) (a ^ 2) x‖ *
        ‖x‖ ^ α =
    (a ^ 3)⁻¹ * a ^ α *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x‖ * ‖x‖ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {t : ℝ}
  (ht : 0 < t) :
  MeasureTheory.Integrable
    (fun x =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t x‖ * ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t x‖ * ‖x‖ ^ α =
    t ^ (α / 2 - 3 / 2) *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 x‖ * ‖x‖ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (t : ℝ),
            0 < t →
              MeasureTheory.Integrable
                  (fun x =>
                    ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t
                          x‖ *
                      ‖x‖ ^ α)
                  MeasureTheory.MeasureSpace.volume ∧
                ∫ (x : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t
                          x‖ *
                      ‖x‖ ^ α ≤
                  C * t ^ (α / 2 - 3 / 2)
Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le {α K a t : ℝ} (hα : 0 < α)
  (hα1 : α < 1) (hat : a ≤ t) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Ioo a t, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖∫ (s : ℝ) in a..t,
        ∫ (y : Poincare.ClosedSmoothModel 3),
          (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y‖ ≤
    (K *
          ∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
        (2 / α) *
      (t - a) ^ (α / 2)
Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le {α K a t : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (hK0 : 0 ≤ K) (hat : a ≤ t) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Ioo a t, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x z : Poincare.ClosedSmoothModel 3) (hscale : t - a ≤ ‖x - z‖ ^ 2) :
  ‖(∫ (s : ℝ) in a..t,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y) -
        ∫ (s : ℝ) in a..t,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, z - y) - f (s, z)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y‖ ≤
    (2 *
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
          (2 / α) *
        K *
      ‖x - z‖ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ} (hα : 0 < α)
  (hα1 : α < 1) (ht : t ∈ Set.Icc 0 T) (hK0 : 0 ≤ K) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x z : Poincare.ClosedSmoothModel 3) (hscale : t ≤ ‖x - z‖ ^ 2) :
  have u := fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
  ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
    (2 *
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
          (2 / α) *
        K *
      ‖x - z‖ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le {α ρ t : ℝ} (hα1 : α < 1) (hρ : 0 < ρ)
  (ht : ρ ^ 2 ≤ t) : ρ * ∫ (s : ℝ) in 0..t - ρ ^ 2, (t - s) ^ (α / 2 - 3 / 2) ≤ 2 / (1 - α) * ρ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x z : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) z =
    ∫ (y : Poincare.ClosedSmoothModel 3),
      (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + (z - x))
Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x z : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x - fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) z =
    ∫ (y : Poincare.ClosedSmoothModel 3),
      (f (x - y) - f x) •
        ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y -
          (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + (z - x)))
Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le (t : ℝ) (y w : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + w) -
        (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ ≤
    ∫ (r : ℝ) in 0..1,
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t (y + r • w)‖ *
        ‖w‖
Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t)
  (w : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
      (fun y =>
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t (y + w)‖ *
          ‖y‖ ^ α)
      MeasureTheory.MeasureSpace.volume ∧
    ∫ (y : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t (y + w)‖ *
          ‖y‖ ^ α ≤
      (∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t y‖ *
            ‖y‖ ^ α) +
        ‖w‖ ^ α *
          ∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t y‖
Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
  (ht : 0 < t) (w : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
    (fun p =>
      ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t
            (p.2 + p.1 • w)‖ *
        ‖p.2‖ ^ α)
    ((MeasureTheory.MeasureSpace.volume.restrict (Set.Icc 0 1)).prod MeasureTheory.MeasureSpace.volume)
Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t)
  (w : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
      (fun y =>
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + w) -
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ *
          ‖y‖ ^ α)
      MeasureTheory.MeasureSpace.volume ∧
    ∫ (y : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + w) -
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ *
          ‖y‖ ^ α ≤
      ‖w‖ *
        ((∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t y‖ *
              ‖y‖ ^ α) +
          ‖w‖ ^ α *
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) t y‖)
Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far {α t : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
  (ht : 0 < t) (w : Poincare.ClosedSmoothModel 3) (hw : ‖w‖ ^ 2 ≤ t) :
  ∫ (y : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (y + w) -
            (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ *
        ‖y‖ ^ α ≤
    ‖w‖ * t ^ (α / 2 - 3 / 2) *
      ((∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖ *
            ‖y‖ ^ α) +
        ∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖)
Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le {α t M K : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
  (ht : 0 < t) (hK0 : 0 ≤ K) {f : Poincare.ClosedSmoothModel 3 → ℝ}
  (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M)
  (hK : ∀ (x y : Poincare.ClosedSmoothModel 3), |f x - f y| ≤ K * ‖x - y‖ ^ α) (x z : Poincare.ClosedSmoothModel 3)
  (hscale : ‖x - z‖ ^ 2 ≤ t) :
  ‖fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x - fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) z‖ ≤
    ((∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖ *
                ‖y‖ ^ α) +
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖) *
          K *
        ‖x - z‖ *
      t ^ (α / 2 - 3 / 2)
Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) (hK0 : 0 ≤ K) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x z : Poincare.ClosedSmoothModel 3) (hρ : 0 < ‖x - z‖) (hscale : ‖x - z‖ ^ 2 < t) :
  ‖(∫ (s : ℝ) in 0..t - ‖x - z‖ ^ 2,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y) -
        ∫ (s : ℝ) in 0..t - ‖x - z‖ ^ 2,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, z - y) - f (s, z)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y‖ ≤
    ((∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖ *
                ‖y‖ ^ α) +
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖) *
          (2 / (1 - α)) *
        K *
      ‖x - z‖ ^ α
Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t ∈ Set.Icc 0 T,
                              ∀ (x z : Poincare.ClosedSmoothModel 3),
                                ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α
Poincare.HeatDuhamelHessianTimeHolder.euclideanForm :
  Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ
Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor {t : ℝ} (ht : t ≠ 0) (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x =
    (Poincare.heatKernel t x / (4 * t ^ 2)) • ((innerSL ℝ) x).smulRight ((innerSL ℝ) x) -
      (Poincare.heatKernel t x / (2 * t)) • Poincare.HeatDuhamelHessianTimeHolder.euclideanForm
Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time {t : ℝ} (ht : 0 < t) (x : Poincare.ClosedSmoothModel 3) :
  HasDerivAt (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x)
    ((Poincare.heatKernel t x * (‖x‖ ^ 2 / (16 * t ^ 4) - 7 / (8 * t ^ 3))) •
        ((innerSL ℝ) x).smulRight ((innerSL ℝ) x) -
      (Poincare.heatKernel t x * (‖x‖ ^ 2 / (8 * t ^ 3) - 5 / (4 * t ^ 2))) •
        Poincare.HeatDuhamelHessianTimeHolder.euclideanForm)
    t
Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le (x : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x‖ ≤
    Poincare.heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)
Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv {t : ℝ} (ht : 0 < t) :
  Continuous ((fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) t)
Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
  MeasureTheory.Integrable
    (fun x =>
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x‖ *
        ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a)
  (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) (a ^ 2)
      (a • x) =
    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) •
      (fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x
Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) (a ^ 2)
          (a • x)‖ *
      ‖a • x‖ ^ α =
    (a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α *
      (‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x‖ *
        ‖x‖ ^ α)
Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) (a ^ 2)
            x‖ *
        ‖x‖ ^ α =
    (a ^ 4)⁻¹ * a ^ α *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x‖ *
          ‖x‖ ^ α
Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) {t : ℝ}
  (ht : 0 < t) :
  MeasureTheory.Integrable
    (fun x =>
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) t x‖ *
        ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) t x‖ *
        ‖x‖ ^ α =
    t ^ (α / 2 - 2) *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 x‖ *
          ‖x‖ ^ α
Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (t : ℝ),
            0 < t →
              MeasureTheory.Integrable
                  (fun x =>
                    ‖(fun t x =>
                            deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t)
                          t x‖ *
                      ‖x‖ ^ α)
                  MeasureTheory.MeasureSpace.volume ∧
                ∫ (x : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x =>
                            deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t)
                          t x‖ *
                      ‖x‖ ^ α ≤
                  C * t ^ (α / 2 - 2)
Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound {α K T t₁ t₂ : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht₁ : t₁ ∈ Set.Icc 0 T) (ht₂ : t₂ ∈ Set.Icc 0 T) (h12 : t₁ ≤ t₂) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖∫ (s : ℝ) in t₁..t₂,
        ∫ (y : Poincare.ClosedSmoothModel 3),
          (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t₂ - s) y‖ ≤
    (∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
          (2 / α) *
        K *
      |t₂ - t₁| ^ (α / 2)
Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le {α K a b t : ℝ} (hα : 0 < α)
  (hα1 : α < 1) (hK0 : 0 ≤ K) (hab : a ≤ b) (hbt : b ≤ t) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Ioo a b, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖∫ (s : ℝ) in a..b,
        ∫ (y : Poincare.ClosedSmoothModel 3),
          (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y‖ ≤
    (K *
          ∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
        (2 / α) *
      (b - a) ^ (α / 2)
Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le {α K a t₁ t₂ : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (hK0 : 0 ≤ K) (ha : a ≤ t₁) (h12 : t₁ ≤ t₂) (hscale : t₁ - a ≤ t₂ - t₁) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Ioo a t₁, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖(∫ (s : ℝ) in a..t₁,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) •
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t₂ - s) y) -
        ∫ (s : ℝ) in a..t₁,
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) •
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t₁ - s) y‖ ≤
    (2 *
            ∫ (y : Poincare.ClosedSmoothModel 3),
              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
          (2 / α) *
        K *
      (t₂ - t₁) ^ (α / 2)
Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos :
  Continuous fun p =>
    (fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) (↑p.1) p.2
Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv {α a : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
  (ha : 0 < a) (b : ℝ) :
  MeasureTheory.Integrable
    (fun p =>
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t)
            (Max.max a p.1) p.2‖ *
        ‖p.2‖ ^ α)
    ((MeasureTheory.MeasureSpace.volume.restrict (Set.Icc a b)).prod MeasureTheory.MeasureSpace.volume)
Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
  (y : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) b y -
        (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) a y‖ ≤
    ∫ (r : ℝ) in a..b,
      ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t)
          (Max.max a r) y‖
Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference {α a b : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
  (ha : 0 < a) (hab : a ≤ b) :
  MeasureTheory.Integrable
      (fun y =>
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) b y -
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) a y‖ *
          ‖y‖ ^ α)
      MeasureTheory.MeasureSpace.volume ∧
    ∫ (y : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) b y -
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) a y‖ *
          ‖y‖ ^ α ≤
      (b - a) * a ^ (α / 2 - 2) *
        ∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1
                y‖ *
            ‖y‖ ^ α
Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le {α τ t : ℝ} (hα1 : α < 1) (hτ : 0 < τ)
  (ht : τ ≤ t) : τ * ∫ (s : ℝ) in 0..t - τ, (t - s) ^ (α / 2 - 2) ≤ 2 / (2 - α) * τ ^ (α / 2)
Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le {α a b M K : ℝ} (hα : 0 ≤ α)
  (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) (hK0 : 0 ≤ K) {f : Poincare.ClosedSmoothModel 3 → ℝ}
  (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M)
  (hK : ∀ (x y : Poincare.ClosedSmoothModel 3), |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : Poincare.ClosedSmoothModel 3) :
  ‖(∫ (y : Poincare.ClosedSmoothModel 3),
          (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) b y) -
        ∫ (y : Poincare.ClosedSmoothModel 3),
          (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) a y‖ ≤
    (∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1
                  y‖ *
              ‖y‖ ^ α) *
          K *
        (b - a) *
      a ^ (α / 2 - 2)
Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le {α T t₁ t₂ M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht₁ : t₁ ∈ Set.Icc 0 T) (ht₂ : t₂ ∈ Set.Icc 0 T) (h12 : t₁ < t₂) (hscale : t₂ - t₁ < t₁) (hK0 : 0 ≤ K)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖(∫ (s : ℝ) in 0..t₁ - (t₂ - t₁),
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) •
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t₂ - s) y) -
        ∫ (s : ℝ) in 0..t₁ - (t₂ - t₁),
          ∫ (y : Poincare.ClosedSmoothModel 3),
            (f (s, x - y) - f (s, x)) •
              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t₁ - s) y‖ ≤
    (∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1
                  y‖ *
              ‖y‖ ^ α) *
          (2 / (2 - α)) *
        K *
      (t₂ - t₁) ^ (α / 2)
Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t₁ ∈ Set.Icc 0 T,
                              ∀ t₂ ∈ Set.Icc 0 T,
                                ∀ (x : Poincare.ClosedSmoothModel 3),
                                  ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
                                    C * K * |t₁ - t₂| ^ (α / 2)
Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
    (fun y => f y • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (x - y))
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x =
    ∫ (y : Poincare.ClosedSmoothModel 3),
      f y • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t (x - y)
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral_sub {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x =
    ∫ (y : Poincare.ClosedSmoothModel 3),
      f (x - y) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y
Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_sub_smul_hessian {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
    (fun y => f (x - y) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x =
    ∫ (y : Poincare.ClosedSmoothModel 3),
      (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y
Poincare.HeatDuhamelSpatialHolderHessian.integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume)
  (hM : ∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) (x : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.Integrable
    (fun y => (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integrand_le {α K : ℝ}
  {f : Poincare.ClosedSmoothModel 3 → ℝ} (hK : ∀ (x y : Poincare.ClosedSmoothModel 3), |f x - f y| ≤ K * ‖x - y‖ ^ α)
  (t : ℝ) (x y : Poincare.ClosedSmoothModel 3) :
  ‖(f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ ≤
    K * (‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ * ‖y‖ ^ α)
Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integral_le {α K t : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
  (ht : 0 < t) {f : Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ (x y : Poincare.ClosedSmoothModel 3), |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : Poincare.ClosedSmoothModel 3) :
  ‖∫ (y : Poincare.ClosedSmoothModel 3),
        (f (x - y) - f x) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t y‖ ≤
    (K *
        ∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
      t ^ (α / 2 - 1)
Poincare.HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
  ∃ C,
    0 < C ∧
      ∀ {t M K : ℝ},
        0 < t →
          0 ≤ K →
            ∀ {f : Poincare.ClosedSmoothModel 3 → ℝ},
              MeasureTheory.AEStronglyMeasurable f MeasureTheory.MeasureSpace.volume →
                (∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) →
                  (∀ (x y : Poincare.ClosedSmoothModel 3), |f x - f y| ≤ K * ‖x - y‖ ^ α) →
                    ∀ (x : Poincare.ClosedSmoothModel 3),
                      ‖fderiv ℝ (fderiv ℝ (Poincare.heatSolution t f)) x‖ ≤ C * K * t ^ (α / 2 - 1)
Poincare.HeatDuhamelSpatialHolderHessian.intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
  IntervalIntegrable (fun s => A * (t - s) ^ (α / 2 - 1)) MeasureTheory.MeasureSpace.volume 0 t
Poincare.HeatDuhamelSpatialHolderHessian.integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
  ∫ (s : ℝ) in 0..t, A * (t - s) ^ (α / 2 - 1) = A * (2 / α) * t ^ (α / 2)
Poincare.HeatDuhamelSpatialHolderHessian.continuous_hessian_pos :
  Continuous fun p => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (↑p.1) p.2
Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time {α K T t : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : t ∈ Set.Icc 0 T) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  MeasureTheory.IntegrableOn
    (fun s =>
      ∫ (y : Poincare.ClosedSmoothModel 3),
        (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y)
    (Set.Ioo 0 t) MeasureTheory.MeasureSpace.volume
Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le {α K t : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (ht : 0 ≤ t) {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ}
  (hK : ∀ s ∈ Set.Ioo 0 t, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖∫ (s : ℝ) in 0..t,
        ∫ (y : Poincare.ClosedSmoothModel 3),
          (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y‖ ≤
    (K *
          ∫ (y : Poincare.ClosedSmoothModel 3),
            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
        (2 / α) *
      t ^ (α / 2)
Poincare.HeatKernelHessianMoments.hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : Poincare.ClosedSmoothModel 3) :
  (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (a ^ 2) (a • x) =
    ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 x
Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) {r : ℝ} (hr : 0 ≤ r) :
  r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8
Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
  MeasureTheory.Integrable
    (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 x‖ * ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ)
  (x : Poincare.ClosedSmoothModel 3) :
  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
    (a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α *
      (‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 x‖ * ‖x‖ ^ α)
Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (a ^ 2) x‖ * ‖x‖ ^ α =
    (a ^ 2)⁻¹ * a ^ α *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 x‖ * ‖x‖ ^ α
Poincare.HeatKernelHessianMoments.integrable_weighted_hessian {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) {t : ℝ} (ht : 0 < t) :
  MeasureTheory.Integrable
    (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatKernelHessianMoments.weighted_hessian_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
  ∫ (x : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α =
    t ^ (α / 2 - 1) *
      ∫ (x : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 x‖ * ‖x‖ ^ α
Poincare.HeatKernelHessianMoments.integrable_hessian {t : ℝ} (ht : 0 < t) :
  MeasureTheory.Integrable (fun x => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x)
    MeasureTheory.MeasureSpace.volume
Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
  ∫ (x : Poincare.ClosedSmoothModel 3), (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x = 0
Poincare.HeatKernelHessianMoments.hessian_moments (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (t : ℝ),
            0 < t →
              t ≤ 1 →
                MeasureTheory.Integrable
                    (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α)
                    MeasureTheory.MeasureSpace.volume ∧
                  ∫ (x : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x‖ * ‖x‖ ^ α ≤
                      C * t ^ (α / 2 - 1) ∧
                    MeasureTheory.Integrable
                        (fun x => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x)
                        MeasureTheory.MeasureSpace.volume ∧
                      ∫ (x : Poincare.ClosedSmoothModel 3),
                          (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t x =
                        0
Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants {G : ℝ → ℝ → ℝ} {D B : ℝ → ℝ}
  {μ : MeasureTheory.Measure ℝ} {S : Set ℝ} {t : ℝ}
  (hG : ∀ᶠ (r : ℝ) in nhdsWithin t S, MeasureTheory.Integrable (G r) μ) (hGt : MeasureTheory.Integrable (G t) μ)
  (hB : MeasureTheory.Integrable B μ)
  (hbound : ∀ᶠ (r : ℝ) in nhdsWithin t S, ∀ᵐ (s : ℝ) ∂μ, ‖G r s - G t s‖ ≤ B s * ‖r - t‖)
  (hD : ∀ᵐ (s : ℝ) ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t) :
  HasDerivWithinAt (fun r => ∫ (s : ℝ), G r s ∂μ) (∫ (s : ℝ), D s ∂μ) S t
Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc {g : ℝ → ℝ} {T t : ℝ} (ht : t ∈ Set.Icc 0 T)
  (hg : ContinuousOn g (Set.Icc 0 T)) : HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, g s) (g t) (Set.Icc 0 T) t
Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants {F D : ℝ → ℝ → ℝ} {b T t : ℝ}
  (ht : t ∈ Set.Icc 0 T)
  (hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Set.Icc 0 T ∧ p.1 ∈ Set.Icc 0 T ∧ p.2 ≤ p.1})
  (hdiag : F t t = b) (hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t)
  (hbound :
    ∃ B,
      MeasureTheory.IntegrableOn B (Set.Ioc 0 T) MeasureTheory.MeasureSpace.volume ∧
        ∀ᶠ (r : ℝ) in nhdsWithin t (Set.Icc 0 T),
          ∀ᵐ (s : ℝ) ∂MeasureTheory.MeasureSpace.volume.restrict (Set.Ioc 0 T),
            ‖F (Max.max r s) s - F (Max.max t s) s‖ ≤ B s * ‖r - t‖) :
  HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, F r s) (b + ∫ (s : ℝ) in 0..t, D t s) (Set.Icc 0 T) t
Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison {g g' v v' : ℝ → ℝ} {a z : ℝ} (haz : a ≤ z)
  (hg : ContinuousOn g (Set.Icc a z)) (hv : ContinuousOn v (Set.Icc a z))
  (hdg : ∀ r ∈ Set.Ioo a z, HasDerivAt g (g' r) r) (hdv : ∀ r ∈ Set.Ioo a z, HasDerivAt v (v' r) r)
  (hb : ∀ r ∈ Set.Ioo a z, |g' r| ≤ v' r) : |g z - g a| ≤ v z - v a
Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound {g g' : ℝ → ℝ} {s T u v C β : ℝ} (hβ : 0 < β)
  (hc : ContinuousOn g (Set.Icc s T)) (hd : ∀ r ∈ Set.Ioc s T, HasDerivAt g (g' r) r)
  (hb : ∀ r ∈ Set.Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)) (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
  |g v - g u| ≤ C / β * ((v - s) ^ β - (u - s) ^ β)
Poincare.MovingLimitLeibniz.abs_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hx : 0 ≤ x) (hy : 0 < y) :
  |x ^ β - y ^ β| ≤ y ^ (β - 1) * |x - y|
Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hy : y ≠ 0) :
  |Max.max x 0 ^ β - Max.max y 0 ^ β| ≤ |y| ^ (β - 1) * |x - y|
Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow {β T t : ℝ} (hβ : 0 < β) (ht : t ∈ Set.Icc 0 T) :
  IntervalIntegrable (fun s => |t - s| ^ (β - 1)) MeasureTheory.MeasureSpace.volume 0 T
Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound {g g' : ℝ → ℝ} {s T r t C β : ℝ} (hβ : 0 < β)
  (hβ1 : β ≤ 1) (hC : 0 ≤ C) (hs : s ≤ T) (hr : r ≤ T) (ht : t ≤ T) (hst : t ≠ s) (hc : ContinuousOn g (Set.Icc s T))
  (hd : ∀ z ∈ Set.Ioc s T, HasDerivAt g (g' z) z) (hb : ∀ z ∈ Set.Ioc s T, |g' z| ≤ C * (z - s) ^ (β - 1)) :
  |g (Max.max r s) - g (Max.max t s)| ≤ C / β * |t - s| ^ (β - 1) * |r - t|
Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit {F D : ℝ → ℝ → ℝ} {b T t C β : ℝ}
  (ht : t ∈ Set.Icc 0 T) (hβ : 0 < β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
  (hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Set.Icc 0 T ∧ p.1 ∈ Set.Icc 0 T ∧ p.2 ≤ p.1})
  (hdiag : F t t = b) (hderiv : ∀ s ∈ Set.Icc 0 T, ∀ r ∈ Set.Ioc s T, HasDerivAt (fun ρ => F ρ s) (D r s) r)
  (hbound : ∀ s ∈ Set.Icc 0 T, ∀ r ∈ Set.Ioc s T, |D r s| ≤ C * (r - s) ^ (β - 1)) :
  HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, F r s) (b + ∫ (s : ℝ) in 0..t, D t s) (Set.Icc 0 T) t
Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound {α T M K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K)
  {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ} (hf : ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ))
  (hM : ∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M)
  (hK : ∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
  (x : Poincare.ClosedSmoothModel 3) :
  ∃ C,
    0 ≤ C ∧
      ∀ s ∈ Set.Icc 0 T,
        ∀ r ∈ Set.Ioc s T,
          |deriv (fun ρ => Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x) r| ≤ C * (r - s) ^ (α / 2 - 1)
Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation (α : ℝ) :
  0 < α →
    α < 1 →
      ∀ (T : ℝ),
        0 < T →
          T ≤ 1 →
            ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
              0 ≤ M →
                0 ≤ K →
                  ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                    (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                      (∀ t ∈ Set.Icc 0 T,
                          ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                        have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                        (∀ (x : Poincare.ClosedSmoothModel 3), u 0 x = 0) ∧
                          ∀ t ∈ Set.Icc 0 T,
                            ∀ (x : Poincare.ClosedSmoothModel 3),
                              HasDerivWithinAt (fun r => u r x)
                                (f (t, x) +
                                  ∑ i,
                                    ((fderiv ℝ (fderiv ℝ (u t)) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                      ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                (Set.Icc 0 T) t
```

## Complete named dependency output

The scratch program imports `Poincare.Global.ParabolicConstantCoefficient` and
runs `#print axioms` for each fully qualified name in the declaration probe.

```text
'Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.abs_trace_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_value_time_estimates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.holder_of_bounded_lipschitz' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_spatial_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_value_parabolic_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.gradient_heatSolution_sub_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_reversed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.norm_integral_inverse_sqrt_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_time_holder_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_parabolic_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.laplacian_duhamel_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.heatSolution_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.continuousOn_rescaled_heat_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.tendsto_heat_integrand_diagonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.duhamel_time_derivative_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.duhamel_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_kernel_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.third_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_third_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.third_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_weighted_third' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.third_moment_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_integral_cancelled_hessian_near_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.far_time_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_eq_common_cancelled_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.hessian_heatSolution_difference_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_hessian_translation_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_third_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.integrable_segment_weighted_third' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.weighted_hessian_translation_far' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.norm_heat_hessian_difference_far_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.far_hessian_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_sub_smul_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_cancelled_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_cancelled_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integrand_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.intervalIntegrable_hessian_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.integral_hessian_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.continuous_hessian_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound]
```
