# Heat Duhamel heat equation: blocked at the moving-limit derivative

Date: 2026-09-11. Class B worker attempt. Base commit
`c165951b1506056533cbb63ccc0e52e45cffb0ab`; branch
`worker/heat-duhamel-heat-equation`; verified proof head `28e88eb4`.

The frozen `duhamel_solves_heat_equation` is **not proved or declared**.
Eleven partial theorems and one local instance are verified in the single new
Lean module `Poincare/Global/HeatDuhamelHeatEquation.lean`. Each theorem was
committed separately after successful elaboration and dependency printing.
No existing Lean file, root import, or frozen contract was changed. The
required dated handoff is the only existing documentation file changed.
This report does not mark the task accepted or merge the worker branch.

## Verified progress

| Theorem | Result |
| --- | --- |
| `laplacian_eq_hessian_trace` | Mathlib's Euclidean Laplacian equals exactly the user's coordinate Hessian sum. |
| `intervalIntegrable_heat_hessian` | The actual heat convolution Hessian is integrable in forcing time, including the singular endpoint in the almost-everywhere sense. |
| `intervalIntegrable_heat_laplacian` | Its coordinate trace is genuinely integrable in forcing time. |
| `laplacian_duhamel_eq_integral` | The actual Laplacian of the Duhamel value equals the time integral of the heat convolution Laplacian. |
| `hasDerivAt_heat_integrand` | For `s < t`, differentiating the heat integrand in the observation time gives its spatial Laplacian. |
| `heatSolution_sq` | Exact rescaling of heat convolution to the unit Gaussian. |
| `continuousOn_rescaled_heat_integral` | Joint continuity in elapsed time and forcing time of the rescaled integral. |
| `continuousOn_heat_integrand_extension` | Giving the semigroup its initial value at elapsed time zero yields joint continuity on `Ici 0 ×ˢ Icc 0 T`. |
| `tendsto_heat_integrand_diagonal` | The Duhamel boundary limit from `Ico 0 t` equals `f(t,x)`. |
| `duhamel_time_derivative_integral` | The interior time derivative is integrable, and its integral is exactly the actual Duhamel Laplacian. |
| `duhamel_zero` | The specified Duhamel formula vanishes at initial time. |

The continuity statements require only the original boundedness and cylinder
continuity. They do not require continuity of the forcing as a BUC-valued
path or any temporal Hölder hypothesis. The other analytic lemmas use the
original K2 spatial Hölder hypotheses. There are no added data definitions
or analytic premises concealed in an instance.

## Laplacian spelling

The initial probe checked `EuclideanSpace.basisFun (Fin 3) ℝ` against the
landed scalar and vector heat-equation theorems. Helper statements use the
existing notation `Δ`, defined by contraction of the second derivative with
the canonical Euclidean tensor. Its expansion in the requested basis is
proved by `laplacian_eq_hessian_trace`, using
`InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` and
`iteratedFDeriv_two_apply`. The basis expansion is theorem-backed, not a
claim that the two Lean expressions are equal by `rfl`. The frozen target
probe retains the user's sum verbatim and rewrites it with the verified
identity. The scalar homogeneous heat-equation theorem is used because the
forcing here is real-valued; the vector theorem was located and inspected.

## Exact remaining step

After introducing **all** the frozen hypotheses, discharging the zero
initial value, and rewriting with `duhamel_time_derivative_integral`, Lean
leaves precisely:

```lean
HasDerivWithinAt
  (fun r : ℝ => ∫ s in (0 : ℝ)..r,
    heatSolution (r - s) (fun y => f (s, y)) x)
  (f (t, x) + ∫ s in (0 : ℝ)..t,
    deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t)
  (Icc 0 T) t
```

The context already contains the interior derivative's `IntervalIntegrable`
proof, the diagonal `Tendsto` proof, and its pointwise `HasDerivAt` proof for
all `s ∈ Ioo 0 t`. The exact target probe below deliberately ends with
`trace_state`; its exit code is 1, with this unsolved goal. It is evidence of
the remaining obligation, not a checked theorem.

## Routes examined and why work stops here

1. **Boundary approximation.** The initially found scalar approximate-identity
   statement required integrable whole-space data, and the BUC continuity
   material bundles data in a supremum norm. Instead, rescaling gives
   `H_(a²)g(x) = ∫ K_1(y) g(x-a y) dy`. Dominated convergence with the fixed
   majorant `M K_1` proves joint continuity and closes the boundary limit.
2. **Spatial and time interchanges.** K2 identifies the actual Hessian with
   the cancelled integral. Its integrability passes through bounded linear
   evaluation twice and then a finite sum. This closes the Laplacian
   interchange and identifies the integrable interior time derivative.
3. **Leibniz interchange.** Mathlib's
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   differentiates a *fixed* interval. It asks for a neighborhood `s ∈ 𝓝 t`
   and a single integrable bound for the derivative at every observation
   time in that neighborhood. In the present notation its resisting bound
   has the shape

   ```lean
   ∀ᵐ q ∂volume, q ∈ Ι 0 t → ∀ r ∈ s,
     ‖deriv (fun τ : ℝ =>
       heatSolution (τ - q) (fun y => f (q, y)) x) r‖ ≤ bound q
   ```

   The landed cancellation majorant has time factor
   `(r-q)^(α/2-1)` for `r>q`. Its exponent is negative. Fixed-time
   integrability at `r=t` does not provide the required uniform bound in a
   two-sided neighborhood: for `q<t` close to `t`, that neighborhood contains
   observation times arbitrarily close to `q` from above. The positive-time
   derivative theorem also cannot be applied across `r=q`. This is a limit
   of this direct application, not a counterexample to the frozen PDE.
   The ordinary variable-upper-limit FTC theorem, also printed below,
   holds the integrand fixed and therefore does not supply the missing
   parameter derivative.

A right-sided difference-quotient argument can use the decreasing majorant
for observation times `r≥t`, but must still prove the short-interval boundary
average and the derivative interchange. Reaching the final endpoint `T`
also requires a left-sided argument, or continuity of the resulting velocity
and `hasDerivWithinAt_Icc_of_continuousOn_rightDerivative`. That helper was
located in `SemilinearHeatBUCTwoSidedInteriorRegularity.lean`; neither of its
new continuity/derivative obligations was assumed. No temporal Hölder result
from the other worker was used. The missing proof is left explicit under the
permitted class-B stop condition.

The interval-parametric API was initially unavailable under the module's
imports. Its explicit import exposed a missing cached object. The focused
build of `Mathlib.Analysis.Calculus.ParametricIntervalIntegral` succeeded;
the final API probe includes that import. This cache issue was repaired and
is not the mathematical blocker.

## Gates and reproducibility

The final source command returned exit 0 with no output:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHeatEquation.lean
```

The required token scan returned no matches, exit 1 as expected for an empty
`rg` result. `git diff c165951b1506056533cbb63ccc0e52e45cffb0ab --check`
returned exit 0. The dependency probe copies the module verbatim into a
scratch Lean file and appends `#print axioms` for all 11 theorems and the
named local instance. Every final declaration has exactly
`[propext, Classical.choice, Quot.sound]`; failed intermediate probes are
preserved separately below. No full root build or integration audits were
run, because this worker result remains unaccepted.

First action for the next proof attempt: reproduce the exact remaining-goal
probe by appending the following snippet to a scratch copy of the new
module, then implement its right-sided moving-limit argument. Reviewers can
first rerun the focused source command above.


```lean
namespace Poincare.HeatDuhamelHeatEquation
local notation "E" => Poincare.ClosedSmoothModel 3

example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x : E, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    HasDerivWithinAt (fun r : ℝ => u r x)
      (f (t, x) + ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u t)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (Icc 0 T) t := by
  intro α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK
  dsimp only
  refine ⟨fun x => duhamel_zero f x, ?_⟩
  intro t ht x
  rw [← laplacian_eq_hessian_trace]
  rw [← (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).2]
  have hinterior := (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).1
  have hboundary := tendsto_heat_integrand_diagonal ht hf hM x
  have hpointwise := fun s (hs : s ∈ Ioo 0 t) =>
    hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x
  trace_state

end Poincare.HeatDuhamelHeatEquation
```


## Recorded command output

All captured Lean attempts, including failures, are retained below. Empty output is
shown by the following exit-code line. Trailing whitespace is normalized for
the repository whitespace gate. Repeated source copies in successful dependency
probes differ only by the then-current module and the appended print commands.


### run-001

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Probe.lean
EuclideanSpace.basisFun.{u_1, u_3} (ι : Type u_1) (𝕜 : Type u_3) [RCLike 𝕜] [Fintype ι] :
  OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)
InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis.{u_2, u_3, u_5} {E : Type u_2} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {F : Type u_3} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
  {ι : Type u_5} [Fintype ι] (v : OrthonormalBasis ι ℝ E) : Δ f = fun x => ∑ i, (iteratedFDeriv ℝ 2 f x) ![v i, v i]
/tmp/heat-equation-evidence/Probe.lean:6:7: error(lean.unknownIdentifier): Unknown constant `intervalIntegral.integral_apply`
ContinuousLinearMap.intervalIntegral_comp_comm.{u_2, u_5, u_6} {𝕜 : Type u_2} {E : Type u_5} {F : Type u_6}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {μ : Measure ℝ} {f : ℝ → E} [RCLike 𝕜] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace F] [CompleteSpace E] (L : E →L[𝕜] F)
  (hf : IntervalIntegrable f μ a b) : ∫ (x : ℝ) in a..b, L (f x) ∂μ = L (∫ (x : ℝ) in a..b, f x ∂μ)
/tmp/heat-equation-evidence/Probe.lean:8:7: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Integrable.clm_apply`
/tmp/heat-equation-evidence/Probe.lean:9:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.heatSolution_hasDerivAt`
'Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
/tmp/heat-equation-evidence/Probe.lean:13:85: error: unsolved goals
f : Poincare.ClosedSmoothModel 3 → ℝ
x : Poincare.ClosedSmoothModel 3
⊢ ∑ x_1,
      ((fderiv ℝ (fderiv ℝ f) x)
          (![(EuclideanSpace.basisFun (Fin 3) ℝ) x_1, (EuclideanSpace.basisFun (Fin 3) ℝ) x_1] 0))
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) x_1, (EuclideanSpace.basisFun (Fin 3) ℝ) x_1] 1) =
    ∑ i, ((fderiv ℝ (fderiv ℝ f) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)

exit_code=1
```


### run-002

```text
$ rg -n 'theorem|lemma' Poincare/Global/HeatCauchyFinal.lean | tail -15
25:theorem one_add_norm_sq_sub_left_le_translate_bound (x y : E) :
31:theorem deriv_heatKernel_time_eq_heatKernel_mul {t : ℝ} (ht : 0 < t) (u : E) :
44:theorem laplacian_heatKernel_sub_left_eq_heatKernel_mul {t : ℝ} (ht : 0 < t) (x y : E) :
72:theorem heatKernel_time_window_gaussian_le {t τ : ℝ} (ht : 0 < t)
122:theorem heatKernel_laplacian_quadratic_abs_le {t : ℝ} (ht : 0 < t) (x y : E) :
166:theorem heatKernel_time_window_quadratic_abs_le {t τ : ℝ} (ht : 0 < t)
205:theorem heatKernel_time_deriv_window_sub_left_mul_le_timeWindowEnvelope {t τ C : ℝ}
254:theorem laplacian_heatKernel_sub_left_mul_le_laplacianEnvelope {t C : ℝ} (ht : 0 < t)
284:theorem heatKernel_time_deriv_integrand_aestronglyMeasurable {t : ℝ} (ht : 0 < t)
308:theorem heatKernel_time_deriv_integral_hasDerivAt {t C : ℝ} (ht : 0 < t)
364:theorem heatSolution_solves_heatEquation_of_spatial_interchange {t C : ℝ}
376:Model Cauchy theorem with the time interchange discharged.  The remaining
379:theorem heatSolution_model_cauchy_problem_of_spatial_interchange {t C : ℝ}

exit_code=0
```


### run-003

```text
$ rg -n 'integrable.*apply|Integrable.*apply|def apply' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean

exit_code=1
```


### run-004

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHeatEquation.lean

exit_code=0
```


### run-005

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
/tmp/heat-equation-evidence/Dependencies.lean:30:14: error(lean.unknownIdentifier): Unknown constant `Poincare.HeatDuhamelHeatEquation.instNormedAddCommGroupContinuousLinearMap`

exit_code=1
```


### run-006

```text
$ rg -n 'intervalIntegral\.integral_same|heatSolution_apply_swap|apply_continuousLinearMap|intervalIntegral_apply|integral_finsetSum' Poincare/Global/HeatCauchy.lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:441:    exact intervalIntegral.integral_same
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1207:theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α → H →SL[σ] E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:768:nonrec theorem integral_finsetSum {ι} {s : Finset ι} {f : ι → ℝ → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:771:  simp only [intervalIntegral_eq_integral_uIoc, integral_finsetSum s fun i hi => (h i hi).def',
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:774:@[deprecated (since := "2026-04-08")] alias integral_finset_sum := integral_finsetSum
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:853:theorem _root_.ContinuousLinearMap.intervalIntegral_apply {a b : ℝ} {φ : ℝ → F →L[𝕜] E}
Poincare/Global/HeatCauchy.lean:109:    exact heatSolution_apply_swap (E := E) τ f x

exit_code=0
```


### run-007

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```


### run-008

```text
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelHeatEquation.lean

exit_code=1
```


### run-009

```text
$ git diff --check

exit_code=0
```


### run-010

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHeatEquation.lean

exit_code=0
```


### run-011

```text
$ rg -n 'heatKernel_sq_smul|integral_comp_smul|integral_smul' Poincare/Global/HeatDuhamelHessianDifferentiation.lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:29:    heatKernel_sq_smul a ha x]
Poincare/Global/HeatKernelHessianMoments.lean:107:  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:34:    heatKernel_sq_smul a ha x]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:53:  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:131:  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:140:      rw [integral_smul]

exit_code=0
```


### run-012

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```


### run-013

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
/tmp/heat-equation-evidence/Dependencies.lean:58:2: error: Tactic `apply` failed: could not unify the conclusion of `@IntervalIntegrable.sum`
  IntervalIntegrable (∑ i ∈ ?s, ?f i) ?μ ?a ?b
with the goal
  IntervalIntegrable
    (fun s =>
      ∑ i,
        ((fderiv ℝ (fderiv ℝ (heatSolution (t - s) fun y => f (s, y))) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
    volume 0 t

Note: The full type of `@IntervalIntegrable.sum` is
  ∀ {ι : Type ?u.19417.512} {a b : ℝ} {μ : Measure ℝ} {ε : Type ?u.19417.511} [inst : TopologicalSpace ε]
    [inst_1 : ENormedAddCommMonoid ε] [ContinuousAdd ε] (s : Finset ι) {f : ι → ℝ → ε},
    (∀ i ∈ s, IntervalIntegrable (f i) μ a b) → IntervalIntegrable (∑ i ∈ s, f i) μ a b

α T t M K : ℝ
hα : 0 < α
hα1 : α < 1
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
hK : ∀ s ∈ Icc 0 T, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
hi : IntervalIntegrable (fun s => fderiv ℝ (fderiv ℝ (heatSolution (t - s) fun y => f (s, y))) x) volume 0 t
⊢ IntervalIntegrable
    (fun s =>
      ∑ i,
        ((fderiv ℝ (fderiv ℝ (heatSolution (t - s) fun y => f (s, y))) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
    volume 0 t
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```


### run-014

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```


### run-015

```text
$ rg -n 'theorem.*continuousOn_of_dominated|theorem.*continuous_of_dominated|theorem heatKernel_sq_smul|theorem.*integral_comp_smul_of_nonneg|theorem.*Finset.sum_apply' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean Poincare/Global/HeatKernelScaling.lean
rg: Poincare/Global/HeatKernelScaling.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:114:theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:462:theorem continuousOn_of_dominated {F : X → α → G} {bound : α → ℝ} {s : Set X}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:473:theorem continuous_of_dominated {F : X → α → G} {bound : α → ℝ}

exit_code=2
```


### run-016

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-017

```text
$ rg -n 'theorem heatKernel_sq_smul|theorem integral_same|theorem HasDerivAt.sub_const|theorem HasDerivAt.comp|theorem HasDerivAt.congr_deriv' Poincare/Global .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:671:theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:605:theorem HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (h' : f' = g') : HasDerivAt f g' x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:186:theorem HasDerivAt.comp_hasFDerivAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:190:theorem HasDerivAt.comp_hasFDerivAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:195:theorem HasDerivAt.comp_hasFDerivWithinAt {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:200:theorem HasDerivAt.comp_hasFDerivWithinAt_of_eq {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:258:theorem HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:266:theorem HasDerivAt.comp_of_eq
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:281:theorem HasDerivAt.comp_hasDerivWithinAt (hh₂ : HasDerivAt h₂ h₂' (h x))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean:285:theorem HasDerivAt.comp_hasDerivWithinAt_of_eq (hh₂ : HasDerivAt h₂ h₂' y)
Poincare/Global/BoundedUniformContinuousHeat.lean:135:theorem heatKernel_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :

exit_code=0
```


### run-018

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-019

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-020

```text
$ rg -n 'theorem.*(sqrt_pos|sq_sqrt|continuous_sqrt|sqrt_zero)|theorem ContinuousOn.mul|theorem Filter.Tendsto.congr' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean .lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean

exit_code=1
```


### run-021

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
/tmp/heat-equation-evidence/Dependencies.lean:145:42: error: unexpected token ':='; expected ')', ',' or ':'
/tmp/heat-equation-evidence/Dependencies.lean:145:40: error: Application type mismatch: The argument
  E
has type
  Type
of sort `Type 1` but is expected to have type
  ℝ
of sort `Type` in the application
  contDiff_heatKernel_spatial E
/tmp/heat-equation-evidence/Dependencies.lean:138:76: error: unsolved goals
case h_bound
T M : ℝ
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
⊢ ∀ x_1 ∈ univ ×ˢ Icc 0 T, ∀ᵐ (a : E), ‖heatKernel 1 a * f (x_1.2, x - √x_1.1 • a)‖ ≤ heatKernel 1 a * M

case bound_integrable
T M : ℝ
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
⊢ Integrable (fun y => heatKernel 1 y * M) volume

case h_cont
T M : ℝ
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
⊢ ∀ᵐ (a : E), ContinuousOn (fun x_1 => heatKernel 1 a * f (x_1.2, x - √x_1.1 • a)) (univ ×ˢ Icc 0 T)
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```


### run-022

```text
$ rg -n 'continuous_sqrt|sq_sqrt|sqrt_pos|sqrt_zero' .lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean | head -20
rg: .lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean: IO error for operation on .lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean: No such file or directory (os error 2)

exit_code=0
```


### run-023

```text
$ rg -n 'tendsto_nhdsWithin_iff|Tendsto.congr|theorem.*congr.*Tendsto|nhdsWithin_mono|ContinuousWithinAt.tendsto' .lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean .lake/packages/mathlib/Mathlib/Topology/Continuous.lean .lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean .lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean | head -35
.lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean:101:theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
.lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean:109:theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:216:  inter_mem (nhdsWithin_mono _ inter_subset_left h) (nhdsWithin_mono _ inter_subset_right h')
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:351:  this.mono <| nhdsWithin_mono _ fun _y hy ↦ lt_of_strongLT fun i ↦ hy i trivial
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:374:theorem tendsto_nhdsWithin_mono_left {f : α → β} {a : α} {s t : Set α} {l : Filter β} (hst : s ⊆ t)
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:376:  h.mono_left <| nhdsWithin_mono a hst
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:378:theorem tendsto_nhdsWithin_mono_right {f : β → α} {l : Filter β} {a : α} {s t : Set α} (hst : s ⊆ t)
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:380:  h.mono_right (nhdsWithin_mono a hst)
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:458:theorem tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s : Set α} {f : β → α} :
.lake/packages/mathlib/Mathlib/Topology/NhdsWithin.lean:512:theorem tendsto_nhdsWithin_iff_subtype {s : Set α} {a : α} (h : a ∈ s) (f : α → β) (l : Filter β) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:39:theorem ContinuousWithinAt.tendsto (h : ContinuousWithinAt f s x) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:54:  tendsto_nhdsWithin_iff_subtype h f _
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:56:theorem ContinuousWithinAt.tendsto_nhdsWithin {t : Set β}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:61:theorem ContinuousWithinAt.tendsto_nhdsWithin_image (h : ContinuousWithinAt f s x) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:81:  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:230:  h.mono_left (nhdsWithin_mono x hs)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:311:    ContinuousOn f t := fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:398:  h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)

exit_code=0
```


### run-024

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-025

```text
$ rg -n 'theorem sq_sqrt|theorem sqrt_zero|theorem sqrt_pos|theorem continuous_sqrt|lemma sq_sqrt|lemma continuous_sqrt' .lake/packages/mathlib/Mathlib | head -20
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:49:@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:95:theorem continuous_sqrt : Continuous sqrt := sqrt.continuous
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:97:@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:126:theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:178:theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:192:theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:276:theorem sq_sqrt' : √x ^ 2 = max x 0 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:286:theorem sqrt_pos : 0 < √x ↔ 0 < x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:648:lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by

exit_code=0
```


### run-026

```text
$ rg -n 'integral_mul_const|integral_heatKernel_eq_one|self_mem_nhdsWithin' Poincare/Global/Heat*.lean | head -20
Poincare/Global/HeatDuhamelBUCGeneratorHolderContinuity.lean:129:    · filter_upwards [self_mem_nhdsWithin] with t ht
Poincare/Global/HeatDuhamelBUCGeneratorDini.lean:245:    filter_upwards [Icc_mem_nhdsLT ht, self_mem_nhdsWithin] with c hc hct
Poincare/Global/HeatSemigroupOperator.lean:29:  exact integral_heatKernel_eq_one (E := E) ht
Poincare/Global/HeatKernelHessianMoments.lean:156:      (integral_heatKernel_eq_one («E» := E) ht)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:269:    _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:478:          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
Poincare/Global/HeatKernelIntegral.lean:61:theorem integral_heatKernel_eq_one {t : ℝ} (ht : 0 < t) :
Poincare/Global/HeatGeneratorLocality.lean:135:  filter_upwards [self_mem_nhdsWithin] with t ht
Poincare/Global/HeatGeneratorLocality.lean:214:      _ = Q := by rw [integral_heatKernel_eq_one (E := E) ht2, mul_one]
Poincare/Global/HeatGeneratorLocality.lean:229:    · filter_upwards [self_mem_nhdsWithin] with t ht
Poincare/Global/HeatGeneratorLocality.lean:379:  filter_upwards [self_mem_nhdsWithin] with t ht
Poincare/Global/HeatSemigroupBUCStrongContinuity.lean:68:  have hmass := integral_heatKernel_eq_one (E := E) ht
Poincare/Global/HeatLaplacianZeroTime.lean:540:    filter_upwards [self_mem_nhdsWithin] with t ht
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:285:      rw [integral_mul_const]
Poincare/Global/HeatSemigroupBUCGeneratorEvolution.lean:410:  filter_upwards [self_mem_nhdsWithin] with ε hε
Poincare/Global/HeatKernelSemigroup.lean:93:    exact integral_heatKernel_eq_one (E := E) hr
Poincare/Global/HeatKernelSemigroup.lean:189:            rw [integral_mul_const]

exit_code=0
```


### run-027

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
/tmp/heat-equation-evidence/Dependencies.lean:169:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  if p.1 = 0 then ?m.153 else ?m.154
in the target expression
  (fun p => if p.1 = 0 then f (p.2, x) else heatSolution p.1 (fun y => f (p.2, y)) x) p =
    (fun p => ∫ (y : E), heatKernel 1 y * f (p.2, x - √p.1 • y)) p

case neg
T M : ℝ
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
hc : ContinuousOn (fun p => ∫ (y : E), heatKernel 1 y * f (p.2, x - √p.1 • y)) (Ici 0 ×ˢ Icc 0 T)
p : ℝ × ℝ
hp : p ∈ Ici 0 ×ˢ Icc 0 T
hz : ¬p.1 = 0
⊢ (fun p => if p.1 = 0 then f (p.2, x) else heatSolution p.1 (fun y => f (p.2, y)) x) p =
    (fun p => ∫ (y : E), heatKernel 1 y * f (p.2, x - √p.1 • y)) p
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```


### run-028

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-029

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-030

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-031

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/Dependencies.lean
'Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
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

exit_code=0
```


### run-032

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHeatEquation.lean

exit_code=0
```


### run-033

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/RemainingStep.lean
/tmp/heat-equation-evidence/RemainingStep.lean:249:21: error: unsolved goals
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
hinterior : IntervalIntegrable (fun s => deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t
hboundary : Filter.Tendsto (fun s => heatSolution (t - s) (fun y => f (s, y)) x) (𝓝[Ico 0 t] t) (𝓝 (f (t, x)))
hpointwise :
  ∀ s ∈ Ioo 0 t,
    HasDerivAt (fun r => heatSolution (r - s) (fun y => f (s, y)) x) (Δ (heatSolution (t - s) fun y => f (s, y)) x) t
⊢ HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, heatSolution (r - s) (fun y => f (s, y)) x)
    (f (t, x) + ∫ (s : ℝ) in 0..t, deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) (Icc 0 T) t
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
hinterior : IntervalIntegrable (fun s => deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t
hboundary : Filter.Tendsto (fun s => heatSolution (t - s) (fun y => f (s, y)) x) (𝓝[Ico 0 t] t) (𝓝 (f (t, x)))
hpointwise :
  ∀ s ∈ Ioo 0 t,
    HasDerivAt (fun r => heatSolution (r - s) (fun y => f (s, y)) x) (Δ (heatSolution (t - s) fun y => f (s, y)) x) t
⊢ HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, heatSolution (r - s) (fun y => f (s, y)) x)
    (f (t, x) + ∫ (s : ℝ) in 0..t, deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) (Icc 0 T) t

exit_code=1
```


### run-034

```text
$ rg -n 'has(F)?DerivWithinAt_integral|Has(F)?DerivWithinAt.*integral|integral.*(leibniz|Leibniz)' .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/MeasureTheory/Integral

exit_code=1
```


### run-035

```text
$ rg -n 'hasDerivWithinAt_Icc_of_continuousOn_rightDerivative|hasDerivAt_integral_of_dominated_loc_of_deriv_le|integral_hasDerivWithinAt_of_tendsto_ae_right' Poincare/Global/SemilinearHeatBUCTwoSidedInteriorRegularity.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean
Poincare/Global/SemilinearHeatBUCTwoSidedInteriorRegularity.lean:46:theorem hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
Poincare/Global/SemilinearHeatBUCTwoSidedInteriorRegularity.lean:87:`hasDerivWithinAt_Icc_of_continuousOn_rightDerivative` is an ordinary
Poincare/Global/SemilinearHeatBUCTwoSidedInteriorRegularity.lean:98:    (hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
Poincare/Global/SemilinearHeatBUCTwoSidedInteriorRegularity.lean:153:    hasDerivWithinAt_Icc_of_continuousOn_rightDerivative
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean:97:nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean:110:  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:69:`integral_hasFDerivAt_of_tendsto_ae`). Similarly, `integral_hasDerivWithinAt_of_tendsto_ae_right`
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:859:theorem integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:872:  integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:882:  (integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas hb).derivWithin hs
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:902:  exact (integral_hasDerivWithinAt_of_tendsto_ae_right hf.symm hmeas ha).neg

exit_code=0
```


### run-036

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/APIs.lean
/tmp/heat-equation-evidence/APIs.lean:232:7: error(lean.unknownIdentifier): Unknown constant `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right.{u_3} {E : Type u_3} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {c : E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
  [intervalIntegral.FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b) volume)
  (hb : Filter.Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) : HasDerivWithinAt (fun u => ∫ (x : ℝ) in a..u, f x) c s b

exit_code=1
```


### run-037

```text
$ git diff c165951b1506056533cbb63ccc0e52e45cffb0ab --check

exit_code=0
```


### run-038

```text
$ git log --oneline c165951b1506056533cbb63ccc0e52e45cffb0ab..HEAD
28e88eb4 Verify zero initial value of the specified Duhamel formula
310ef549 Identify the integrable interior time derivative with the Duhamel Laplacian
d52217bf Prove the Duhamel diagonal limit equals the forcing value
b975f940 Extend heat convolution continuously to zero elapsed time
1e647eb8 Prove joint continuity of the rescaled heat integral on the cylinder
b1768d94 Rescale the heat convolution to the unit Gaussian
8ddc1019 Identify the heat integrand time derivative away from the diagonal
96263a49 Commute the Euclidean Laplacian with the Duhamel integral
81fc2987 Prove time integrability of the heat convolution Laplacian
0c2aa1e5 Prove time integrability of the actual heat convolution Hessian
84a810e8 Prove the Euclidean Laplacian equals the coordinate Hessian trace

exit_code=0
```


### run-039

```text
$ git diff c165951b1506056533cbb63ccc0e52e45cffb0ab -- Poincare/Global/HeatDuhamelHeatEquation.lean
diff --git a/Poincare/Global/HeatDuhamelHeatEquation.lean b/Poincare/Global/HeatDuhamelHeatEquation.lean
new file mode 100644
index 00000000..838fc8e2
--- /dev/null
+++ b/Poincare/Global/HeatDuhamelHeatEquation.lean
@@ -0,0 +1,230 @@
+import Poincare.Global.HeatDuhamelHessianDifferentiation
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology RealInnerProductSpace Interval Laplacian
+
+namespace Poincare.HeatDuhamelHeatEquation
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+  HeatDuhamelHessianDifferentiation
+
+/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
+theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
+    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
+      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
+  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
+    (EuclideanSpace.basisFun (Fin 3) ℝ)]
+  simp [iteratedFDeriv_two_apply]
+
+/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
+theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    IntervalIntegrable (fun s : ℝ =>
+      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
+  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
+  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have hc : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hsT, mem_univ y⟩)
+  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
+    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
+
+/-- Taking the trace preserves the time integrability supplied by cancellation. -/
+theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    IntervalIntegrable (fun s : ℝ =>
+      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
+  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
+  simp_rw [laplacian_eq_hessian_trace]
+  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
+      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
+        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
+      volume 0 t :=
+    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
+      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
+  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)
+
+/-- The Laplacian passes through the Duhamel time integral. -/
+theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z)) x =
+      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
+  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
+  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
+      ∫ s in (0 : ℝ)..t,
+        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
+    apply intervalIntegral.integral_congr_ae_restrict
+    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
+    have hc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
+      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
+  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
+      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
+    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
+  simp_rw [laplacian_eq_hessian_trace]
+  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
+  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
+    ContinuousLinearMap.intervalIntegral_apply (hv _)]
+  symm
+  apply intervalIntegral.integral_finsetSum
+  intro i _
+  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩
+
+/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
+theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
+    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
+      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
+  have hc : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hs, mem_univ y⟩)
+  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
+    simpa only [Real.norm_eq_abs] using hM s hs
+  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
+    hc.aestronglyMeasurable hb x
+  have hd' : DifferentiableAt ℝ
+      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
+    simpa only [heatSolution_apply_swap] using hd.differentiableAt
+  have hp := hd'.hasDerivAt
+  rw [heatSolution_solves_heatEquation_of_bounded_measurable
+    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
+  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)
+
+/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
+theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
+    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
+  rw [heatSolution_apply]
+  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
+  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
+    smul_eq_mul, mul_assoc, integral_const_mul] at hc
+  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm
+
+/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
+theorem continuousOn_rescaled_heat_integral {T M : ℝ}
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
+      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
+  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
+  · intro p hp
+    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
+      hf.comp_continuous
+        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
+        (fun y => ⟨hp.2, mem_univ _⟩)
+    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
+  · intro p hp
+    exact Filter.Eventually.of_forall fun y => by
+      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
+      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
+  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
+  · refine Filter.Eventually.of_forall fun y => ?_
+    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
+      continuous_snd.prodMk
+        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
+    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))
+
+/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
+theorem continuousOn_heat_integrand_extension {T M : ℝ}
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
+      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
+  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
+    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
+  apply hc.congr
+  intro p hp
+  dsimp only
+  by_cases hz : p.1 = 0
+  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
+  · rw [if_neg hz]
+    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
+    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
+      (fun y => f (p.2, y)) x
+    rwa [Real.sq_sqrt hpos.le] at he
+
+/-- The Duhamel boundary term converges to the forcing at the observation point. -/
+theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
+      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
+  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
+      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
+    (continuousOn_rescaled_heat_integral hf hM x).comp
+      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
+      (fun s hs => ⟨mem_univ _, hs⟩)
+  have hl := (hc t ht).tendsto.mono_left
+    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
+      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
+  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
+      f (t, x) := by
+    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
+  rw [hmass] at hl
+  apply hl.congr'
+  filter_upwards [self_mem_nhdsWithin] with s hs
+  have hpos : 0 < t - s := sub_pos.mpr hs.2
+  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
+    (fun y => f (s, y)) x
+  rw [Real.sq_sqrt hpos.le] at he
+  exact he.symm
+
+/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
+theorem duhamel_time_derivative_integral {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    IntervalIntegrable (fun s : ℝ =>
+      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
+    (∫ s in (0 : ℝ)..t,
+      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
+      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
+        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
+  have he : (fun s : ℝ =>
+      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
+      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
+    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
+  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
+  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
+  exact intervalIntegral.integral_congr_ae_restrict he
+
+/-- The specified Duhamel formula has zero initial value. -/
+theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
+    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
+  exact intervalIntegral.integral_same
+
+end Poincare.HeatDuhamelHeatEquation

exit_code=0
```


### run-040

```text
$ rg -n '^(theorem|lemma|nonrec theorem|noncomputable def|def|abbrev) (heatSolution|heatSolution_apply_swap|heatKernel_sq_smul|heatSolution_solves_heatEquation_of_bounded_measurable|vectorHeatSolution_solves_heatEquation_of_bounded_measurable|heatKernel_time_deriv_integral_hasDerivAt|hessian_duhamel_eq_integral|hessian_heatSolution_eq_cancelled_integral|integrableOn_cancelled_hessian_time|intervalIntegrable_hessian_majorant|norm_cancelled_hessian_integral_le|laplacian_eq_iteratedFDeriv_orthonormalBasis|integral_comp_smul_of_nonneg|continuousOn_of_dominated|integral_finsetSum|integral_congr_ae_restrict|ContinuousLinearMap.intervalIntegral_apply|MeasureTheory.Integrable.apply_continuousLinearMap|ContinuousOn.comp_continuous|ContinuousOn.comp|ContinuousOn.congr|Tendsto.congr|integral_same|basisFun|sq_sqrt|continuous_sqrt|sqrt_pos)( |\b)' Poincare/Global .lake/packages/mathlib/Mathlib
Poincare/Global/VectorHeatCauchy.lean:272:theorem vectorHeatSolution_solves_heatEquation_of_bounded_measurable
Poincare/Global/HeatKernelIntegral.lean:87:def heatSolution (t : ℝ) (f : E → ℝ) : E → ℝ :=
Poincare/Global/BoundedUniformContinuousHeat.lean:135:theorem heatKernel_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
Poincare/Global/HeatApproxIdentity.lean:75:theorem heatSolution_apply_swap (t : ℝ) (f : E → ℝ) (x : E) :
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:81:theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:124:theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:158:theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:202:theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
Poincare/Global/HeatCauchyNext2.lean:870:theorem heatSolution_solves_heatEquation_of_bounded_measurable
Poincare/Global/HeatCauchyFinal.lean:308:theorem heatKernel_time_deriv_integral_hasDerivAt {t C : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:385:theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:95:theorem continuous_sqrt : Continuous sqrt := sqrt.continuous
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:126:theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:178:theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:276:theorem sq_sqrt' : √x ^ 2 = max x 0 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:286:theorem sqrt_pos : 0 < √x ↔ 0 < x :=
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:158:lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:796:noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/StdBasis.lean:121:noncomputable def basisFun : Basis η R (η → R) :=
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:174:theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:1167:def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:648:lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:368:theorem ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn g f s) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:495:theorem ContinuousOn.comp {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:501:theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:523:theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
.lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean:101:theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
.lake/packages/mathlib/Mathlib/Order/Filter/Tendsto.lean:109:theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:248:theorem integral_finsetSum {ι} (s : Finset ι) {f : ι → α → G} (hf : ∀ i ∈ s, Integrable (f i) μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:462:theorem continuousOn_of_dominated {F : X → α → G} {bound : α → ℝ} {s : Set X}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:671:theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:768:nonrec theorem integral_finsetSum {ι} {s : Finset ι} {f : ι → ℝ → E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1220:theorem integral_congr_ae_restrict {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:114:theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1207:theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α → H →SL[σ] E}

exit_code=0
```


### run-041

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/APIs.lean
/tmp/heat-equation-evidence/APIs.lean:1:0: error: object file '/private/tmp/poincare-workers/heat-duhamel-heat-equation/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.olean' of module Mathlib.Analysis.Calculus.ParametricIntervalIntegral does not exist

exit_code=1
```


### run-042

```text
$ LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.Calculus.ParametricIntervalIntegral
✔ [2570/2570] Built Mathlib.Analysis.Calculus.ParametricIntervalIntegral (1.9s)
Build completed successfully (2570 jobs).

exit_code=0
```


### run-043

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-equation-evidence/APIs.lean
intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le.{u_1, u_2} {𝕜 : Type u_1} [RCLike 𝕜] {μ : Measure ℝ}
  {E : Type u_2} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {a b : ℝ} {bound : ℝ → ℝ} {F F' : 𝕜 → ℝ → E}
  {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ (x : 𝕜) in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
  (hF_int : IntervalIntegrable (F x₀) μ a b) (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
  (h_bound : ∀ᵐ (t : ℝ) ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t) (bound_integrable : IntervalIntegrable bound μ a b)
  (h_diff : ∀ᵐ (t : ℝ) ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x) :
  IntervalIntegrable (F' x₀) μ a b ∧
    HasDerivAt (fun x => ∫ (t : ℝ) in a..b, F x t ∂μ) (∫ (t : ℝ) in a..b, F' x₀ t ∂μ) x₀
intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right.{u_3} {E : Type u_3} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {c : E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
  [intervalIntegral.FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b) volume)
  (hb : Filter.Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) : HasDerivWithinAt (fun u => ∫ (x : ℝ) in a..u, f x) c s b

exit_code=0
```


### run-044

```text
$ git diff --check

exit_code=0
```


## Failed probe sources

These are the captured source files for failed Lean elaborations. They are
report evidence only; none is installed as a project module.


<details>
<summary>run-001: Probe.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation
open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian
#check EuclideanSpace.basisFun
#check InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
#check intervalIntegral.integral_apply
#check ContinuousLinearMap.intervalIntegral_comp_comm
#check Integrable.clm_apply
#check Poincare.heatSolution_hasDerivAt
#print axioms Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral
example (f : Poincare.ClosedSmoothModel 3 → ℝ) (x : Poincare.ClosedSmoothModel 3) :
    (Δ f) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply]
```

</details>


<details>
<summary>run-005: source-005-Dependencies.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

end Poincare.HeatDuhamelHeatEquation
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
#print axioms Poincare.HeatDuhamelHeatEquation.instNormedAddCommGroupContinuousLinearMap
```

</details>


<details>
<summary>run-013: source-013-Dependencies.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  apply IntervalIntegrable.sum
  intro i _
  exact ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
    (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩

end Poincare.HeatDuhamelHeatEquation

#print axioms Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian
```

</details>


<details>
<summary>run-021: source-021-Dependencies.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial (E := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable (E := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

end Poincare.HeatDuhamelHeatEquation

#print axioms Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_duhamel_eq_integral
#print axioms Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand
#print axioms Poincare.HeatDuhamelHeatEquation.heatSolution_sq
#print axioms Poincare.HeatDuhamelHeatEquation.continuousOn_rescaled_heat_integral
```

</details>


<details>
<summary>run-027: source-027-Dependencies.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

end Poincare.HeatDuhamelHeatEquation

#print axioms Poincare.HeatDuhamelHeatEquation.instHessianNormedAddCommGroup
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_hessian
#print axioms Poincare.HeatDuhamelHeatEquation.intervalIntegrable_heat_laplacian
#print axioms Poincare.HeatDuhamelHeatEquation.laplacian_duhamel_eq_integral
#print axioms Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand
#print axioms Poincare.HeatDuhamelHeatEquation.heatSolution_sq
#print axioms Poincare.HeatDuhamelHeatEquation.continuousOn_rescaled_heat_integral
#print axioms Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension
```

</details>


<details>
<summary>run-033: source-033-RemainingStep.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

/-- The specified Duhamel formula has zero initial value. -/
theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
  exact intervalIntegral.integral_same

end Poincare.HeatDuhamelHeatEquation

namespace Poincare.HeatDuhamelHeatEquation
local notation "E" => Poincare.ClosedSmoothModel 3

example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x : E, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    HasDerivWithinAt (fun r : ℝ => u r x)
      (f (t, x) + ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u t)) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (Icc 0 T) t := by
  intro α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK
  dsimp only
  refine ⟨fun x => duhamel_zero f x, ?_⟩
  intro t ht x
  rw [← laplacian_eq_hessian_trace]
  rw [← (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).2]
  have hinterior := (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).1
  have hboundary := tendsto_heat_integrand_diagonal ht hf hM x
  have hpointwise := fun s (hs : s ∈ Ioo 0 t) =>
    hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x
  trace_state

end Poincare.HeatDuhamelHeatEquation
```

</details>


<details>
<summary>run-036: source-036-HeatDuhamelHeatEquation.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

/-- The specified Duhamel formula has zero initial value. -/
theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
  exact intervalIntegral.integral_same

end Poincare.HeatDuhamelHeatEquation
```

</details>


<details>
<summary>run-036: source-036-APIs.lean</summary>

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

/-- The specified Duhamel formula has zero initial value. -/
theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
  exact intervalIntegral.integral_same

end Poincare.HeatDuhamelHeatEquation

#check intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
#check intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
```

</details>


<details>
<summary>run-041: source-041-APIs.lean</summary>

```lean
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Poincare.Global.HeatDuhamelHessianDifferentiation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace Interval Laplacian

namespace Poincare.HeatDuhamelHeatEquation

local notation "E" => Poincare.ClosedSmoothModel 3
local instance instHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation

/-- The Euclidean Laplacian is the coordinate trace of the actual Hessian. -/
theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
    (Δ g) x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ g) x
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply]

/-- The actual heat Hessian is integrable in the forcing time up to the diagonal. -/
theorem intervalIntegrable_heat_hessian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  apply (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hsT, mem_univ y⟩)
  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm

/-- Taking the trace preserves the time integrability supplied by cancellation. -/
theorem intervalIntegrable_heat_laplacian {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) volume 0 t := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  simp_rw [laplacian_eq_hessian_trace]
  have hd (i : Fin 3) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
      volume 0 t :=
    ⟨(hi.1.apply_continuousLinearMap _).apply_continuousLinearMap _,
      (hi.2.apply_continuousLinearMap _).apply_continuousLinearMap _⟩
  simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hd i)

/-- The Laplacian passes through the Duhamel time integral. -/
theorem laplacian_duhamel_eq_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
      heatSolution (t - s) (fun y => f (s, y)) z)) x =
      ∫ s in (0 : ℝ)..t, (Δ (heatSolution (t - s) (fun y => f (s, y)))) x := by
  have hi := intervalIntegrable_heat_hessian hα hα1 ht hf hM hK x
  have he : (∫ s in (0 : ℝ)..t, ∫ y : E,
      (f (s, x - y) - f (s, x)) • Hess (t - s) y) =
      ∫ s in (0 : ℝ)..t,
        fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hc : Continuous (fun y : E => f (s, y)) :=
      hf.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hsT, mem_univ y⟩)
    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
  have hv (v : E) : IntervalIntegrable (fun s : ℝ =>
      fderiv ℝ (fderiv ℝ (heatSolution (t - s) (fun y => f (s, y)))) x v) volume 0 t :=
    ⟨hi.1.apply_continuousLinearMap v, hi.2.apply_continuousLinearMap v⟩
  simp_rw [laplacian_eq_hessian_trace]
  rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, he]
  simp_rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply (hv _)]
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ⟨(hv _).1.apply_continuousLinearMap _, (hv _).2.apply_continuousLinearMap _⟩

/-- Away from the diagonal, the integrand time derivative is its spatial Laplacian. -/
theorem hasDerivAt_heat_integrand {T t s M : ℝ} (hs : s ∈ Icc 0 T) (hst : s < t)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r, y)| ≤ M) (x : E) :
    HasDerivAt (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x)
      ((Δ (heatSolution (t - s) (fun y => f (s, y)))) x) t := by
  have hc : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs, mem_univ y⟩)
  have hb : ∀ y : E, ‖f (s, y)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using hM s hs
  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
    hc.aestronglyMeasurable hb x
  have hd' : DifferentiableAt ℝ
      (fun r : ℝ => heatSolution r (fun y => f (s, y)) x) (t - s) := by
    simpa only [heatSolution_apply_swap] using hd.differentiableAt
  have hp := hd'.hasDerivAt
  rw [heatSolution_solves_heatEquation_of_bounded_measurable
    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)

/-- Scaling transfers the heat convolution to the fixed unit-time Gaussian. -/
theorem heatSolution_sq (a : ℝ) (ha : 0 < a) (g : E → ℝ) (x : E) :
    heatSolution (a ^ 2) g x = ∫ y : E, heatKernel 1 y * g (x - a • y) := by
  rw [heatSolution_apply]
  have hc := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun y : E => heatKernel (a ^ 2) y * g (x - y)) a (hR := ha.le)
  simp only [heatKernel_sq_smul a ha, ClosedSmoothModel, finrank_euclideanSpace_fin,
    smul_eq_mul, mul_assoc, integral_const_mul] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne')) hc.symm

/-- The rescaled integral is jointly continuous in elapsed time and forcing time. -/
theorem continuousOn_rescaled_heat_integral {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ y : E,
      heatKernel 1 y * f (p.2, x - Real.sqrt p.1 • y)) (univ ×ˢ Icc 0 T) := by
  apply continuousOn_of_dominated (bound := fun y : E => heatKernel 1 y * M)
  · intro p hp
    have hc : Continuous (fun y : E => f (p.2, x - Real.sqrt p.1 • y)) :=
      hf.comp_continuous
        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
        (fun y => ⟨hp.2, mem_univ _⟩)
    exact ((contDiff_heatKernel_spatial («E» := E) 1).continuous.mul hc).aestronglyMeasurable
  · intro p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => (p.2, x - Real.sqrt p.1 • y)) :=
      continuous_snd.prodMk
        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))

/-- Giving the heat convolution its initial value makes it jointly continuous at zero. -/
theorem continuousOn_heat_integrand_extension {T M : ℝ}
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    ContinuousOn (fun p : ℝ × ℝ => if p.1 = 0 then f (p.2, x)
      else heatSolution p.1 (fun y => f (p.2, y)) x) (Ici 0 ×ˢ Icc 0 T) := by
  have hc := (continuousOn_rescaled_heat_integral hf hM x).mono
    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
  apply hc.congr
  intro p hp
  dsimp only
  by_cases hz : p.1 = 0
  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  · rw [if_neg hz]
    have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
    have he := heatSolution_sq (Real.sqrt p.1) (Real.sqrt_pos.mpr hpos)
      (fun y => f (p.2, y)) x
    rwa [Real.sq_sqrt hpos.le] at he

/-- The Duhamel boundary term converges to the forcing at the observation point. -/
theorem tendsto_heat_integrand_diagonal {T t M : ℝ} (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
    Filter.Tendsto (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x)
      (𝓝[Ico 0 t] t) (𝓝 (f (t, x))) := by
  have hc : ContinuousOn (fun s : ℝ => ∫ y : E,
      heatKernel 1 y * f (s, x - Real.sqrt (t - s) • y)) (Icc 0 T) :=
    (continuousOn_rescaled_heat_integral hf hM x).comp
      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩)
  have hl := (hc t ht).tendsto.mono_left
    (nhdsWithin_mono t (show Ico 0 t ⊆ Icc 0 T from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.2⟩))
  have hmass : (∫ y : E, heatKernel 1 y * f (t, x - Real.sqrt (t - t) • y)) =
      f (t, x) := by
    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
  rw [hmass] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hpos : 0 < t - s := sub_pos.mpr hs.2
  have he := heatSolution_sq (Real.sqrt (t - s)) (Real.sqrt_pos.mpr hpos)
    (fun y => f (s, y)) x
  rw [Real.sq_sqrt hpos.le] at he
  exact he.symm

/-- The interior time derivative is integrable and its integral is the Duhamel Laplacian. -/
theorem duhamel_time_derivative_integral {α T t M K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    IntervalIntegrable (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) volume 0 t ∧
    (∫ s in (0 : ℝ)..t,
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =
      (Δ (fun z : E => ∫ s in (0 : ℝ)..t,
        heatSolution (t - s) (fun y => f (s, y)) z)) x := by
  have he : (fun s : ℝ =>
      deriv (fun r : ℝ => heatSolution (r - s) (fun y => f (s, y)) x) t) =ᵐ[volume.restrict (Ι 0 t)]
      (fun s : ℝ => (Δ (heatSolution (t - s) (fun y => f (s, y)))) x) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hasDerivAt_heat_integrand ⟨hs.1.le, hs.2.le.trans ht.2⟩ hs.2 hf hM x).deriv
  refine ⟨(intervalIntegrable_heat_laplacian hα hα1 ht hf hM hK x).congr_ae he.symm, ?_⟩
  rw [laplacian_duhamel_eq_integral hα hα1 ht hf hM hK x]
  exact intervalIntegral.integral_congr_ae_restrict he

/-- The specified Duhamel formula has zero initial value. -/
theorem duhamel_zero (f : ℝ × E → ℝ) (x : E) :
    (∫ s in (0 : ℝ)..0, heatSolution (0 - s) (fun y => f (s, y)) x) = 0 := by
  exact intervalIntegral.integral_same

end Poincare.HeatDuhamelHeatEquation

#check intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
#check intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right
```

</details>


## Dependency probe generator

```python
import pathlib,re,subprocess,sys
p=pathlib.Path('Poincare/Global/HeatDuhamelHeatEquation.lean')
s=p.read_text()
names=['instHessianNormedAddCommGroup']+re.findall(r'^theorem (\w+)',s,re.M)
pth=pathlib.Path('/tmp/heat-equation-evidence/Dependencies.lean')
pth.write_text(s+'\n'+'\n'.join('#print axioms Poincare.HeatDuhamelHeatEquation.'+n for n in names)+'\n')
subprocess.run(['python3','/tmp/heat-equation-evidence/run.py',f'LEAN_NUM_THREADS=1 lake env lean {pth}'])
```
