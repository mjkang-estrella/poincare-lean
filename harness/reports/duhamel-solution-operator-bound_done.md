# Duhamel solution operator bound: all four groups proved

Date: 2026-09-11. Branch: `worker/duhamel-solution-operator-bound`.

Base: `d87c6cee6fdf4413582988c7eca3ca4ae236a349`. Verified proof head: `4fd8d6fdc157e48e2071f59f5e59810611f236f3`.

Toolchain: `leanprover/lean4:v4.30.0-rc2`. Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.

## Result

`Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound` proves the frozen existential solution-graph bound. Its only spelling adjustment is `(«E» := E)` in named arguments, because the local `E` notation otherwise causes a parser error. The final probe assigns the exact frozen proposition to the proved theorem.

All four groups are complete. There is no remaining resisting goal for this task. This is a worker result awaiting independent orchestrator review; it is not a claim that the Poincare conjecture is complete.

1. The time derivative satisfies the requested sup estimate and parabolic Holder estimate. Its value is `f + Δu`, and the proof explicitly carries `HasDerivWithinAt` on `Icc 0 T`, including both endpoints. The Laplacian trace is bounded by three times the Hessian operator norm.

2. The gradient satisfies the exact `2 M C1 sqrt(t)` sup estimate and a uniform parabolic Holder estimate. Spatial control uses bounded Lipschitz interpolation. For temporal control, reversing the Duhamel time integral keeps the kernel fixed on the shared interval. The forcing time increment gives `2 C1 K (t-s)^(alpha/2)`, and the tail gives `2 C1 M sqrt(t-s)`, bounded by `2 C1 M (t-s)^(alpha/2)` for `0 <= s <= t <= 1`. Their sum proves the stronger explicit ordered-time constant `2 C1 (M+K)`.

3. Values satisfy `|u(t,x)| <= t (M + 3 C K T^(alpha/2))`, the corresponding time Lipschitz estimate, and a uniform parabolic Holder estimate.

4. For every forcing in `Y`, its norm supplies the sup and Holder bounds. Positive Holder control supplies cylinder continuity. The four raw jets are extended with the cylinder indicator and passed to `ParabolicSolutionGraph.ofDerivatives`, which uses `ParabolicHolder.ofFunction` for each component. Spatial derivative relations are preserved on each full spatial slice; time derivatives are preserved within the interval. The graph norm is bounded by summing the four sup and Holder estimates.

In the assembly proof, the constant is `(1+3*V)+2*W+(1+3*C)+(1+3*D)+2*J+2*Q+A+B`, where `A` is the Hessian sup constant, `B` the Hessian Holder constant, `C` the time-derivative sup constant, `D` the time-derivative Holder constant, `V` the value time-bound constant, `W` the value Holder constant, `Q` the gradient Holder constant, and `J` the time-one gradient kernel norm integral. Every constant is chosen before `T` and `f`; the total is positive.

## Scope and verification

Exactly one new Lean file is delivered, plus this required report. Existing Lean files, `Poincare.lean`, frozen contracts, and `HANDOFF.md` were not edited. The task-specific file restriction overrides the general handoff-edit instruction. The supplied worker branch is retained as required by this task. The worktree was clean at the base, and its status, HEAD and full worktree inventory were inspected before editing. Required project context and the actual upstream definitions/imports were read.

Fifteen theorems were compiled and committed separately. The final module check exits 0 with no output. The token scan is empty and exits 1 as expected for no matches. Both the working-tree whitespace check and the complete base-to-proof-head whitespace check exit 0. Every new declaration has exactly `[propext, Classical.choice, Quot.sound]`. The exact frozen-type assignment exits 0. No root import or integration audit is claimed by this worker.

First action for the orchestrator: independently rerun `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean`, then replay the exact-type and dependency probe below against the recorded proof head.

## Actual gate output and commits

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```text
```

```sh
git diff --check
```

Exit: `0`.

```text
```

```sh
git diff --check d87c6cee6fdf4413582988c7eca3ca4ae236a349..HEAD
```

Exit: `0`.

```text
```

```sh
git status --short --branch
```

Exit: `0`.

```text
## worker/duhamel-solution-operator-bound
```

```sh
git log --reverse '--format=%h %s' d87c6cee..HEAD
```

Exit: `0`.

```text
0c9b8dad Prove the three dimensional Hessian trace norm bound
f06d1dd9 Bound the Duhamel time derivative including both endpoints
b5e5b0c2 Prove the parabolic Holder bound for the Duhamel time derivative
7b9122cc Integrate the gradient kernel to bound the Duhamel gradient
07dd0f91 Bound Duhamel values and temporal value increments
bcc42cfd Prove bounded Lipschitz to Holder interpolation
13a85faf Prove uniform spatial Holder control of the Duhamel gradient
ca96d680 Prove the parabolic Holder estimate for Duhamel values
b3b40508 Bound heat gradient differences by forcing differences
45a00e26 Reverse the Duhamel gradient time integral
70205e52 Integrate inverse square root majorants on nonnegative intervals
7eeb1eb3 Prove the Duhamel gradient time Holder estimate
f36c75e0 Prove full parabolic Holder control of the Duhamel gradient
5c8bf8ba Derive cylinder continuity from parabolic Holder control
4fd8d6fd Assemble the bounded Duhamel solution graph for Holder forcing
```

```sh
git diff --stat d87c6cee..HEAD
```

Exit: `0`.

```text
 Poincare/Global/DuhamelSolutionOperatorBound.lean | 648 ++++++++++++++++++++++
 1 file changed, 648 insertions(+)
```

```sh
cat lean-toolchain
```

Exit: `0`.

```text
leanprover/lean4:v4.30.0-rc2
```

```sh
git -C .lake/packages/mathlib rev-parse HEAD
```

Exit: `0`.

```text
7175569c842f9164564bd76ff8b207e7b4705522
```

```sh
rg -n '^theorem ' Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```text
20:theorem abs_trace_le (A : E →L[ℝ] E →L[ℝ] ℝ) :
34:theorem duhamel_time_derivative_bound :
67:theorem duhamel_time_derivative_holder :
109:theorem duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Icc 0 T)
138:theorem duhamel_value_time_estimates :
172:theorem holder_of_bounded_lipschitz {F : Type*} [NormedAddCommGroup F]
194:theorem duhamel_gradient_spatial_holder :
234:theorem duhamel_value_parabolic_holder :
302:theorem gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
323:theorem duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Icc 0 T)
336:theorem norm_integral_inverse_sqrt_le {F : Type*} [NormedAddCommGroup F]
367:theorem duhamel_gradient_time_holder_of_le {α T s t M K : ℝ}
438:theorem duhamel_gradient_parabolic_holder :
490:theorem continuousOn_of_hasHolderBound {F : Type*} [NormedAddCommGroup F]
510:theorem exists_solution_graph_bound :
```

## Probe archive

Every Lean invocation is recorded below with its actual exit status and unabridged compiler output. Inputs are preserved as the full source for stand-alone probes, and a sequence of unified diffs for successive module checks. Applying the zero-context module diffs in order reconstructs every attempted source; use `git apply --unidiff-zero`. Empty context lines in the initial report draft triggered the staged whitespace check, so the embedded diffs were regenerated with zero context. Compiler outputs are unchanged. Failed attempts are retained, including parser, rewrite, inference and heartbeat diagnostics. Probes 026 and 029 print the remaining graph component declarations. Probe 030 appends the declaration dependency checks and exact frozen-type assignment to the final module.

### 001-prerequisites

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/duhamel-solution-probes/001-prerequisites.lean
```

Exit: `1`.

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation
import Poincare.Global.DuhamelParabolicHolderSeminorm
import Poincare.Global.MovingLimitLeibniz
import Poincare.Global.ParabolicHolderSpace
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.HeatDuhamelHeatEquation
#print Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound
#print Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel
#print Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel
#print Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral
#print Poincare.HeatDuhamelHessianDifferentiation.gradient_integral
#print Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral
#print Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le
#print Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time
#print Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time
#print Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
#print Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian
#print Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation
#print Poincare.ParabolicHolder.Y
#print Poincare.ParabolicHolder.parabolicDist
#print Poincare.ParabolicHolder.cylinder
#print Poincare.ParabolicHolder.HasHolderBound
#print Poincare.ParabolicHolder.ofFunction
#print Poincare.ParabolicHolder.norm_le_of_bounds
#print Poincare.ParabolicHolder.norm_eq
#print Poincare.ParabolicSolutionGraph.norm_eq
#print Poincare.ParabolicSolutionGraph.Graph
#print Poincare.ParabolicSolutionGraph.ofDerivatives
#print Poincare.ParabolicSolutionGraph.time_bound
#print Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
open Set MeasureTheory
open scoped Interval
namespace Poincare.DuhamelSolutionOperatorBound
local notation "E" => Poincare.ClosedSmoothModel 3
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y (E := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph (E := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder (E := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖)
end Poincare.DuhamelSolutionOperatorBound
```

Actual compiler output:

```text
theorem Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound : ∀ (α : ℝ),
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
                                        (Set.Ioo 0 t) MeasureTheory.volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : Poincare.ClosedSmoothModel 3),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2) :=
fun α hα hα1 =>
  let J :=
    ∫ (y : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α;
  Exists.intro (max 1 (J * (2 / α)))
    ⟨lt_of_lt_of_le zero_lt_one (le_max_left 1 (J * (2 / α))), fun T a a_1 f M K a_2 hK0 hf hM hK =>
      id
        ⟨fun x => intervalIntegral.integral_same, fun t ht x =>
          ⟨Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel hα hα1 ht hf hM hK,
            ⟨Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
              ⟨Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
                Eq.mpr
                  (id
                    (congrArg (fun _a => ‖_a‖ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2))
                      (Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x)))
                  (Trans.trans
                    (Trans.trans
                      (Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le hα hα1 ht.left
                        (fun s hs => hK s ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht.right⟩) x)
                      (Mathlib.Tactic.Ring.of_eq
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right J (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (K ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (J ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                        (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                    (Eq.symm
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a => α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                      Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                          (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                      (Eq.symm
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                        Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (J ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                            (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))))
                    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 (J * (2 / α))) hK0)
                      (Real.rpow_nonneg ht.left (α / 2))))⟩⟩⟩⟩⟩
theorem Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel : ∀ {α T t M K : ℝ},
  0 < α →
    α < 1 →
      t ∈ Set.Icc 0 T →
        ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
          ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
            (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
              (∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) →
                ContDiff ℝ 2 fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z :=
fun {α T t M K} hα hα1 ht {f} hf hM hK =>
  have hD :=
    funext fun z => HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z);
  have hDD :=
    funext fun z =>
      HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z);
  id
    (contDiff_succ_iff_fderiv.mpr
      ⟨fun z =>
        HasFDerivAt.differentiableAt (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z),
        ⟨of_eq_true
            (Eq.trans
              (Eq.trans
                (implies_congr (Eq.trans WithTop.one_ne_top._simp_2 (eq_false not_false))
                  (congrFun'
                    (congrArg (AnalyticOnNhd ℝ)
                      (funext fun z =>
                        congrFun'
                          (congrFun'
                            (congrFun'
                              (congrArg intervalIntegral
                                (funext fun s => Poincare.heatSolution_apply (t - s) (fun y => f (s, y)) z))
                              0)
                            t)
                          MeasureTheory.volume))
                    Set.univ))
                IsEmpty.forall_iff._simp_1)
              (eq_true True.intro)),
          Eq.mpr (id (congrArg (fun _a => ContDiff ℝ 1 _a) hD))
            (contDiff_one_iff_fderiv.mpr
              ⟨fun z =>
                HasFDerivAt.differentiableAt
                  (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z),
                Eq.mpr (id (congrArg (fun _a => Continuous _a) hDD))
                  (Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian hα hα1 ht hf hM hK)⟩)⟩⟩)
theorem Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            HasFDerivAt (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z)
              (∫ (s : ℝ) in 0..t, fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x) x :=
fun {T t M} ht {f} hf hM x =>
  let A := M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖;
  have hmem := fun s hs => ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht.right⟩;
  have hfc := fun s hs =>
    ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
      ⟨hmem s hs, Set.mem_univ y⟩;
  hasFDerivAt_integral_of_dominated_of_fderiv_le'' (of_eq_true Filter.univ_mem._simp_1)
    (Filter.Eventually.of_forall fun z =>
      Eq.mpr
        (id
          (congrArg
            (@MeasureTheory.AEStronglyMeasurable ℝ ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
              Real.measurableSpace Real.measurableSpace fun t_1 =>
              Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) z)
            (congrArg MeasureTheory.volume.restrict (Set.uIoc_of_le ht.left))))
        (IntervalIntegrable.aestronglyMeasurable
          (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht hf hM z)))
    (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht hf hM x)
    (Eq.mpr
      (id
        (congrArg
          (@MeasureTheory.AEStronglyMeasurable ℝ (Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
            ContinuousLinearMap.topologicalSpace Real.measurableSpace Real.measurableSpace fun s =>
            fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
          (congrArg MeasureTheory.volume.restrict (Set.uIoc_of_le ht.left))))
      (IntervalIntegrable.aestronglyMeasurable
        (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time ht hf hM x)))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ∀ᵐ (t_1 : ℝ) ∂MeasureTheory.volume.restrict _a,
              ∀ x ∈ Set.univ,
                ‖fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x‖ ≤ A * (t - t_1) ^ (-(1 / 2)))
          (Set.uIoc_of_le ht.left)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              ∀ᵐ (t_1 : ℝ) ∂_a,
                ∀ x ∈ Set.univ,
                  ‖fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x‖ ≤ A * (t - t_1) ^ (-(1 / 2)))
            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
          (Filter.univ_mem'
            (id fun s hs z a =>
              Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le (sub_pos.mpr hs.right)
                (Continuous.aestronglyMeasurable (hfc s hs)) (id (hM s (hmem s hs))) z)))))
    (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant t A)
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ∀ᵐ (t_1 : ℝ) ∂MeasureTheory.volume.restrict _a,
              ∀ x ∈ Set.univ,
                HasFDerivAt (fun x => Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) x)
                  (fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x) x)
          (Set.uIoc_of_le ht.left)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              ∀ᵐ (t_1 : ℝ) ∂_a,
                ∀ x ∈ Set.univ,
                  HasFDerivAt (fun x => Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) x)
                    (fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x) x)
            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
          (Filter.univ_mem'
            (id fun s hs z a =>
              DifferentiableAt.hasFDerivAt
                (HasFDerivAt.differentiableAt
                  (Poincare.heatSolution_hasFDerivAt (sub_pos.mpr hs.right) (Continuous.aestronglyMeasurable (hfc s hs))
                    (id (hM s (hmem s hs))) z)))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral : ∀ {α T t M K : ℝ},
  0 < α →
    α < 1 →
      t ∈ Set.Icc 0 T →
        ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
          ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
            (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
              (∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) →
                ∀ (x : Poincare.ClosedSmoothModel 3),
                  fderiv ℝ (fderiv ℝ fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z)
                      x =
                    ∫ (s : ℝ) in 0..t,
                      ∫ (y : Poincare.ClosedSmoothModel 3),
                        (f (s, x - y) - f (s, x)) •
                          (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y :=
fun {α T t M K} hα hα1 ht {f} hf hM hK x =>
  have hD :=
    funext fun z => HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z);
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          fderiv ℝ _a x =
            ∫ (s : ℝ) in 0..t,
              ∫ (y : Poincare.ClosedSmoothModel 3),
                (f (s, x - y) - f (s, x)) •
                  (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y)
        hD))
    (HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x))
theorem Poincare.HeatDuhamelHessianDifferentiation.gradient_integral : ∀ {t : ℝ},
  0 < t →
    ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y‖ =
      (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
        t ^ (-(1 / 2)) :=
fun {t} ht =>
  have h := Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq (√t) (Real.sqrt_pos.mpr ht);
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a =
            (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
              t ^ (-(1 / 2)))
        (Eq.mp
          (congrArg
            (fun _a =>
              ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) _a y‖ =
                (√t)⁻¹ *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
            (Real.sq_sqrt (LT.lt.le ht)))
          h)))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            _a⁻¹ *
                ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖ =
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                t ^ (-(1 / 2)))
          (Real.sqrt_eq_rpow t)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              (t ^ (1 / 2))⁻¹ *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖ =
                (∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  _a)
            (Real.rpow_neg (LT.lt.le ht) (1 / 2))))
        (Mathlib.Tactic.Ring.of_eq
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.inv_congr
              (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (1 / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.inv_single
                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (t ^ (1 / 2))⁻¹)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                  (Eq.symm
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                    Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))))
            (Mathlib.Tactic.Ring.Common.atom_pf
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
              rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                    (∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                            ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1 +
                  0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
              rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.inv_congr
              (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (1 / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.inv_single
                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (t ^ (1 / 2))⁻¹)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                  (Eq.symm
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                    Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                    (∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                            ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0)))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral : ∀ {t M : ℝ},
  0 < t →
    ∀ {f : Poincare.ClosedSmoothModel 3 → ℝ},
      MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
        (∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            fderiv ℝ (Poincare.heatSolution t f) x =
              ∫ (y : Poincare.ClosedSmoothModel 3),
                f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y :=
fun {t M} ht {f} hf hM x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a =
            ∫ (y : Poincare.ClosedSmoothModel 3),
              f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y)
        (HasFDerivAt.fderiv (Poincare.heatSolution_hasFDerivAt ht hf hM x))))
    (have hc :=
      MeasureTheory.integral_sub_left_eq_self
        (fun y => f y • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t (x - y)) MeasureTheory.volume x;
    id
      (Eq.mp
        (congrArg
          (Eq (∫ (x_1 : Poincare.ClosedSmoothModel 3), f x_1 • fderiv ℝ (fun z => Poincare.heatKernel t z) (x - x_1)))
          (congrArg (MeasureTheory.integral MeasureTheory.volume)
            (funext fun x_1 =>
              congrArg (HSMul.hSMul (f (x - x_1)))
                (congrArg (fderiv ℝ fun z => Poincare.heatKernel t z) (sub_sub_cancel x x_1)))))
        (Eq.symm hc)))
theorem Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le : ∀ {t M : ℝ},
  0 < t →
    ∀ {f : Poincare.ClosedSmoothModel 3 → ℝ},
      MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
        (∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            ‖fderiv ℝ (Poincare.heatSolution t f) x‖ ≤
              (M *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                t ^ (-(1 / 2)) :=
fun {t M} ht {f} hf hM x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          ‖_a‖ ≤
            (M *
                ∫ (y : Poincare.ClosedSmoothModel 3),
                  ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
              t ^ (-(1 / 2)))
        (Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral ht hf hM x)))
    (Trans.trans
      (MeasureTheory.norm_integral_le_of_norm_le
        (MeasureTheory.Integrable.const_mul
          (MeasureTheory.Integrable.norm (Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient ht)) M)
        (Filter.Eventually.of_forall fun y =>
          LE.le.trans
            (Poincare.norm_real_smul_continuousLinearMap_one_le (f (x - y))
              ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y))
            (mul_le_mul_of_nonneg_right (hM (x - y))
              (norm_nonneg ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y)))))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a =
                (M *
                    ∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  t ^ (-(1 / 2)))
            (MeasureTheory.integral_const_mul M fun y =>
              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y‖)))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                M * _a =
                  (M *
                      ∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                    t ^ (-(1 / 2)))
              (Poincare.HeatDuhamelHessianDifferentiation.gradient_integral ht)))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  M *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                        t ^ (-(1 / 2))) =
                    _a)
                (mul_assoc M
                  (∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                  (t ^ (-(1 / 2))))))
            (Eq.refl
              (M *
                ((∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  t ^ (-(1 / 2)))))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          Continuous fun p => fderiv ℝ (Poincare.heatSolution (t - ↑p.1) fun y => f (↑p.1, y)) p.2 :=
fun {T t M} ht {f} hf hM =>
  have hmem := fun s => ⟨LT.lt.le s.property.left, LE.le.trans (LT.lt.le s.property.right) ht.right⟩;
  have hs := Continuous.comp continuous_subtype_val continuous_fst;
  have ha := Continuous.comp Real.continuous_sqrt (Continuous.sub continuous_const hs);
  have hapos := fun p => Real.sqrt_pos.mpr (sub_pos.mpr p.1.property.right);
  have hunit :=
    ContDiff.continuous
      (ContDiff.fderiv_right (Poincare.contDiff_heatKernel_spatial 1)
        (of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg LE.le
                  (Mathlib.Meta.NormNum.IsNat.to_eq
                    (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd)
                      (Mathlib.Meta.NormNum.isNat_ofNat (WithTop ℕ∞) Nat.cast_zero)
                      (Mathlib.Meta.NormNum.isNat_ofNat (WithTop ℕ∞) Nat.cast_one) (Eq.refl 1))
                    Nat.cast_one))
                ⊤)
              le_top._simp_2)
            (eq_true True.intro))));
  have hn :=
    MeasureTheory.continuous_of_dominated
      (fun p =>
        Continuous.aestronglyMeasurable
          (Continuous.smul
            (ContinuousOn.comp_continuous hf
              (Continuous.prodMk continuous_const
                (Continuous.sub continuous_const (Continuous.smul continuous_const continuous_id)))
              fun y => ⟨hmem p.1, Set.mem_univ (p.1.1, p.2 - √(t - ↑p.1) • id y).2⟩)
            hunit))
      (fun p =>
        Filter.Eventually.of_forall fun y =>
          LE.le.trans
            (Poincare.norm_real_smul_continuousLinearMap_one_le (f (↑p.1, p.2 - √(t - ↑p.1) • y))
              ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y))
            (mul_le_mul_of_nonneg_right (hM (↑p.1) (hmem p.1) (p.2 - √(t - ↑p.1) • y))
              (norm_nonneg ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y))))
      (MeasureTheory.Integrable.const_mul
        (MeasureTheory.Integrable.norm (Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient zero_lt_one)) M)
      (Filter.Eventually.of_forall fun y =>
        Continuous.smul
          (ContinuousOn.comp_continuous hf
            (Continuous.prodMk hs (Continuous.sub continuous_snd (Continuous.smul ha continuous_const))) fun p =>
            ⟨hmem p.1, Set.mem_univ (↑p.1, p.2 - √(t - ↑p.1) • y).2⟩)
          continuous_const);
  Continuous.congr (Continuous.smul (Continuous.inv₀ ha fun p => LT.lt.ne' (hapos p)) hn) fun p =>
    have hfc :=
      ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
        ⟨hmem p.1, Set.mem_univ y⟩;
    Eq.mpr
      (id
        (congrArg
          (fun _a =>
            (√(t - ↑p.1))⁻¹ •
                ∫ (y : Poincare.ClosedSmoothModel 3),
                  f (↑p.1, p.2 - √(t - ↑p.1) • y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y =
              _a)
          (Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.right)
            (Continuous.aestronglyMeasurable hfc) (id (hM (↑p.1) (hmem p.1))) p.2)))
      (have h :=
        Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq (√(t - ↑p.1)) (hapos p)
          (fun y => f (↑p.1, y)) p.2;
      Eq.symm
        (Eq.mp
          (congrArg
            (fun _a =>
              ∫ (y : Poincare.ClosedSmoothModel 3),
                  f (↑p.1, p.2 - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) _a y =
                (√(t - ↑p.1))⁻¹ •
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    f (↑p.1, p.2 - √(t - ↑p.1) • y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y)
            (Real.sq_sqrt (LT.lt.le (sub_pos.mpr p.1.property.right))))
          h))
theorem Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            IntervalIntegrable (fun s => fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
              MeasureTheory.volume 0 t :=
fun {T t M} ht {f} hf hM x =>
  have hc :=
    Continuous.comp (Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time ht hf hM)
      (Continuous.prodMk continuous_id continuous_const);
  let A := M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖;
  have hi :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.left enorm_ne_top enorm_ne_top).mp
      (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant t A);
  Eq.mpr
    (id
      (congrArg (fun _a => _a)
        (propext (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.left enorm_ne_top enorm_ne_top))))
    (Eq.mpr (id (congrArg (fun _a => _a) (propext (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo))))
      (MeasureTheory.Integrable.mono'
        (Eq.mp (congrArg (fun _a => _a) (propext (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo)))
          hi)
        (Continuous.aestronglyMeasurable hc)
        (Filter.Eventually.of_forall fun s =>
          have hmem := ⟨LT.lt.le s.property.left, LE.le.trans (LT.lt.le s.property.right) ht.right⟩;
          have hfc :=
            ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
              ⟨hmem, Set.mem_univ y⟩;
          Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le (sub_pos.mpr s.property.right)
            (Continuous.aestronglyMeasurable hfc) (id (hM (↑s) hmem)) x)))
theorem Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder : ∀ (α : ℝ),
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
                                  C * K * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun α hα hα1 =>
  Exists.casesOn (Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1) fun C₁ h =>
    And.casesOn h fun hC₁ hspace =>
      Exists.casesOn (Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1) fun C₂ h =>
        And.casesOn h fun hC₂ htime =>
          Exists.intro (C₁ + C₂)
            ⟨add_pos hC₁ hC₂, fun T hT hT1 f M K hM hK hf hfM hfK =>
              id fun p hp q hq =>
                let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.left p.2 q.2;
                have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.left q.1 hq.left q.2;
                have hspow :=
                  Real.rpow_le_rpow (norm_nonneg (p.2 - q.2)) (le_add_of_nonneg_right (Real.sqrt_nonneg |p.1 - q.1|))
                    (LT.lt.le hα);
                have htpow :=
                  Trans.trans
                    (Eq.mpr (id (congrArg (fun _a => |p.1 - q.1| ^ (α / 2) = _a ^ α) (Real.sqrt_eq_rpow |p.1 - q.1|)))
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => |p.1 - q.1| ^ (α / 2) = _a)
                            (Eq.symm (Real.rpow_mul (abs_nonneg (p.1 - q.1)) (1 / 2) α))))
                        ((fun {α β γ} [HPow α β γ] a a_1 e_a =>
                            Eq.rec (motive := fun a_2 e_a => ∀ (a_3 a_4 : β), a_3 = a_4 → a ^ a_3 = a_2 ^ a_4)
                              (fun a_2 a_3 e_a => e_a ▸ Eq.refl (a ^ a_2)) e_a)
                          |p.1 - q.1| |p.1 - q.1| (Eq.refl |p.1 - q.1|) (α / 2) (1 / 2 * α)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                          (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 2 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                          (Eq.refl (Nat.mul 1 1)) (Eq.refl 2)))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 1 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 2 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 1 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                              (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                                (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                              (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (NNRat.rawCast 1 2))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0))))))))
                    (Real.rpow_le_rpow (Real.sqrt_nonneg |p.1 - q.1|) (le_add_of_nonneg_left (norm_nonneg (p.2 - q.2)))
                      (LT.lt.le hα));
                Trans.trans
                  (Trans.trans
                    (Trans.trans
                      (Eq.mp
                        (congrFun'
                          (congrArg LE.le
                            (congrArg norm
                              (sub_add_sub_cancel (fderiv ℝ (fderiv ℝ (u p.1)) p.2) (fderiv ℝ (fderiv ℝ (u p.1)) q.2)
                                (fderiv ℝ (fderiv ℝ (u q.1)) q.2))))
                          (‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
                            ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖))
                        (norm_add_le (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
                          (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)))
                      (add_le_add hs ht))
                    (add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg (LT.lt.le hC₁) hK))
                      (mul_le_mul_of_nonneg_left htpow (mul_nonneg (LT.lt.le hC₂) hK))))
                  (Mathlib.Tactic.Ring.of_eq
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₁ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₁ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₁ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                    (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 *
                                  (K ^ Nat.rawCast 1 *
                                    ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                      Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C₁ ^ Nat.rawCast 1 *
                                (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₂ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₂ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                    (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                    (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (C₁ ^ Nat.rawCast 1 *
                          (K ^ Nat.rawCast 1 *
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (K ^ Nat.rawCast 1 *
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₁ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₁ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₁ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf C₂ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₂ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C₁ ^ Nat.rawCast 1 *
                                (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                    (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (C₁ ^ Nat.rawCast 1 *
                            (K ^ Nat.rawCast 1 *
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))))⟩
theorem Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian : ∀ (α : ℝ),
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
                              (fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K) :=
fun α hα hα1 =>
  Exists.casesOn (Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1) fun C h =>
    And.casesOn h fun hC hbound => Exists.intro C ⟨hC, hbound⟩
theorem Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation : ∀ (α : ℝ),
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
                                (Set.Icc 0 T) t :=
fun α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK =>
  id
    ⟨fun x => Poincare.HeatDuhamelHeatEquation.duhamel_zero f x, fun t ht x =>
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, Poincare.heatSolution (r - s) (fun y => f (s, y)) x)
                (f (t, x) + _a) (Set.Icc 0 T) t)
            (Eq.symm
              (Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
                (fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x) x))))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, Poincare.heatSolution (r - s) (fun y => f (s, y)) x)
                  (f (t, x) + _a) (Set.Icc 0 T) t)
              (Eq.symm (Poincare.HeatDuhamelHeatEquation.duhamel_time_derivative_integral hα hα1 ht hf hM hK x).right)))
          (let F := fun r s => if r - s = 0 then f (s, x) else Poincare.heatSolution (r - s) (fun y => f (s, y)) x;
          have hc :=
            ContinuousOn.comp (Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension hf hM x)
              (Continuous.continuousOn
                (Continuous.prodMk (Continuous.sub continuous_fst continuous_snd) continuous_snd))
              fun p hp => ⟨sub_nonneg.mpr hp.right.right, hp.left⟩;
          have hd := fun s hs r hr =>
            have hd0 :=
              DifferentiableAt.hasDerivAt
                (HasDerivAt.differentiableAt
                  (Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand hs hr.left hf hM x));
            HasDerivAt.congr_of_eventuallyEq hd0
              (Filter.mp_mem (Ioi_mem_nhds hr.left)
                (Filter.univ_mem'
                  (id fun ρ hρ =>
                    of_eq_true
                      (Eq.trans
                        (congrFun'
                          (congrArg Eq
                            (Eq.trans
                              (congrFun'
                                (congrFun'
                                  (funext fun r =>
                                    funext fun s =>
                                      ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                        Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                  ρ)
                                s)
                              ((fun x_0 x_1 x_2 x_3 =>
                                  (fun x_0 x_1 x_2 x_3 =>
                                      if_neg
                                        (ne_of_gt
                                          (sub_pos.mpr
                                            (have this := hρ;
                                            this))))
                                    x_0 x_1 x_2 x_3)
                                ((ρ - s).decidableEq 0) ℝ (f (s, x))
                                (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))))
                          (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))
                        (eq_self (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))))));
          Exists.casesOn (Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound hα hα1 hK0 hf hM hK x)
            fun C h =>
            And.casesOn h fun hC hCb =>
              have hsolve :=
                Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit ht
                  (lt_of_not_ge fun a =>
                    Mathlib.Tactic.Linarith.lt_irrefl
                      (Eq.mp
                        (congrArg (fun _a => _a < 0)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.add_congr
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                    (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.zero_mul 0)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                                (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsInt.to_isNat
                                    (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                      (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                      (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                      (Eq.refl (Int.ofNat 0)))))
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                            (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                        (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                          (Eq.mp
                            (congrArg (fun _a => _a ≤ 0)
                              (Mathlib.Tactic.CancelDenoms.sub_subst
                                (Mathlib.Tactic.CancelDenoms.div_subst rfl
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                      (Mathlib.Meta.NormNum.isNNRat_div
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                rfl))
                            (Mathlib.Tactic.Linarith.mul_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le a)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false)))))))
                  (le_of_not_gt fun a =>
                    Mathlib.Tactic.Linarith.lt_irrefl
                      (Eq.mp
                        (congrArg (fun _a => _a < 0)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.add_congr
                              (Mathlib.Tactic.Ring.Common.add_congr
                                (Mathlib.Tactic.Ring.Common.sub_congr
                                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.sub_pf
                                    (Mathlib.Tactic.Ring.Common.neg_add
                                      (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                            (Eq.refl (Int.negOfNat 1)))))
                                      Mathlib.Tactic.Ring.Common.neg_zero)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                      (Eq.mpr
                                        (id
                                          (congrArg
                                            (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                    (Mathlib.Tactic.Ring.Common.sub_pf
                                      (Mathlib.Tactic.Ring.Common.neg_add
                                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                            (Eq.refl (Int.negOfNat 1))))
                                        Mathlib.Tactic.Ring.Common.neg_zero)
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                          (Eq.refl (Int.negOfNat 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_add
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                        (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 2).rawCast
                                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                                    (Mathlib.Tactic.Ring.Common.zero_mul
                                      ((Int.negOfNat 1).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((Int.negOfNat 2).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 2).rawCast
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
                                    (Mathlib.Tactic.Ring.Common.add_overlap_pf α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                            (Eq.refl (Int.ofNat 1))))))
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 2 + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                    (Eq.refl (Int.ofNat 0))))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                        (Eq.refl (Int.ofNat 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                            (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                        (Mathlib.Tactic.Linarith.add_neg
                          (Mathlib.Tactic.Linarith.add_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                            (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα1)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))))
                          (Eq.mp
                            (congrArg (fun _a => _a < 0)
                              (Mathlib.Tactic.CancelDenoms.sub_subst rfl
                                (Mathlib.Tactic.CancelDenoms.div_subst rfl
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                      (Mathlib.Meta.NormNum.isNNRat_div
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))))
                            (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt a)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false)))))))
                  hC hc
                  (of_eq_true
                    (Eq.trans
                      (congrFun'
                        (congrArg Eq
                          (Eq.trans
                            (congrFun'
                              (congrFun'
                                (funext fun r =>
                                  funext fun s =>
                                    ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                      Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                t)
                              t)
                            (Eq.trans
                              (ite_congr (Eq.trans (congrFun' (congrArg Eq (sub_self t)) 0) (eq_self 0))
                                (fun a => Eq.refl (f (t, x))) fun a =>
                                Poincare.heatSolution.congr_simp (t - t) 0 (sub_self t) (fun y => f (t, y))
                                  (fun y => f (t, y)) (Eq.refl fun y => f (t, y)) x x (Eq.refl x))
                              (if_true (f (t, x)) (Poincare.heatSolution 0 (fun y => f (t, y)) x)))))
                        (f (t, x)))
                      (eq_self (f (t, x)))))
                  hd hCb;
              HasDerivWithinAt.congr_of_mem hsolve
                (fun r hr =>
                  intervalIntegral.integral_congr_ae_restrict
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            (fun x_1 =>
                                Poincare.heatSolution (r - x_1) (fun y => f (x_1, y))
                                  x) =ᵐ[MeasureTheory.volume.restrict _a]
                              F r)
                          (Set.uIoc_of_le hr.left)))
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a => (fun x_1 => Poincare.heatSolution (r - x_1) (fun y => f (x_1, y)) x) =ᵐ[_a] F r)
                            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
                        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
                          (Filter.univ_mem'
                            (id fun s hs =>
                              of_eq_true
                                (Eq.trans
                                  (congrArg (Eq (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                    (Eq.trans
                                      (congrFun'
                                        (congrFun'
                                          (funext fun r =>
                                            funext fun s =>
                                              ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                                Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                          r)
                                        s)
                                      ((fun x_0 x_1 x_2 x_3 =>
                                          (fun x_0 x_1 x_2 x_3 => if_neg (ne_of_gt (sub_pos.mpr hs.right))) x_0 x_1 x_2
                                            x_3)
                                        ((r - s).decidableEq 0) ℝ (f (s, x))
                                        (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))))
                                  (eq_self (Poincare.heatSolution (r - s) (fun y => f (s, y)) x)))))))))
                ht))⟩
@[reducible] def Poincare.ParabolicHolder.Y.{u_1, u_3} : {E : Type u_1} →
  [NormedAddCommGroup E] →
    ℝ → ℝ → (F : Type u_3) → [inst : NormedAddCommGroup F] → [NormedSpace ℝ F] → Type (max u_1 u_3) :=
fun {E} [NormedAddCommGroup E] α T F [NormedAddCommGroup F] [NormedSpace ℝ F] =>
  ↥(Poincare.ParabolicHolder.holderSubmodule α T)
def Poincare.ParabolicHolder.parabolicDist.{u_1} : {E : Type u_1} → [NormedAddCommGroup E] → ℝ × E → ℝ × E → ℝ :=
fun {E} [NormedAddCommGroup E] p q => ‖p.2 - q.2‖ + √|p.1 - q.1|
def Poincare.ParabolicHolder.cylinder.{u_1} : {E : Type u_1} → ℝ → Set (ℝ × E) :=
fun {E} T => Set.Icc 0 T ×ˢ Set.univ
def Poincare.ParabolicHolder.HasHolderBound.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup E] → [NormedAddCommGroup F] → ℝ → Set (ℝ × E) → (ℝ × E → F) → ℝ → Prop :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] α S f K =>
  ∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * Poincare.ParabolicHolder.parabolicDist p q ^ α
def Poincare.ParabolicHolder.ofFunction.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} →
    [inst : NormedAddCommGroup E] →
      [inst_1 : NormedAddCommGroup F] →
        [inst_2 : NormedSpace ℝ F] →
          {α T : ℝ} →
            (f : ℝ × E → F) →
              (∀ p ∉ Poincare.ParabolicHolder.cylinder T, f p = 0) →
                (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖f p‖ ≤ M) →
                  (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K) →
                    Poincare.ParabolicHolder.Y α T F :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f hoff hb hh =>
  let v := ⟨f, ⋯⟩;
  let w := ⟨fun i => (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2), ⋯⟩;
  ⟨WithLp.toLp 1 (v, w), ⋯⟩
theorem Poincare.ParabolicHolder.norm_le_of_bounds.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F) {M K : ℝ},
  0 ≤ M →
    0 ≤ K →
      (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M) →
        Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f)) K →
          ‖f‖ ≤ M + K :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f {M K} hM hK hb hh =>
  Eq.mpr (id (congrArg (fun _a => _a ≤ M + K) (Poincare.ParabolicHolder.norm_eq_parts f)))
    (add_le_add
      (lp.norm_le_of_forall_le hM fun p =>
        if hp : p ∈ Poincare.ParabolicHolder.cylinder T then hb p hp
        else
          id
            (Eq.mpr
              (id
                (congrFun'
                  (congrArg LE.le (Eq.trans (congrArg norm (Poincare.ParabolicHolder.zero_off f hp)) norm_zero)) M))
              hM))
      (lp.norm_le_of_forall_le hK fun i =>
        Eq.mpr (id (congrArg (fun _a => _a ≤ K) (Poincare.ParabolicHolder.increment_norm f i)))
          ((div_le_iff₀
                (Real.rpow_pos_of_pos (Poincare.ParabolicHolder.parabolicDist_pos i.property.right.right) α)).mpr
            (hh (↑i).1 i.property.left (↑i).2 i.property.right.left))))
theorem Poincare.ParabolicHolder.norm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F),
  ‖f‖ =
    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) +
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          ‖f‖ = _a + Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
        (Poincare.ParabolicHolder.supNorm_eq f)))
    (Eq.mpr (id (congrArg (fun _a => ‖f‖ = ‖WithLp.fst ↑f‖ + _a) (Poincare.ParabolicHolder.holderSeminorm_eq f)))
      (Eq.mpr
        (id (congrArg (fun _a => _a = ‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖) (Poincare.ParabolicHolder.norm_eq_parts f)))
        (Eq.refl (‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖))))
theorem Poincare.ParabolicSolutionGraph.norm_eq.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T),
  ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  id
    (Eq.mpr
      (id
        (congrFun'
          (congrArg Eq
            (Eq.trans (WithLp.prod_norm_eq_of_L1 ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))
              (congr
                (congrArg HAdd.hAdd
                  (WithLp.prod_norm_eq_of_L1 (WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))
                (WithLp.prod_norm_eq_of_L1 (WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))))
          (‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖)))
      (Eq.symm
        (add_assoc
          (‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖ +
            ‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)))
structure Poincare.ParabolicSolutionGraph.Graph.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (α T : ℝ) : Type u_1
number of parameters: 5
fields:
  Poincare.ParabolicSolutionGraph.Graph.u : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.ut : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.zero_trace : ∀ (x : E), ↑(WithLp.fst ↑self.u) (0, x) = 0
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.u) (t, z)) (↑(WithLp.fst ↑self.du) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.du) (t, z)) (↑(WithLp.fst ↑self.ddu) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasDeriv_time : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E),
        HasDerivWithinAt (fun s => ↑(WithLp.fst ↑self.u) (s, x)) (↑(WithLp.fst ↑self.ut) (t, x)) (Set.Icc 0 T) t
constructor:
  Poincare.ParabolicSolutionGraph.Graph.mk.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
    (u ut : Poincare.ParabolicHolder.Y α T ℝ) (du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ))
    (ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)) (zero_trace : ∀ (x : E), ↑(WithLp.fst ↑u) (0, x) = 0)
    (hasFDeriv :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑u) (t, z)) (↑(WithLp.fst ↑du) (t, x)) x)
    (hasFDeriv_du :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑du) (t, z)) (↑(WithLp.fst ↑ddu) (t, x)) x)
    (hasDeriv_time :
      ∀ t ∈ Set.Icc 0 T,
        ∀ (x : E), HasDerivWithinAt (fun s => ↑(WithLp.fst ↑u) (s, x)) (↑(WithLp.fst ↑ut) (t, x)) (Set.Icc 0 T) t) :
    Poincare.ParabolicSolutionGraph.Graph α T
def Poincare.ParabolicSolutionGraph.ofDerivatives.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {α T : ℝ} →
        (u ut : ℝ × E → ℝ) →
          (du : ℝ × E → E →L[ℝ] ℝ) →
            (ddu : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) →
              (∀ p ∉ Poincare.ParabolicHolder.cylinder T, u p = 0) →
                (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖u p‖ ≤ M) →
                  (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) u K) →
                    (∀ p ∉ Poincare.ParabolicHolder.cylinder T, ut p = 0) →
                      (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ut p‖ ≤ M) →
                        (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ut K) →
                          (∀ p ∉ Poincare.ParabolicHolder.cylinder T, du p = 0) →
                            (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖du p‖ ≤ M) →
                              (∃ K,
                                  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) du
                                    K) →
                                (∀ p ∉ Poincare.ParabolicHolder.cylinder T, ddu p = 0) →
                                  (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ddu p‖ ≤ M) →
                                    (∃ K,
                                        Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                                          ddu K) →
                                      (∀ (x : E), u (0, x) = 0) →
                                        (∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => u (t, z)) (du (t, x)) x) →
                                          (∀ t ∈ Set.Icc 0 T,
                                              ∀ (x : E), HasFDerivAt (fun z => du (t, z)) (ddu (t, x)) x) →
                                            (∀ t ∈ Set.Icc 0 T,
                                                ∀ (x : E),
                                                  HasDerivWithinAt (fun s => u (s, x)) (ut (t, x)) (Set.Icc 0 T) t) →
                                              Poincare.ParabolicSolutionGraph.Graph α T :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} u ut du ddu hu_off hu_bound hu_holder hut_off hut_bound
    hut_holder hdu_off hdu_bound hdu_holder hddu_off hddu_bound hddu_holder hzero hdu hddu hut =>
  { u := Poincare.ParabolicHolder.ofFunction u hu_off hu_bound hu_holder,
    ut := Poincare.ParabolicHolder.ofFunction ut hut_off hut_bound hut_holder,
    du := Poincare.ParabolicHolder.ofFunction du hdu_off hdu_bound hdu_holder,
    ddu := Poincare.ParabolicHolder.ofFunction ddu hddu_off hddu_bound hddu_holder, zero_trace := hzero,
    hasFDeriv := hdu, hasFDeriv_du := hddu, hasDeriv_time := hut }
theorem Poincare.ParabolicSolutionGraph.time_bound.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {t : ℝ},
  t ∈ Set.Icc 0 T → ∀ (x : E), ‖↑(WithLp.fst ↑g.u) (t, x)‖ ≤ t * ‖g.ut‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {t} ht x =>
  have h :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s hs => g.hasDeriv_time s hs x)
      (fun s x_1 => Poincare.ParabolicHolder.norm_le g.ut (s, x)) (convex_Icc 0 T)
      (have this := ⟨le_rfl, LE.le.trans ht.left ht.right⟩;
      this)
      ht;
  Eq.mpr (id ge_iff_le._simp_1)
    (Eq.mp
      (congr
        (congrArg LE.le
          (congrArg norm
            (Eq.trans (congrArg (HSub.hSub (↑(WithLp.fst ↑g.u) (t, x))) (g.zero_trace x))
              (sub_zero (↑(WithLp.fst ↑g.u) (t, x))))))
        (Eq.trans (congrArg (HMul.hMul ‖↑g.ut‖) (Eq.trans (congrArg norm (sub_zero t)) (Real.norm_of_nonneg ht.left)))
          (mul_comm ‖↑g.ut‖ t)))
      h)
theorem Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace : ∀ (g : Poincare.ClosedSmoothModel 3 → ℝ)
  (x : Poincare.ClosedSmoothModel 3),
  Laplacian.laplacian g x =
    ∑ i, ((fderiv ℝ (fderiv ℝ g) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) :=
fun g x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a x =
            ∑ i,
              ((fderiv ℝ (fderiv ℝ g) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g (EuclideanSpace.basisFun (Fin 3) ℝ))))
    (of_eq_true
      (Eq.trans
        (congr
          (congrArg Eq
            (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
              Eq.trans
                (Eq.trans
                  (congrArg (⇑(iteratedFDeriv ℝ 2 g x))
                    (congr (congrArg Matrix.vecCons (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1))
                      (congrFun' (congrArg Matrix.vecCons (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)) ![])))
                  (iteratedFDeriv_two_apply g x ![EuclideanSpace.single x_1 1, EuclideanSpace.single x_1 1]))
                (congrArg (⇑((fderiv ℝ (fderiv ℝ g) x) (EuclideanSpace.single x_1 1)))
                  (Matrix.cons_val_fin_one (EuclideanSpace.single x_1 1) ![] 0))))
          (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
            congr
              (congrArg DFunLike.coe
                (congrArg (⇑(fderiv ℝ (fderiv ℝ g) x)) (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)))
              (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)))
        (eq_self (∑ x_1, ((fderiv ℝ (fderiv ℝ g) x) (EuclideanSpace.single x_1 1)) (EuclideanSpace.single x_1 1)))))
/tmp/duhamel-solution-probes/001-prerequisites.lean:37:28: error: unexpected token ':='; expected ')', ',' or ':'
```

### 002-prerequisites

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/duhamel-solution-probes/002-prerequisites.lean
```

Exit: `0`.

```lean
import Poincare.Global.HeatDuhamelHessianDifferentiation
import Poincare.Global.DuhamelParabolicHolderSeminorm
import Poincare.Global.MovingLimitLeibniz
import Poincare.Global.ParabolicHolderSpace
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.HeatDuhamelHeatEquation
#print Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound
#print Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel
#print Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel
#print Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral
#print Poincare.HeatDuhamelHessianDifferentiation.gradient_integral
#print Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral
#print Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le
#print Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time
#print Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time
#print Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
#print Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian
#print Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation
#print Poincare.ParabolicHolder.Y
#print Poincare.ParabolicHolder.parabolicDist
#print Poincare.ParabolicHolder.cylinder
#print Poincare.ParabolicHolder.HasHolderBound
#print Poincare.ParabolicHolder.ofFunction
#print Poincare.ParabolicHolder.norm_le_of_bounds
#print Poincare.ParabolicHolder.norm_eq
#print Poincare.ParabolicSolutionGraph.norm_eq
#print Poincare.ParabolicSolutionGraph.Graph
#print Poincare.ParabolicSolutionGraph.ofDerivatives
#print Poincare.ParabolicSolutionGraph.time_bound
#print Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
open Set MeasureTheory
open scoped Interval
namespace Poincare.DuhamelSolutionOperatorBound
local notation "E" => Poincare.ClosedSmoothModel 3
#check (∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖)
end Poincare.DuhamelSolutionOperatorBound
```

Actual compiler output:

```text
theorem Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound : ∀ (α : ℝ),
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
                                        (Set.Ioo 0 t) MeasureTheory.volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : Poincare.ClosedSmoothModel 3),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2) :=
fun α hα hα1 =>
  let J :=
    ∫ (y : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α;
  Exists.intro (max 1 (J * (2 / α)))
    ⟨lt_of_lt_of_le zero_lt_one (le_max_left 1 (J * (2 / α))), fun T a a_1 f M K a_2 hK0 hf hM hK =>
      id
        ⟨fun x => intervalIntegral.integral_same, fun t ht x =>
          ⟨Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel hα hα1 ht hf hM hK,
            ⟨Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
              ⟨Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
                Eq.mpr
                  (id
                    (congrArg (fun _a => ‖_a‖ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2))
                      (Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x)))
                  (Trans.trans
                    (Trans.trans
                      (Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le hα hα1 ht.left
                        (fun s hs => hK s ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht.right⟩) x)
                      (Mathlib.Tactic.Ring.of_eq
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right J (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (K ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (J ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                        (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                    (Eq.symm
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a => α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                      Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                          (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                      (Eq.symm
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                        Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (J ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                            (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))))
                    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 (J * (2 / α))) hK0)
                      (Real.rpow_nonneg ht.left (α / 2))))⟩⟩⟩⟩⟩
theorem Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel : ∀ {α T t M K : ℝ},
  0 < α →
    α < 1 →
      t ∈ Set.Icc 0 T →
        ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
          ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
            (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
              (∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) →
                ContDiff ℝ 2 fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z :=
fun {α T t M K} hα hα1 ht {f} hf hM hK =>
  have hD :=
    funext fun z => HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z);
  have hDD :=
    funext fun z =>
      HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z);
  id
    (contDiff_succ_iff_fderiv.mpr
      ⟨fun z =>
        HasFDerivAt.differentiableAt (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z),
        ⟨of_eq_true
            (Eq.trans
              (Eq.trans
                (implies_congr (Eq.trans WithTop.one_ne_top._simp_2 (eq_false not_false))
                  (congrFun'
                    (congrArg (AnalyticOnNhd ℝ)
                      (funext fun z =>
                        congrFun'
                          (congrFun'
                            (congrFun'
                              (congrArg intervalIntegral
                                (funext fun s => Poincare.heatSolution_apply (t - s) (fun y => f (s, y)) z))
                              0)
                            t)
                          MeasureTheory.volume))
                    Set.univ))
                IsEmpty.forall_iff._simp_1)
              (eq_true True.intro)),
          Eq.mpr (id (congrArg (fun _a => ContDiff ℝ 1 _a) hD))
            (contDiff_one_iff_fderiv.mpr
              ⟨fun z =>
                HasFDerivAt.differentiableAt
                  (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z),
                Eq.mpr (id (congrArg (fun _a => Continuous _a) hDD))
                  (Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian hα hα1 ht hf hM hK)⟩)⟩⟩)
theorem Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            HasFDerivAt (fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z)
              (∫ (s : ℝ) in 0..t, fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x) x :=
fun {T t M} ht {f} hf hM x =>
  let A := M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖;
  have hmem := fun s hs => ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht.right⟩;
  have hfc := fun s hs =>
    ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
      ⟨hmem s hs, Set.mem_univ y⟩;
  hasFDerivAt_integral_of_dominated_of_fderiv_le'' (of_eq_true Filter.univ_mem._simp_1)
    (Filter.Eventually.of_forall fun z =>
      Eq.mpr
        (id
          (congrArg
            (@MeasureTheory.AEStronglyMeasurable ℝ ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
              Real.measurableSpace Real.measurableSpace fun t_1 =>
              Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) z)
            (congrArg MeasureTheory.volume.restrict (Set.uIoc_of_le ht.left))))
        (IntervalIntegrable.aestronglyMeasurable
          (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht hf hM z)))
    (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht hf hM x)
    (Eq.mpr
      (id
        (congrArg
          (@MeasureTheory.AEStronglyMeasurable ℝ (Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
            ContinuousLinearMap.topologicalSpace Real.measurableSpace Real.measurableSpace fun s =>
            fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
          (congrArg MeasureTheory.volume.restrict (Set.uIoc_of_le ht.left))))
      (IntervalIntegrable.aestronglyMeasurable
        (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time ht hf hM x)))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ∀ᵐ (t_1 : ℝ) ∂MeasureTheory.volume.restrict _a,
              ∀ x ∈ Set.univ,
                ‖fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x‖ ≤ A * (t - t_1) ^ (-(1 / 2)))
          (Set.uIoc_of_le ht.left)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              ∀ᵐ (t_1 : ℝ) ∂_a,
                ∀ x ∈ Set.univ,
                  ‖fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x‖ ≤ A * (t - t_1) ^ (-(1 / 2)))
            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
          (Filter.univ_mem'
            (id fun s hs z a =>
              Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le (sub_pos.mpr hs.right)
                (Continuous.aestronglyMeasurable (hfc s hs)) (id (hM s (hmem s hs))) z)))))
    (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant t A)
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ∀ᵐ (t_1 : ℝ) ∂MeasureTheory.volume.restrict _a,
              ∀ x ∈ Set.univ,
                HasFDerivAt (fun x => Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) x)
                  (fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x) x)
          (Set.uIoc_of_le ht.left)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              ∀ᵐ (t_1 : ℝ) ∂_a,
                ∀ x ∈ Set.univ,
                  HasFDerivAt (fun x => Poincare.heatSolution (t - t_1) (fun y => f (t_1, y)) x)
                    (fderiv ℝ (Poincare.heatSolution (t - t_1) fun y => f (t_1, y)) x) x)
            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
          (Filter.univ_mem'
            (id fun s hs z a =>
              DifferentiableAt.hasFDerivAt
                (HasFDerivAt.differentiableAt
                  (Poincare.heatSolution_hasFDerivAt (sub_pos.mpr hs.right) (Continuous.aestronglyMeasurable (hfc s hs))
                    (id (hM s (hmem s hs))) z)))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral : ∀ {α T t M K : ℝ},
  0 < α →
    α < 1 →
      t ∈ Set.Icc 0 T →
        ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
          ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
            (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
              (∀ s ∈ Set.Icc 0 T, ∀ (x y : Poincare.ClosedSmoothModel 3), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) →
                ∀ (x : Poincare.ClosedSmoothModel 3),
                  fderiv ℝ (fderiv ℝ fun z => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) z)
                      x =
                    ∫ (s : ℝ) in 0..t,
                      ∫ (y : Poincare.ClosedSmoothModel 3),
                        (f (s, x - y) - f (s, x)) •
                          (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y :=
fun {α T t M K} hα hα1 ht {f} hf hM hK x =>
  have hD :=
    funext fun z => HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel ht hf hM z);
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          fderiv ℝ _a x =
            ∫ (s : ℝ) in 0..t,
              ∫ (y : Poincare.ClosedSmoothModel 3),
                (f (s, x - y) - f (s, x)) •
                  (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y)
        hD))
    (HasFDerivAt.fderiv (Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x))
theorem Poincare.HeatDuhamelHessianDifferentiation.gradient_integral : ∀ {t : ℝ},
  0 < t →
    ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y‖ =
      (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
        t ^ (-(1 / 2)) :=
fun {t} ht =>
  have h := Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq (√t) (Real.sqrt_pos.mpr ht);
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a =
            (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
              t ^ (-(1 / 2)))
        (Eq.mp
          (congrArg
            (fun _a =>
              ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) _a y‖ =
                (√t)⁻¹ *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
            (Real.sq_sqrt (LT.lt.le ht)))
          h)))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            _a⁻¹ *
                ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖ =
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                t ^ (-(1 / 2)))
          (Real.sqrt_eq_rpow t)))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              (t ^ (1 / 2))⁻¹ *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖ =
                (∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  _a)
            (Real.rpow_neg (LT.lt.le ht) (1 / 2))))
        (Mathlib.Tactic.Ring.of_eq
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.inv_congr
              (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (1 / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.inv_single
                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (t ^ (1 / 2))⁻¹)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                  (Eq.symm
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                    Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))))
            (Mathlib.Tactic.Ring.Common.atom_pf
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
              rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                    (∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                            ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1 +
                  0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
              rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        (∫ (y : Poincare.ClosedSmoothModel 3),
                              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.inv_congr
              (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (1 / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((t ^ (1 / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.inv_single
                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (t ^ (1 / 2))⁻¹)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                  (Eq.symm
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                    Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (1 / 2))⁻¹ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                    (∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                            ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((t ^ (1 / 2))⁻¹ ^ Nat.rawCast 1 *
                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0)))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral : ∀ {t M : ℝ},
  0 < t →
    ∀ {f : Poincare.ClosedSmoothModel 3 → ℝ},
      MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
        (∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            fderiv ℝ (Poincare.heatSolution t f) x =
              ∫ (y : Poincare.ClosedSmoothModel 3),
                f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y :=
fun {t M} ht {f} hf hM x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a =
            ∫ (y : Poincare.ClosedSmoothModel 3),
              f (x - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y)
        (HasFDerivAt.fderiv (Poincare.heatSolution_hasFDerivAt ht hf hM x))))
    (have hc :=
      MeasureTheory.integral_sub_left_eq_self
        (fun y => f y • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t (x - y)) MeasureTheory.volume x;
    id
      (Eq.mp
        (congrArg
          (Eq (∫ (x_1 : Poincare.ClosedSmoothModel 3), f x_1 • fderiv ℝ (fun z => Poincare.heatKernel t z) (x - x_1)))
          (congrArg (MeasureTheory.integral MeasureTheory.volume)
            (funext fun x_1 =>
              congrArg (HSMul.hSMul (f (x - x_1)))
                (congrArg (fderiv ℝ fun z => Poincare.heatKernel t z) (sub_sub_cancel x x_1)))))
        (Eq.symm hc)))
theorem Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le : ∀ {t M : ℝ},
  0 < t →
    ∀ {f : Poincare.ClosedSmoothModel 3 → ℝ},
      MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
        (∀ (y : Poincare.ClosedSmoothModel 3), ‖f y‖ ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            ‖fderiv ℝ (Poincare.heatSolution t f) x‖ ≤
              (M *
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                t ^ (-(1 / 2)) :=
fun {t M} ht {f} hf hM x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          ‖_a‖ ≤
            (M *
                ∫ (y : Poincare.ClosedSmoothModel 3),
                  ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
              t ^ (-(1 / 2)))
        (Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral ht hf hM x)))
    (Trans.trans
      (MeasureTheory.norm_integral_le_of_norm_le
        (MeasureTheory.Integrable.const_mul
          (MeasureTheory.Integrable.norm (Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient ht)) M)
        (Filter.Eventually.of_forall fun y =>
          LE.le.trans
            (Poincare.norm_real_smul_continuousLinearMap_one_le (f (x - y))
              ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y))
            (mul_le_mul_of_nonneg_right (hM (x - y))
              (norm_nonneg ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y)))))
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a =
                (M *
                    ∫ (y : Poincare.ClosedSmoothModel 3),
                      ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  t ^ (-(1 / 2)))
            (MeasureTheory.integral_const_mul M fun y =>
              ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) t y‖)))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                M * _a =
                  (M *
                      ∫ (y : Poincare.ClosedSmoothModel 3),
                        ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                    t ^ (-(1 / 2)))
              (Poincare.HeatDuhamelHessianDifferentiation.gradient_integral ht)))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  M *
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                          ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                        t ^ (-(1 / 2))) =
                    _a)
                (mul_assoc M
                  (∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖)
                  (t ^ (-(1 / 2))))))
            (Eq.refl
              (M *
                ((∫ (y : Poincare.ClosedSmoothModel 3),
                    ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖) *
                  t ^ (-(1 / 2)))))))))
theorem Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          Continuous fun p => fderiv ℝ (Poincare.heatSolution (t - ↑p.1) fun y => f (↑p.1, y)) p.2 :=
fun {T t M} ht {f} hf hM =>
  have hmem := fun s => ⟨LT.lt.le s.property.left, LE.le.trans (LT.lt.le s.property.right) ht.right⟩;
  have hs := Continuous.comp continuous_subtype_val continuous_fst;
  have ha := Continuous.comp Real.continuous_sqrt (Continuous.sub continuous_const hs);
  have hapos := fun p => Real.sqrt_pos.mpr (sub_pos.mpr p.1.property.right);
  have hunit :=
    ContDiff.continuous
      (ContDiff.fderiv_right (Poincare.contDiff_heatKernel_spatial 1)
        (of_eq_true
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg LE.le
                  (Mathlib.Meta.NormNum.IsNat.to_eq
                    (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd)
                      (Mathlib.Meta.NormNum.isNat_ofNat (WithTop ℕ∞) Nat.cast_zero)
                      (Mathlib.Meta.NormNum.isNat_ofNat (WithTop ℕ∞) Nat.cast_one) (Eq.refl 1))
                    Nat.cast_one))
                ⊤)
              le_top._simp_2)
            (eq_true True.intro))));
  have hn :=
    MeasureTheory.continuous_of_dominated
      (fun p =>
        Continuous.aestronglyMeasurable
          (Continuous.smul
            (ContinuousOn.comp_continuous hf
              (Continuous.prodMk continuous_const
                (Continuous.sub continuous_const (Continuous.smul continuous_const continuous_id)))
              fun y => ⟨hmem p.1, Set.mem_univ (p.1.1, p.2 - √(t - ↑p.1) • id y).2⟩)
            hunit))
      (fun p =>
        Filter.Eventually.of_forall fun y =>
          LE.le.trans
            (Poincare.norm_real_smul_continuousLinearMap_one_le (f (↑p.1, p.2 - √(t - ↑p.1) • y))
              ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y))
            (mul_le_mul_of_nonneg_right (hM (↑p.1) (hmem p.1) (p.2 - √(t - ↑p.1) • y))
              (norm_nonneg ((fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y))))
      (MeasureTheory.Integrable.const_mul
        (MeasureTheory.Integrable.norm (Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient zero_lt_one)) M)
      (Filter.Eventually.of_forall fun y =>
        Continuous.smul
          (ContinuousOn.comp_continuous hf
            (Continuous.prodMk hs (Continuous.sub continuous_snd (Continuous.smul ha continuous_const))) fun p =>
            ⟨hmem p.1, Set.mem_univ (↑p.1, p.2 - √(t - ↑p.1) • y).2⟩)
          continuous_const);
  Continuous.congr (Continuous.smul (Continuous.inv₀ ha fun p => LT.lt.ne' (hapos p)) hn) fun p =>
    have hfc :=
      ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
        ⟨hmem p.1, Set.mem_univ y⟩;
    Eq.mpr
      (id
        (congrArg
          (fun _a =>
            (√(t - ↑p.1))⁻¹ •
                ∫ (y : Poincare.ClosedSmoothModel 3),
                  f (↑p.1, p.2 - √(t - ↑p.1) • y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y =
              _a)
          (Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.right)
            (Continuous.aestronglyMeasurable hfc) (id (hM (↑p.1) (hmem p.1))) p.2)))
      (have h :=
        Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq (√(t - ↑p.1)) (hapos p)
          (fun y => f (↑p.1, y)) p.2;
      Eq.symm
        (Eq.mp
          (congrArg
            (fun _a =>
              ∫ (y : Poincare.ClosedSmoothModel 3),
                  f (↑p.1, p.2 - y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) _a y =
                (√(t - ↑p.1))⁻¹ •
                  ∫ (y : Poincare.ClosedSmoothModel 3),
                    f (↑p.1, p.2 - √(t - ↑p.1) • y) • (fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y)
            (Real.sq_sqrt (LT.lt.le (sub_pos.mpr p.1.property.right))))
          h))
theorem Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            IntervalIntegrable (fun s => fderiv ℝ (Poincare.heatSolution (t - s) fun y => f (s, y)) x)
              MeasureTheory.volume 0 t :=
fun {T t M} ht {f} hf hM x =>
  have hc :=
    Continuous.comp (Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time ht hf hM)
      (Continuous.prodMk continuous_id continuous_const);
  let A := M * ∫ (y : Poincare.ClosedSmoothModel 3), ‖(fun t x => fderiv ℝ (fun z => Poincare.heatKernel t z) x) 1 y‖;
  have hi :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.left enorm_ne_top enorm_ne_top).mp
      (Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant t A);
  Eq.mpr
    (id
      (congrArg (fun _a => _a)
        (propext (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.left enorm_ne_top enorm_ne_top))))
    (Eq.mpr (id (congrArg (fun _a => _a) (propext (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo))))
      (MeasureTheory.Integrable.mono'
        (Eq.mp (congrArg (fun _a => _a) (propext (MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo)))
          hi)
        (Continuous.aestronglyMeasurable hc)
        (Filter.Eventually.of_forall fun s =>
          have hmem := ⟨LT.lt.le s.property.left, LE.le.trans (LT.lt.le s.property.right) ht.right⟩;
          have hfc :=
            ContinuousOn.comp_continuous hf (Continuous.prodMk continuous_const continuous_id) fun y =>
              ⟨hmem, Set.mem_univ y⟩;
          Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le (sub_pos.mpr s.property.right)
            (Continuous.aestronglyMeasurable hfc) (id (hM (↑s) hmem)) x)))
theorem Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder : ∀ (α : ℝ),
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
                                  C * K * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun α hα hα1 =>
  Exists.casesOn (Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1) fun C₁ h =>
    And.casesOn h fun hC₁ hspace =>
      Exists.casesOn (Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1) fun C₂ h =>
        And.casesOn h fun hC₂ htime =>
          Exists.intro (C₁ + C₂)
            ⟨add_pos hC₁ hC₂, fun T hT hT1 f M K hM hK hf hfM hfK =>
              id fun p hp q hq =>
                let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.left p.2 q.2;
                have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.left q.1 hq.left q.2;
                have hspow :=
                  Real.rpow_le_rpow (norm_nonneg (p.2 - q.2)) (le_add_of_nonneg_right (Real.sqrt_nonneg |p.1 - q.1|))
                    (LT.lt.le hα);
                have htpow :=
                  Trans.trans
                    (Eq.mpr (id (congrArg (fun _a => |p.1 - q.1| ^ (α / 2) = _a ^ α) (Real.sqrt_eq_rpow |p.1 - q.1|)))
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => |p.1 - q.1| ^ (α / 2) = _a)
                            (Eq.symm (Real.rpow_mul (abs_nonneg (p.1 - q.1)) (1 / 2) α))))
                        ((fun {α β γ} [HPow α β γ] a a_1 e_a =>
                            Eq.rec (motive := fun a_2 e_a => ∀ (a_3 a_4 : β), a_3 = a_4 → a ^ a_3 = a_2 ^ a_4)
                              (fun a_2 a_3 e_a => e_a ▸ Eq.refl (a ^ a_2)) e_a)
                          |p.1 - q.1| |p.1 - q.1| (Eq.refl |p.1 - q.1|) (α / 2) (1 / 2 * α)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                          (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 2 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                            (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                          (Eq.refl (Nat.mul 1 1)) (Eq.refl 2)))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 1 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (NNRat.rawCast 1 2 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero (NNRat.rawCast 1 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNNRat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                          (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                              (Mathlib.Meta.NormNum.IsNNRat.of_raw ℝ 1 2
                                                (Mathlib.Meta.NormNum.IsNNRat.den_nz
                                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)))))
                                              (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Eq.refl (Nat.mul 1 1)) (Eq.refl 2))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (NNRat.rawCast 1 2))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (α ^ Nat.rawCast 1 * NNRat.rawCast 1 2 + 0))))))))
                    (Real.rpow_le_rpow (Real.sqrt_nonneg |p.1 - q.1|) (le_add_of_nonneg_left (norm_nonneg (p.2 - q.2)))
                      (LT.lt.le hα));
                Trans.trans
                  (Trans.trans
                    (Trans.trans
                      (Eq.mp
                        (congrFun'
                          (congrArg LE.le
                            (congrArg norm
                              (sub_add_sub_cancel (fderiv ℝ (fderiv ℝ (u p.1)) p.2) (fderiv ℝ (fderiv ℝ (u p.1)) q.2)
                                (fderiv ℝ (fderiv ℝ (u q.1)) q.2))))
                          (‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
                            ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖))
                        (norm_add_le (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
                          (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)))
                      (add_le_add hs ht))
                    (add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg (LT.lt.le hC₁) hK))
                      (mul_le_mul_of_nonneg_left htpow (mul_nonneg (LT.lt.le hC₂) hK))))
                  (Mathlib.Tactic.Ring.of_eq
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₁ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₁ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₁ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                    (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 *
                                  (K ^ Nat.rawCast 1 *
                                    ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                      Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C₁ ^ Nat.rawCast 1 *
                                (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₂ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₂ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                    (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                    (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (C₁ ^ Nat.rawCast 1 *
                          (K ^ Nat.rawCast 1 *
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (K ^ Nat.rawCast 1 *
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf C₁ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₁ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₁ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf C₂ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 = C₂ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (C₁ ^ Nat.rawCast 1 * Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left C₁ (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (C₁ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 1)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C₁ ^ Nat.rawCast 1 *
                                (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C₂ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))))
                            (Mathlib.Tactic.Ring.Common.mul_zero
                              (K ^ Nat.rawCast 1 * (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                    (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (C₁ ^ Nat.rawCast 1 *
                            (K ^ Nat.rawCast 1 *
                              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (K ^ Nat.rawCast 1 *
                                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                                  (C₂ ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                              0))))))⟩
theorem Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian : ∀ (α : ℝ),
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
                              (fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K) :=
fun α hα hα1 =>
  Exists.casesOn (Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1) fun C h =>
    And.casesOn h fun hC hbound => Exists.intro C ⟨hC, hbound⟩
theorem Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation : ∀ (α : ℝ),
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
                                (Set.Icc 0 T) t :=
fun α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK =>
  id
    ⟨fun x => Poincare.HeatDuhamelHeatEquation.duhamel_zero f x, fun t ht x =>
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, Poincare.heatSolution (r - s) (fun y => f (s, y)) x)
                (f (t, x) + _a) (Set.Icc 0 T) t)
            (Eq.symm
              (Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace
                (fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x) x))))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, Poincare.heatSolution (r - s) (fun y => f (s, y)) x)
                  (f (t, x) + _a) (Set.Icc 0 T) t)
              (Eq.symm (Poincare.HeatDuhamelHeatEquation.duhamel_time_derivative_integral hα hα1 ht hf hM hK x).right)))
          (let F := fun r s => if r - s = 0 then f (s, x) else Poincare.heatSolution (r - s) (fun y => f (s, y)) x;
          have hc :=
            ContinuousOn.comp (Poincare.HeatDuhamelHeatEquation.continuousOn_heat_integrand_extension hf hM x)
              (Continuous.continuousOn
                (Continuous.prodMk (Continuous.sub continuous_fst continuous_snd) continuous_snd))
              fun p hp => ⟨sub_nonneg.mpr hp.right.right, hp.left⟩;
          have hd := fun s hs r hr =>
            have hd0 :=
              DifferentiableAt.hasDerivAt
                (HasDerivAt.differentiableAt
                  (Poincare.HeatDuhamelHeatEquation.hasDerivAt_heat_integrand hs hr.left hf hM x));
            HasDerivAt.congr_of_eventuallyEq hd0
              (Filter.mp_mem (Ioi_mem_nhds hr.left)
                (Filter.univ_mem'
                  (id fun ρ hρ =>
                    of_eq_true
                      (Eq.trans
                        (congrFun'
                          (congrArg Eq
                            (Eq.trans
                              (congrFun'
                                (congrFun'
                                  (funext fun r =>
                                    funext fun s =>
                                      ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                        Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                  ρ)
                                s)
                              ((fun x_0 x_1 x_2 x_3 =>
                                  (fun x_0 x_1 x_2 x_3 =>
                                      if_neg
                                        (ne_of_gt
                                          (sub_pos.mpr
                                            (have this := hρ;
                                            this))))
                                    x_0 x_1 x_2 x_3)
                                ((ρ - s).decidableEq 0) ℝ (f (s, x))
                                (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))))
                          (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))
                        (eq_self (Poincare.heatSolution (ρ - s) (fun y => f (s, y)) x))))));
          Exists.casesOn (Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound hα hα1 hK0 hf hM hK x)
            fun C h =>
            And.casesOn h fun hC hCb =>
              have hsolve :=
                Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit ht
                  (lt_of_not_ge fun a =>
                    Mathlib.Tactic.Linarith.lt_irrefl
                      (Eq.mp
                        (congrArg (fun _a => _a < 0)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.add_congr
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                    (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.zero_mul 0)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                                (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsInt.to_isNat
                                    (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                      (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                      (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                      (Eq.refl (Int.ofNat 0)))))
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                            (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                        (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                          (Eq.mp
                            (congrArg (fun _a => _a ≤ 0)
                              (Mathlib.Tactic.CancelDenoms.sub_subst
                                (Mathlib.Tactic.CancelDenoms.div_subst rfl
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                      (Mathlib.Meta.NormNum.isNNRat_div
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                rfl))
                            (Mathlib.Tactic.Linarith.mul_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le a)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false)))))))
                  (le_of_not_gt fun a =>
                    Mathlib.Tactic.Linarith.lt_irrefl
                      (Eq.mp
                        (congrArg (fun _a => _a < 0)
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.add_congr
                              (Mathlib.Tactic.Ring.Common.add_congr
                                (Mathlib.Tactic.Ring.Common.sub_congr
                                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.sub_pf
                                    (Mathlib.Tactic.Ring.Common.neg_add
                                      (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                            (Eq.refl (Int.negOfNat 1)))))
                                      Mathlib.Tactic.Ring.Common.neg_zero)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                      (Eq.mpr
                                        (id
                                          (congrArg
                                            (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                    (Mathlib.Tactic.Ring.Common.sub_pf
                                      (Mathlib.Tactic.Ring.Common.neg_add
                                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                            (Eq.refl (Int.negOfNat 1))))
                                        Mathlib.Tactic.Ring.Common.neg_zero)
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                          (Eq.refl (Int.negOfNat 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_add
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                        (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 2).rawCast
                                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                          (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                                    (Mathlib.Tactic.Ring.Common.zero_mul
                                      ((Int.negOfNat 1).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((Int.negOfNat 2).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 2).rawCast
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
                                    (Mathlib.Tactic.Ring.Common.add_overlap_pf α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                            (Eq.refl (Int.ofNat 1))))))
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 2 + 0))))
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                    (Eq.refl (Int.ofNat 0))))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                        (Eq.refl (Int.ofNat 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                            (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                        (Mathlib.Tactic.Linarith.add_neg
                          (Mathlib.Tactic.Linarith.add_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                            (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα1)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))))
                          (Eq.mp
                            (congrArg (fun _a => _a < 0)
                              (Mathlib.Tactic.CancelDenoms.sub_subst rfl
                                (Mathlib.Tactic.CancelDenoms.div_subst rfl
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                      (Mathlib.Meta.NormNum.isNNRat_div
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                              (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                  (Mathlib.Meta.NormNum.isNat_eq_true
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))))
                            (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt a)
                              (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false)))))))
                  hC hc
                  (of_eq_true
                    (Eq.trans
                      (congrFun'
                        (congrArg Eq
                          (Eq.trans
                            (congrFun'
                              (congrFun'
                                (funext fun r =>
                                  funext fun s =>
                                    ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                      Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                t)
                              t)
                            (Eq.trans
                              (ite_congr (Eq.trans (congrFun' (congrArg Eq (sub_self t)) 0) (eq_self 0))
                                (fun a => Eq.refl (f (t, x))) fun a =>
                                Poincare.heatSolution.congr_simp (t - t) 0 (sub_self t) (fun y => f (t, y))
                                  (fun y => f (t, y)) (Eq.refl fun y => f (t, y)) x x (Eq.refl x))
                              (if_true (f (t, x)) (Poincare.heatSolution 0 (fun y => f (t, y)) x)))))
                        (f (t, x)))
                      (eq_self (f (t, x)))))
                  hd hCb;
              HasDerivWithinAt.congr_of_mem hsolve
                (fun r hr =>
                  intervalIntegral.integral_congr_ae_restrict
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            (fun x_1 =>
                                Poincare.heatSolution (r - x_1) (fun y => f (x_1, y))
                                  x) =ᵐ[MeasureTheory.volume.restrict _a]
                              F r)
                          (Set.uIoc_of_le hr.left)))
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a => (fun x_1 => Poincare.heatSolution (r - x_1) (fun y => f (x_1, y)) x) =ᵐ[_a] F r)
                            (Eq.symm MeasureTheory.restrict_Ioo_eq_restrict_Ioc)))
                        (Filter.mp_mem (MeasureTheory.ae_restrict_mem measurableSet_Ioo)
                          (Filter.univ_mem'
                            (id fun s hs =>
                              of_eq_true
                                (Eq.trans
                                  (congrArg (Eq (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                    (Eq.trans
                                      (congrFun'
                                        (congrFun'
                                          (funext fun r =>
                                            funext fun s =>
                                              ite_congr (Eq.refl (r - s = 0)) (fun a => Eq.refl (f (s, x))) fun a =>
                                                Eq.refl (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))
                                          r)
                                        s)
                                      ((fun x_0 x_1 x_2 x_3 =>
                                          (fun x_0 x_1 x_2 x_3 => if_neg (ne_of_gt (sub_pos.mpr hs.right))) x_0 x_1 x_2
                                            x_3)
                                        ((r - s).decidableEq 0) ℝ (f (s, x))
                                        (Poincare.heatSolution (r - s) (fun y => f (s, y)) x))))
                                  (eq_self (Poincare.heatSolution (r - s) (fun y => f (s, y)) x)))))))))
                ht))⟩
@[reducible] def Poincare.ParabolicHolder.Y.{u_1, u_3} : {E : Type u_1} →
  [NormedAddCommGroup E] →
    ℝ → ℝ → (F : Type u_3) → [inst : NormedAddCommGroup F] → [NormedSpace ℝ F] → Type (max u_1 u_3) :=
fun {E} [NormedAddCommGroup E] α T F [NormedAddCommGroup F] [NormedSpace ℝ F] =>
  ↥(Poincare.ParabolicHolder.holderSubmodule α T)
def Poincare.ParabolicHolder.parabolicDist.{u_1} : {E : Type u_1} → [NormedAddCommGroup E] → ℝ × E → ℝ × E → ℝ :=
fun {E} [NormedAddCommGroup E] p q => ‖p.2 - q.2‖ + √|p.1 - q.1|
def Poincare.ParabolicHolder.cylinder.{u_1} : {E : Type u_1} → ℝ → Set (ℝ × E) :=
fun {E} T => Set.Icc 0 T ×ˢ Set.univ
def Poincare.ParabolicHolder.HasHolderBound.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup E] → [NormedAddCommGroup F] → ℝ → Set (ℝ × E) → (ℝ × E → F) → ℝ → Prop :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] α S f K =>
  ∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * Poincare.ParabolicHolder.parabolicDist p q ^ α
def Poincare.ParabolicHolder.ofFunction.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} →
    [inst : NormedAddCommGroup E] →
      [inst_1 : NormedAddCommGroup F] →
        [inst_2 : NormedSpace ℝ F] →
          {α T : ℝ} →
            (f : ℝ × E → F) →
              (∀ p ∉ Poincare.ParabolicHolder.cylinder T, f p = 0) →
                (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖f p‖ ≤ M) →
                  (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K) →
                    Poincare.ParabolicHolder.Y α T F :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f hoff hb hh =>
  let v := ⟨f, ⋯⟩;
  let w := ⟨fun i => (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2), ⋯⟩;
  ⟨WithLp.toLp 1 (v, w), ⋯⟩
theorem Poincare.ParabolicHolder.norm_le_of_bounds.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F) {M K : ℝ},
  0 ≤ M →
    0 ≤ K →
      (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M) →
        Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f)) K →
          ‖f‖ ≤ M + K :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f {M K} hM hK hb hh =>
  Eq.mpr (id (congrArg (fun _a => _a ≤ M + K) (Poincare.ParabolicHolder.norm_eq_parts f)))
    (add_le_add
      (lp.norm_le_of_forall_le hM fun p =>
        if hp : p ∈ Poincare.ParabolicHolder.cylinder T then hb p hp
        else
          id
            (Eq.mpr
              (id
                (congrFun'
                  (congrArg LE.le (Eq.trans (congrArg norm (Poincare.ParabolicHolder.zero_off f hp)) norm_zero)) M))
              hM))
      (lp.norm_le_of_forall_le hK fun i =>
        Eq.mpr (id (congrArg (fun _a => _a ≤ K) (Poincare.ParabolicHolder.increment_norm f i)))
          ((div_le_iff₀
                (Real.rpow_pos_of_pos (Poincare.ParabolicHolder.parabolicDist_pos i.property.right.right) α)).mpr
            (hh (↑i).1 i.property.left (↑i).2 i.property.right.left))))
theorem Poincare.ParabolicHolder.norm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F),
  ‖f‖ =
    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) +
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          ‖f‖ = _a + Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
        (Poincare.ParabolicHolder.supNorm_eq f)))
    (Eq.mpr (id (congrArg (fun _a => ‖f‖ = ‖WithLp.fst ↑f‖ + _a) (Poincare.ParabolicHolder.holderSeminorm_eq f)))
      (Eq.mpr
        (id (congrArg (fun _a => _a = ‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖) (Poincare.ParabolicHolder.norm_eq_parts f)))
        (Eq.refl (‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖))))
theorem Poincare.ParabolicSolutionGraph.norm_eq.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T),
  ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  id
    (Eq.mpr
      (id
        (congrFun'
          (congrArg Eq
            (Eq.trans (WithLp.prod_norm_eq_of_L1 ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))
              (congr
                (congrArg HAdd.hAdd
                  (WithLp.prod_norm_eq_of_L1 (WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))
                (WithLp.prod_norm_eq_of_L1 (WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))))
          (‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖)))
      (Eq.symm
        (add_assoc
          (‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖ +
            ‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)))
structure Poincare.ParabolicSolutionGraph.Graph.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (α T : ℝ) : Type u_1
number of parameters: 5
fields:
  Poincare.ParabolicSolutionGraph.Graph.u : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.ut : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.zero_trace : ∀ (x : E), ↑(WithLp.fst ↑self.u) (0, x) = 0
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.u) (t, z)) (↑(WithLp.fst ↑self.du) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.du) (t, z)) (↑(WithLp.fst ↑self.ddu) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasDeriv_time : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E),
        HasDerivWithinAt (fun s => ↑(WithLp.fst ↑self.u) (s, x)) (↑(WithLp.fst ↑self.ut) (t, x)) (Set.Icc 0 T) t
constructor:
  Poincare.ParabolicSolutionGraph.Graph.mk.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
    (u ut : Poincare.ParabolicHolder.Y α T ℝ) (du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ))
    (ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)) (zero_trace : ∀ (x : E), ↑(WithLp.fst ↑u) (0, x) = 0)
    (hasFDeriv :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑u) (t, z)) (↑(WithLp.fst ↑du) (t, x)) x)
    (hasFDeriv_du :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑du) (t, z)) (↑(WithLp.fst ↑ddu) (t, x)) x)
    (hasDeriv_time :
      ∀ t ∈ Set.Icc 0 T,
        ∀ (x : E), HasDerivWithinAt (fun s => ↑(WithLp.fst ↑u) (s, x)) (↑(WithLp.fst ↑ut) (t, x)) (Set.Icc 0 T) t) :
    Poincare.ParabolicSolutionGraph.Graph α T
def Poincare.ParabolicSolutionGraph.ofDerivatives.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {α T : ℝ} →
        (u ut : ℝ × E → ℝ) →
          (du : ℝ × E → E →L[ℝ] ℝ) →
            (ddu : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) →
              (∀ p ∉ Poincare.ParabolicHolder.cylinder T, u p = 0) →
                (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖u p‖ ≤ M) →
                  (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) u K) →
                    (∀ p ∉ Poincare.ParabolicHolder.cylinder T, ut p = 0) →
                      (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ut p‖ ≤ M) →
                        (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ut K) →
                          (∀ p ∉ Poincare.ParabolicHolder.cylinder T, du p = 0) →
                            (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖du p‖ ≤ M) →
                              (∃ K,
                                  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) du
                                    K) →
                                (∀ p ∉ Poincare.ParabolicHolder.cylinder T, ddu p = 0) →
                                  (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ddu p‖ ≤ M) →
                                    (∃ K,
                                        Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
                                          ddu K) →
                                      (∀ (x : E), u (0, x) = 0) →
                                        (∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => u (t, z)) (du (t, x)) x) →
                                          (∀ t ∈ Set.Icc 0 T,
                                              ∀ (x : E), HasFDerivAt (fun z => du (t, z)) (ddu (t, x)) x) →
                                            (∀ t ∈ Set.Icc 0 T,
                                                ∀ (x : E),
                                                  HasDerivWithinAt (fun s => u (s, x)) (ut (t, x)) (Set.Icc 0 T) t) →
                                              Poincare.ParabolicSolutionGraph.Graph α T :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} u ut du ddu hu_off hu_bound hu_holder hut_off hut_bound
    hut_holder hdu_off hdu_bound hdu_holder hddu_off hddu_bound hddu_holder hzero hdu hddu hut =>
  { u := Poincare.ParabolicHolder.ofFunction u hu_off hu_bound hu_holder,
    ut := Poincare.ParabolicHolder.ofFunction ut hut_off hut_bound hut_holder,
    du := Poincare.ParabolicHolder.ofFunction du hdu_off hdu_bound hdu_holder,
    ddu := Poincare.ParabolicHolder.ofFunction ddu hddu_off hddu_bound hddu_holder, zero_trace := hzero,
    hasFDeriv := hdu, hasFDeriv_du := hddu, hasDeriv_time := hut }
theorem Poincare.ParabolicSolutionGraph.time_bound.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {t : ℝ},
  t ∈ Set.Icc 0 T → ∀ (x : E), ‖↑(WithLp.fst ↑g.u) (t, x)‖ ≤ t * ‖g.ut‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {t} ht x =>
  have h :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun s hs => g.hasDeriv_time s hs x)
      (fun s x_1 => Poincare.ParabolicHolder.norm_le g.ut (s, x)) (convex_Icc 0 T)
      (have this := ⟨le_rfl, LE.le.trans ht.left ht.right⟩;
      this)
      ht;
  Eq.mpr (id ge_iff_le._simp_1)
    (Eq.mp
      (congr
        (congrArg LE.le
          (congrArg norm
            (Eq.trans (congrArg (HSub.hSub (↑(WithLp.fst ↑g.u) (t, x))) (g.zero_trace x))
              (sub_zero (↑(WithLp.fst ↑g.u) (t, x))))))
        (Eq.trans (congrArg (HMul.hMul ‖↑g.ut‖) (Eq.trans (congrArg norm (sub_zero t)) (Real.norm_of_nonneg ht.left)))
          (mul_comm ‖↑g.ut‖ t)))
      h)
theorem Poincare.HeatDuhamelHeatEquation.laplacian_eq_hessian_trace : ∀ (g : Poincare.ClosedSmoothModel 3 → ℝ)
  (x : Poincare.ClosedSmoothModel 3),
  Laplacian.laplacian g x =
    ∑ i, ((fderiv ℝ (fderiv ℝ g) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) :=
fun g x =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          _a x =
            ∑ i,
              ((fderiv ℝ (fderiv ℝ g) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g (EuclideanSpace.basisFun (Fin 3) ℝ))))
    (of_eq_true
      (Eq.trans
        (congr
          (congrArg Eq
            (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
              Eq.trans
                (Eq.trans
                  (congrArg (⇑(iteratedFDeriv ℝ 2 g x))
                    (congr (congrArg Matrix.vecCons (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1))
                      (congrFun' (congrArg Matrix.vecCons (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)) ![])))
                  (iteratedFDeriv_two_apply g x ![EuclideanSpace.single x_1 1, EuclideanSpace.single x_1 1]))
                (congrArg (⇑((fderiv ℝ (fderiv ℝ g) x) (EuclideanSpace.single x_1 1)))
                  (Matrix.cons_val_fin_one (EuclideanSpace.single x_1 1) ![] 0))))
          (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
            congr
              (congrArg DFunLike.coe
                (congrArg (⇑(fderiv ℝ (fderiv ℝ g) x)) (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)))
              (EuclideanSpace.basisFun_apply (Fin 3) ℝ x_1)))
        (eq_self (∑ x_1, ((fderiv ℝ (fderiv ℝ g) x) (EuclideanSpace.single x_1 1)) (EuclideanSpace.single x_1 1)))))
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ParabolicHolder.Y α T ℝ),
                  ∃ G,
                    (∀ p ∈ ParabolicHolder.cylinder T,
                        ↑(WithLp.fst ↑G.u) p =
                          ∫ (s : ℝ) in 0..p.1, heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                      ‖G‖ ≤ C * ‖f‖ : Prop
```

### 003-trace

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 003-trace.lean
@@ -0,0 +1,33 @@
+import Poincare.Global.MovingLimitLeibniz
+import Poincare.Global.DuhamelParabolicHolderSeminorm
+import Poincare.Global.ParabolicSolutionGraph
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Interval Laplacian
+
+namespace Poincare.DuhamelSolutionOperatorBound
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+open HeatDuhamelHessianDifferentiation HeatDuhamelHeatEquation ParabolicHolder
+
+/-- The three coordinate diagonal evaluations are bounded by three operator norms. -/
+theorem abs_trace_le (A : E →L[ℝ] E →L[ℝ] ℝ) :
+    |∑ i : Fin 3, A (e i) (e i)| ≤ 3 * ‖A‖ := by
+  calc
+    |∑ i : Fin 3, A (e i) (e i)| ≤ ∑ i : Fin 3, ‖A (e i) (e i)‖ := by
+      simpa only [Real.norm_eq_abs] using
+        norm_sum_le Finset.univ (fun i : Fin 3 => A (e i) (e i))
+    _ ≤ ∑ _i : Fin 3, ‖A‖ := by
+      apply Finset.sum_le_sum
+      intro i _
+      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
+        ContinuousLinearMap.le_opNorm₂ A (e i) (e i)
+    _ = 3 * ‖A‖ := by simp; ring
+
+end Poincare.DuhamelSolutionOperatorBound
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:31:28: error: No goals to be solved
```

### 004-trace

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 004-trace.lean
@@ -31 +31 @@
-    _ = 3 * ‖A‖ := by simp; ring
+    _ = 3 * ‖A‖ := by simp
```

Actual compiler output:

```text
```

### 005-time-sup

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 005-time-sup.lean
@@ -32,0 +33,33 @@
+/-- The within-interval time derivative has the expected sup estimate. -/
+theorem duhamel_time_derivative_bound :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun r => u r x) (f (t,x) + (Δ (u t)) x) (Icc 0 T) t ∧
+      |f (t,x) + (Δ (u t)) x| ≤ M + 3 * C * K * t ^ (α / 2) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  dsimp only
+  intro t ht x
+  have hd := (MovingLimitLeibniz.duhamel_solves_heat_equation
+    α hα hα1 T hT hT1 f M K hM hK hf hfM hfK).2 t ht x
+  rw [← laplacian_eq_hessian_trace] at hd
+  refine ⟨hd, ?_⟩
+  have hb := ((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht x).2.2.2
+  rw [laplacian_eq_hessian_trace]
+  calc
+    _ ≤ |f (t,x)| + 3 * ‖fderiv ℝ (fderiv ℝ (fun z : E =>
+        ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) z)) x‖ :=
+      (abs_add_le _ _).trans (add_le_add_left (abs_trace_le _) _)
+    _ ≤ M + 3 * (C * K * t ^ (α / 2)) :=
+      add_le_add (hfM t ht x) (mul_le_mul_of_nonneg_left hb (by norm_num))
+    _ = M + 3 * C * K * t ^ (α / 2) := by ring
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:61:29: error: Application type mismatch: The argument
  add_le_add_left (abs_trace_le ?m.377) ?m.378
has type
  |∑ i, (?m.377 (e i)) (e i)| + ?m.378 ≤ 3 * ‖?m.377‖ + ?m.378
but is expected to have type
  |f (t, x)| +
      |∑ i,
          ((fderiv ℝ (fderiv ℝ fun x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x) x) (e i))
            (e i)| ≤
    |f (t, x)| + 3 * ‖fderiv ℝ (fderiv ℝ fun z => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) z) x‖
in the application
  LE.le.trans
    (abs_add_le (f (t, x))
      (∑ i,
        ((fderiv ℝ (fderiv ℝ fun x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x) x) (e i)) (e i)))
    (add_le_add_left (abs_trace_le ?m.377) ?m.378)
```

### 006-time-sup

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 006-time-sup.lean
@@ -61 +61 @@
-      (abs_add_le _ _).trans (add_le_add_left (abs_trace_le _) _)
+      (abs_add_le _ _).trans (add_le_add le_rfl (abs_trace_le _))
```

Actual compiler output:

```text
```

### 007-time-holder

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 007-time-holder.lean
@@ -65,0 +66,43 @@
+/-- Tracing the parabolic Hessian increment controls the time derivative increment. -/
+theorem duhamel_time_derivative_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    HasHolderBound α (cylinder T) f K →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    HasHolderBound α (cylinder T) (fun p => f p + (Δ (u p.1)) p.2)
+      (K + 3 * C * K) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ :=
+    DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
+      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using
+      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  dsimp only
+  intro p hp q hq
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  have hb := hCb T hT hT1 f M K hM hK hf hfM hspace p hp q hq
+  have htrace : |(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2| ≤
+      3 * ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 -
+        fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
+    simpa only [laplacian_eq_hessian_trace, ContinuousLinearMap.sub_apply,
+      Finset.sum_sub_distrib] using abs_trace_le
+        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
+  change ‖(f p + (Δ (u p.1)) p.2) - (f q + (Δ (u q.1)) q.2)‖ ≤ _
+  rw [show f p + (Δ (u p.1)) p.2 - (f q + (Δ (u q.1)) q.2) =
+    (f p - f q) + ((Δ (u p.1)) p.2 - (Δ (u q.1)) q.2) by ring]
+  calc
+    _ ≤ ‖f p - f q‖ + ‖(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2‖ := norm_add_le _ _
+    _ ≤ K * parabolicDist p q ^ α + 3 * (C * K * parabolicDist p q ^ α) :=
+      add_le_add (hfK p hp q hq)
+        (htrace.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
+    _ = (K + 3 * C * K) * parabolicDist p q ^ α := by ring
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:100:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  f p + ?m.471 - (f q + ?m.473)
in the target expression
  ‖f p + Δ (u p.1) p.2 - (f q + Δ (u q.1) q.2)‖ ≤ (K + 3 * C * K) * parabolicDist p q ^ α

α : ℝ
hα : 0 < α
hα1 : α < 1
C : ℝ
hC : 0 < C
hCb :
  ∀ (T : ℝ),
    0 < T →
      T ≤ 1 →
        ∀ (f : ℝ × E → ℝ) (M K : ℝ),
          0 ≤ M →
            0 ≤ K →
              ContinuousOn f (Icc 0 T ×ˢ univ) →
                (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                  (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                    have u := fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x;
                    ∀ p ∈ cylinder T,
                      ∀ q ∈ cylinder T,
                        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
                          C * K * parabolicDist p q ^ α
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM : 0 ≤ M
hK : 0 ≤ K
hf : ContinuousOn f (cylinder T)
hfM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hfK : HasHolderBound α (cylinder T) f K
hspace : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
p : ℝ × E
hp : p ∈ cylinder T
q : ℝ × E
hq : q ∈ cylinder T
u : ℝ → E → ℝ := fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x
hb :
  ‖fderiv ℝ (fderiv ℝ ((fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x) p.1)) p.2 -
        fderiv ℝ (fderiv ℝ ((fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x) q.1)) q.2‖ ≤
    C * K * parabolicDist p q ^ α
htrace : |Δ (u p.1) p.2 - Δ (u q.1) q.2| ≤ 3 * ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
⊢ ‖f p + Δ (u p.1) p.2 - (f q + Δ (u q.1) q.2)‖ ≤ (K + 3 * C * K) * parabolicDist p q ^ α
```

### 008-time-holder

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 008-time-holder.lean
@@ -100,2 +100 @@
-  rw [show f p + (Δ (u p.1)) p.2 - (f q + (Δ (u q.1)) q.2) =
-    (f p - f q) + ((Δ (u p.1)) p.2 - (Δ (u q.1)) q.2) by ring]
+  rw [add_sub_add_comm]
```

Actual compiler output:

```text
```

### 009-gradient-sup

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 009-gradient-sup.lean
@@ -107,0 +108,27 @@
+/-- Integrating the gradient kernel gives the sharp square-root time factor. -/
+theorem duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
+    ‖fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t-s) (fun y => f (s,y)) z) x‖ ≤
+      2 * M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * Real.sqrt t := by
+  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
+  let A := M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖)
+  have hb : ‖∫ s in (0 : ℝ)..t,
+      fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) x‖ ≤
+      ∫ s in (0 : ℝ)..t, A * (t-s) ^ (-(1/2 : ℝ)) := by
+    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
+      (intervalIntegrable_gradient_majorant t A)
+    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
+    have hc : Continuous (fun y : E => f (s,y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) hc.aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s hsT) x
+  have he := HeatDuhamelSpatialHolderHessian.integral_hessian_majorant zero_lt_one t A
+  norm_num at he
+  rw [he] at hb
+  simpa [A, Real.sqrt_eq_rpow, mul_assoc, mul_left_comm, mul_comm] using hb
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:121:6: error: Application type mismatch: The argument
  intervalIntegrable_gradient_majorant t A
has type
  IntervalIntegrable (fun s => A * (t - s) ^ (-(1 / 2))) volume 0 t
but is expected to have type
  ∀ᵐ (t_1 : ℝ) ∂?m.257, t_1 ∈ Ioc 0 t → ‖?m.256 t_1‖ ≤ ?m.258 t_1
in the application
  intervalIntegral.norm_integral_le_of_norm_le ht.left (intervalIntegrable_gradient_majorant t A)
Poincare/Global/DuhamelSolutionOperatorBound.lean:122:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Ι 0 t
in the target expression
  IntervalIntegrable (fun t_1 => A * (t - t_1) ^ (-(1 / 2))) volume 0 t

T t M : ℝ
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hf : ContinuousOn f (cylinder T)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
A : ℝ := ⋯
⊢ IntervalIntegrable (fun t_1 => A * (t - t_1) ^ (-(1 / 2))) volume 0 t
Poincare/Global/DuhamelSolutionOperatorBound.lean:132:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  A * ∫ (x : ℝ) in 0..t, (t - x) ^ (-(1 / 2))
in the target expression
  ‖∫ (s : ℝ) in 0..t, fderiv ℝ (heatSolution (t - s) fun y => f (s, y)) x‖ ≤ ∫ (s : ℝ) in 0..t, A * (t - s) ^ (-(1 / 2))

T t M : ℝ
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hf : ContinuousOn f (cylinder T)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
A : ℝ := M * ∫ (y : E), ‖fderiv ℝ (heatKernel 1) y‖
hb :
  ‖∫ (s : ℝ) in 0..t, fderiv ℝ (heatSolution (t - s) fun y => f (s, y)) x‖ ≤ ∫ (s : ℝ) in 0..t, A * (t - s) ^ (-(1 / 2))
he : A * ∫ (x : ℝ) in 0..t, (t - x) ^ (-(1 / 2)) = A * 2 * t ^ (1 / 2)
⊢ ‖∫ (s : ℝ) in 0..t, fderiv ℝ (heatSolution (t - s) fun y => f (s, y)) x‖ ≤
    (2 * M * ∫ (y : E), ‖fderiv ℝ (heatKernel 1) y‖) * √t
```

### 010-gradient-sup

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 010-gradient-sup.lean
@@ -120,3 +120,5 @@
-    apply intervalIntegral.norm_integral_le_of_norm_le ht.1
-      (intervalIntegrable_gradient_majorant t A)
-    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
+      ← restrict_Ioo_eq_restrict_Ioc]
+    apply MeasureTheory.norm_integral_le_of_norm_le
+      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+        (intervalIntegrable_gradient_majorant t A))
@@ -131 +133 @@
-  norm_num at he
+  norm_num only [div_one, show (1 : ℝ) / 2 - 1 = -(1/2 : ℝ) by norm_num] at he
```

Actual compiler output:

```text
```

### 011-value-time

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 011-value-time.lean
@@ -136,0 +137,34 @@
+/-- A uniform time-derivative bound controls all value increments and the initial trace. -/
+theorem duhamel_value_time_estimates :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    (∀ t ∈ Icc 0 T, ∀ x : E, |u t x| ≤ t * (M + 3 * C * K * T ^ (α/2))) ∧
+    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x : E,
+      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s|) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  have hd := hCb T hT hT1 f M K hM hK hf hfM hfK
+  have hb (r : ℝ) (hr : r ∈ Icc 0 T) (x : E) :
+      ‖f (r,x) + (Δ (u r)) x‖ ≤ M + 3 * C * K * T ^ (α/2) := by
+    apply (hd r hr x).2.trans
+    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow hr.1 hr.2 (by linarith)) (by positivity))
+  have hi (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
+      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s| := by
+    simpa only [Real.norm_eq_abs] using
+      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+        (fun r hr => (hd r hr x).1) (fun r hr => hb r hr x) (convex_Icc (0 : ℝ) T) hs ht
+  refine ⟨?_, hi⟩
+  intro t ht x
+  simpa [u, abs_of_nonneg ht.1, mul_comm] using hi t ht 0 ⟨le_rfl, hT.le⟩ x
+
```

Actual compiler output:

```text
```

### 012-interpolation

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 012-interpolation.lean
@@ -170,0 +171,22 @@
+/-- Bounded Lipschitz increments give every intermediate Hölder exponent. -/
+theorem holder_of_bounded_lipschitz {F : Type*} [NormedAddCommGroup F]
+    {α A B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
+    {g : E → F} (hg : ∀ x, ‖g x‖ ≤ A)
+    (hlip : ∀ x y, ‖g x - g y‖ ≤ B * ‖x-y‖) (x y : E) :
+    ‖g x - g y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+  by_cases hr : ‖x-y‖ ≤ 1
+  · have hp : ‖x-y‖ ≤ ‖x-y‖ ^ α := by
+      simpa only [Real.rpow_one] using
+        Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hr hα hα1
+    exact (hlip x y).trans ((mul_le_mul_of_nonneg_left hp hB).trans
+      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2*A+B)
+        (Real.rpow_nonneg (norm_nonneg _) _)))
+  · have hp : 1 ≤ ‖x-y‖ ^ α := Real.one_le_rpow (le_of_not_ge hr) hα
+    calc
+      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
+      _ ≤ 2*A := by linarith [hg x, hg y]
+      _ ≤ (2*A+B) * ‖x-y‖ ^ α := by
+        calc
+          2*A ≤ 2*A+B := by linarith
+          _ ≤ (2*A+B) * ‖x-y‖ ^ α := le_mul_of_one_le_right (by positivity) hp
+
```

Actual compiler output:

```text
```

### 013-gradient-space

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 013-gradient-space.lean
@@ -192,0 +193,40 @@
+/-- The gradient is spatially Hölder with a constant uniform on short time intervals. -/
+theorem duhamel_gradient_spatial_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    ∀ t ∈ Icc 0 T, ∀ x y : E,
+      ‖fderiv ℝ (u t) x - fderiv ℝ (u t) y‖ ≤ C * (M+K) * ‖x-y‖ ^ α := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨4*J+C, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  dsimp only
+  intro t ht x y
+  let u : E → ℝ := fun z => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun w => f (s,w)) z
+  have hg (z : E) : ‖fderiv ℝ u z‖ ≤ 2*M*J :=
+    (duhamel_gradient_bound ht hf hfM z).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
+  have hh (z : E) : ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ C*K :=
+    (((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht z).2.2.2).trans
+      (mul_le_of_le_one_right (by positivity)
+        (Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)))
+  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
+    ((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
+      (m := 1) (by norm_num)).differentiable_one
+  have hlip (a b : E) : ‖fderiv ℝ u a - fderiv ℝ u b‖ ≤ C*K*‖a-b‖ :=
+    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
+      (fun z _ => hh z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ b) (mem_univ a)
+  have hb := holder_of_bounded_lipschitz hα.le hα1.le
+    (by positivity : 0 ≤ 2*M*J) (by positivity : 0 ≤ C*K) hg hlip x y
+  exact hb.trans (mul_le_mul_of_nonneg_right
+    (by nlinarith [mul_nonneg hJ hK, mul_nonneg hC.le hM] :
+      2*(2*M*J)+C*K ≤ (4*J+C)*(M+K)) (Real.rpow_nonneg (norm_nonneg _) _))
+
```

Actual compiler output:

```text
```

### 014-value-holder

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 014-value-holder.lean
@@ -232,0 +233,68 @@
+/-- Value increments obey a parabolic Hölder bound uniform for times at most one. -/
+theorem duhamel_value_parabolic_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    HasHolderBound α (cylinder T)
+      (fun p : ℝ × E => ∫ s in (0 : ℝ)..p.1,
+        heatSolution (p.1-s) (fun y => f (s,y)) p.2) (C * (M+K)) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_value_time_estimates α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨3+9*C+2*J, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  let D := M+3*C*K
+  have hD : 0 ≤ D := by dsimp [D]; positivity
+  have hd : M+3*C*K*T^(α/2) ≤ D := by
+    exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity)
+      (Real.rpow_le_one hT.le hT1 (by linarith)))
+  have hv := hCb T hT hT1 f M K hM hK hf hfM hfK
+  have hu (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖u t x‖ ≤ D := by
+    exact (hv.1 t ht x).trans ((mul_le_mul_of_nonneg_left hd ht.1).trans
+      (mul_le_of_le_one_left hD (ht.2.trans hT1)))
+  have hg (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖fderiv ℝ (u t) x‖ ≤ 2*M*J :=
+    (duhamel_gradient_bound ht hf hfM x).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
+  intro p hp q hq
+  have hs : ‖u p.1 p.2 - u p.1 q.2‖ ≤ (2*D+2*M*J)*‖p.2-q.2‖^α := by
+    apply holder_of_bounded_lipschitz hα.le hα1.le hD (by positivity) (hu p.1 hp.1)
+    intro a b
+    exact Convex.norm_image_sub_le_of_norm_fderiv_le
+      (fun z _ => (hasFDerivAt_duhamel hp.1 hf hfM z).differentiableAt)
+      (fun z _ => hg p.1 hp.1 z) (convex_univ : Convex ℝ (univ : Set E))
+      (mem_univ b) (mem_univ a)
+  have hab : |p.1-q.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2],
+    by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]⟩
+  have htp : |p.1-q.1| ≤ parabolicDist p q ^ α := by
+    calc
+      |p.1-q.1| ≤ |p.1-q.1|^(α/2) := by
+        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
+          (abs_nonneg (p.1-q.1)) hab (by linarith : 0 ≤ α/2) (by linarith : α/2 ≤ 1)
+      _ = (Real.sqrt |p.1-q.1|)^α := by
+        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
+        congr 1
+        ring
+      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
+        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
+  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
+  have ht : ‖u p.1 q.2 - u q.1 q.2‖ ≤ D * parabolicDist p q ^ α :=
+    (hv.2 p.1 hp.1 q.1 hq.1 q.2).trans
+      ((mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left htp hD))
+  calc
+    ‖u p.1 p.2 - u q.1 q.2‖ ≤ ‖u p.1 p.2 - u p.1 q.2‖ + ‖u p.1 q.2 - u q.1 q.2‖ :=
+      norm_sub_le_norm_sub_add_norm_sub ..
+    _ ≤ (2*D+2*M*J)*parabolicDist p q ^ α + D*parabolicDist p q ^ α :=
+      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity))) ht
+    _ ≤ (3+9*C+2*J)*(M+K)*parabolicDist p q ^ α := by
+      rw [← add_mul]
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (parabolicDist_nonneg _ _) _)
+      dsimp [D]
+      nlinarith [mul_nonneg hC.le hM, mul_nonneg hJ hK]
+
```

Actual compiler output:

```text
```

### 015-gradient-data-difference

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 015-gradient-data-difference.lean
@@ -300,0 +301,19 @@
+/-- A difference of bounded data has the same gradient kernel estimate. -/
+theorem gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
+    {f g : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hg : AEStronglyMeasurable g volume) (hfM : ∀ y, ‖f y‖ ≤ M)
+    (hgN : ∀ y, ‖g y‖ ≤ N) (hL : ∀ y, ‖f y - g y‖ ≤ L) (x : E) :
+    ‖fderiv ℝ (heatSolution t f) x - fderiv ℝ (heatSolution t g) x‖ ≤
+      L * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1/2 : ℝ)) := by
+  have hi := integrable_smul_fderiv_heatKernel_sub ht hf hfM x
+  have hj := integrable_smul_fderiv_heatKernel_sub ht hg hgN x
+  rw [(heatSolution_hasFDerivAt ht hf hfM x).fderiv,
+    (heatSolution_hasFDerivAt ht hg hgN x).fderiv, ← integral_sub hi hj]
+  have he : (fun y : E => f y • fderiv ℝ (heatKernel t) (x-y) -
+      g y • fderiv ℝ (heatKernel t) (x-y)) =
+      fun y => (f y - g y) • fderiv ℝ (heatKernel t) (x-y) := by
+    ext y v
+    simp [sub_smul]
+  rw [he, ← (heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv]
+  exact norm_gradient_heatSolution_le ht (hf.sub hg) hL x
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:317:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (y : E), (f - g) y • fderiv ℝ (fun u => heatKernel t u) (x - y)
in the target expression
  ‖∫ (y : E), (f y - g y) • fderiv ℝ (heatKernel t) (x - y)‖ ≤
    (L * ∫ (y : E), ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1 / 2))

t M N L : ℝ
ht : 0 < t
f g : E → ℝ
hf : AEStronglyMeasurable f volume
hg : AEStronglyMeasurable g volume
hfM : ∀ (y : E), ‖f y‖ ≤ M
hgN : ∀ (y : E), ‖g y‖ ≤ N
hL : ∀ (y : E), ‖f y - g y‖ ≤ L
x : E
hi : Integrable (fun y => f y • fderiv ℝ (fun u => heatKernel t u) (x - y)) volume
hj : Integrable (fun y => g y • fderiv ℝ (fun u => heatKernel t u) (x - y)) volume
he :
  (fun y => f y • fderiv ℝ (heatKernel t) (x - y) - g y • fderiv ℝ (heatKernel t) (x - y)) = fun y =>
    (f y - g y) • fderiv ℝ (heatKernel t) (x - y)
⊢ ‖∫ (y : E), (f y - g y) • fderiv ℝ (heatKernel t) (x - y)‖ ≤
    (L * ∫ (y : E), ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1 / 2))
```

### 016-gradient-data-difference

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 016-gradient-data-difference.lean
@@ -317,2 +317,4 @@
-  rw [he, ← (heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv]
-  exact norm_gradient_heatSolution_le ht (hf.sub hg) hL x
+  rw [he]
+  have hb := norm_gradient_heatSolution_le ht (hf.sub hg) hL x
+  rw [(heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv] at hb
+  exact hb
```

Actual compiler output:

```text
```

### 017-gradient-reversed

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 017-gradient-reversed.lean
@@ -321,0 +322,13 @@
+/-- Reversing Duhamel time keeps the gradient kernel fixed when comparing forcing times. -/
+theorem duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
+    fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t-s) (fun y => f (s,y)) z) x =
+      ∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x := by
+  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
+  have he := intervalIntegral.integral_comp_sub_left
+    (fun s : ℝ => fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x)
+    (a := 0) (b := t) t
+  simpa only [sub_sub_cancel, sub_self, sub_zero] using he
+
```

Actual compiler output:

```text
```

### 018-inverse-sqrt

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 018-inverse-sqrt.lean
@@ -334,0 +335,31 @@
+/-- The inverse square-root majorant controls an arbitrary nonnegative time interval. -/
+theorem norm_integral_inverse_sqrt_le {F : Type*} [NormedAddCommGroup F]
+    [NormedSpace ℝ F] {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A)
+    {g : ℝ → F} (hg : ∀ r ∈ Ioo a b, ‖g r‖ ≤ A * r ^ (-(1/2 : ℝ))) :
+    ‖∫ r in a..b, g r‖ ≤ 2*A*Real.sqrt (b-a) := by
+  have hb : 0 ≤ b := ha.trans hab
+  have hi : IntervalIntegrable (fun r : ℝ => A * r ^ (-(1/2 : ℝ))) volume a b :=
+    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))).const_mul A
+  have hbound : ‖∫ r in a..b, g r‖ ≤ ∫ r in a..b, A * r ^ (-(1/2 : ℝ)) := by
+    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
+      ← restrict_Ioo_eq_restrict_Ioc]
+    apply MeasureTheory.norm_integral_le_of_norm_le
+      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
+    exact hg r hr
+  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))] at hbound
+  norm_num only [show -(1/2 : ℝ)+1 = 1/2 by norm_num] at hbound
+  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hbound
+  have hs : Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b-a) := by
+    have h1 := Real.sq_sqrt ha
+    have h2 := Real.sq_sqrt hb
+    have h3 := Real.sq_sqrt (sub_nonneg.mpr hab)
+    have h4 := Real.sqrt_nonneg a
+    have h5 := Real.sqrt_nonneg b
+    have h6 := Real.sqrt_nonneg (b-a)
+    nlinarith [mul_nonneg h4 h6]
+  calc
+    _ ≤ A * ((Real.sqrt b - Real.sqrt a) / (1/2)) := hbound
+    _ = 2*A*(Real.sqrt b - Real.sqrt a) := by ring
+    _ ≤ 2*A*Real.sqrt (b-a) := mul_le_mul_of_nonneg_left hs (by positivity)
+
```

Actual compiler output:

```text
```

### 019-gradient-time

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 019-gradient-time.lean
@@ -365,0 +366,71 @@
+/-- Reversed time separates a forcing increment from a short gradient tail. -/
+theorem duhamel_gradient_time_holder_of_le {α T s t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
+    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t)
+    (hM : 0 ≤ M) (hK : 0 ≤ K) {f : ℝ × E → ℝ}
+    (hf : ContinuousOn f (cylinder T))
+    (hfM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r,y)| ≤ M)
+    (hfK : HasHolderBound α (cylinder T) f K) (x : E) :
+    let u : ℝ → E → ℝ := fun r z =>
+      ∫ v in (0 : ℝ)..r, heatSolution (r-v) (fun y => f (v,y)) z
+    ‖fderiv ℝ (u t) x - fderiv ℝ (u s) x‖ ≤
+      2 * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * (M+K) * (t-s)^(α/2) := by
+  dsimp only
+  rw [duhamel_gradient_reversed ht hf hfM, duhamel_gradient_reversed hs hf hfM]
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  let v : ℝ → ℝ → E →L[ℝ] ℝ := fun a r =>
+    fderiv ℝ (heatSolution r (fun y => f (a-r,y))) x
+  have hi (a : ℝ) (ha : a ∈ Icc 0 T) : IntervalIntegrable (v a) volume 0 a := by
+    have h := (intervalIntegrable_gradient_heatSolution_time ha hf hfM x).comp_sub_left a
+    simpa only [v, sub_zero, sub_self, sub_sub_cancel] using h.symm
+  have hsub0 : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
+    simpa only [uIcc_of_le hs.1, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl hst
+  have hsub1 : uIcc s t ⊆ uIcc 0 t := by
+    simpa only [uIcc_of_le hst, uIcc_of_le ht.1] using Icc_subset_Icc hs.1 le_rfl
+  have hit0 := (hi t ht).mono_set hsub0
+  have hit1 := (hi t ht).mono_set hsub1
+  have hc (a : ℝ) (ha : a ∈ Icc 0 T) (r : ℝ) (hr : r ∈ Icc 0 a) :
+      Continuous (fun y : E => f (a-r,y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨⟨by linarith [hr.2], by linarith [hr.1, ha.2]⟩, mem_univ y⟩)
+  have hb0 : ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ ≤
+      2 * (K * (t-s)^(α/2) * J) * Real.sqrt s := by
+    simpa only [sub_zero] using norm_integral_inverse_sqrt_le
+      (a := 0) (b := s) le_rfl hs.1 (by positivity : 0 ≤ K*(t-s)^(α/2)*J)
+      (g := fun r => v t r - v s r) (by
+        intro r hr
+        have hrt : r ∈ Icc 0 t := ⟨hr.1.le, hr.2.le.trans hst⟩
+        have hrs : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
+        apply gradient_heatSolution_sub_bound hr.1 (hc t ht r hrt).aestronglyMeasurable
+          (hc s hs r hrs).aestronglyMeasurable
+          (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y)
+          (fun y => hfM (s-r) ⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩ y)
+        intro y
+        have h := hfK (t-r,y) ⟨⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩, mem_univ y⟩
+          (s-r,y) ⟨⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩, mem_univ y⟩
+        simpa [parabolicDist, sub_sub_sub_cancel_right, abs_of_nonneg (sub_nonneg.mpr hst),
+          Real.sqrt_eq_rpow, ← Real.rpow_mul (sub_nonneg.mpr hst), mul_comm, div_eq_mul_inv] using h)
+  have hb1 : ‖∫ r in s..t, v t r‖ ≤ 2*(M*J)*Real.sqrt (t-s) := by
+    apply norm_integral_inverse_sqrt_le hs.1 hst (by positivity)
+    intro r hr
+    have hrt : r ∈ Icc 0 t := ⟨hs.1.trans hr.1.le, hr.2.le⟩
+    exact norm_gradient_heatSolution_le (lt_of_le_of_lt hs.1 hr.1)
+      (hc t ht r hrt).aestronglyMeasurable
+      (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y) x
+  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
+  have hδ1 : t-s ≤ 1 := by linarith [ht.2, hs.1]
+  have hpow : Real.sqrt (t-s) ≤ (t-s)^(α/2) := by
+    rw [Real.sqrt_eq_rpow]
+    exact Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by linarith) (by linarith)
+  change ‖(∫ r in (0 : ℝ)..t, v t r) - ∫ r in (0 : ℝ)..s, v s r‖ ≤ _
+  rw [← intervalIntegral.integral_add_adjacent_intervals hit0 hit1,
+    add_sub_right_comm, ← intervalIntegral.integral_sub hit0 (hi s hs)]
+  calc
+    _ ≤ ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ + ‖∫ r in s..t, v t r‖ := norm_add_le _ _
+    _ ≤ 2*(K*(t-s)^(α/2)*J)*Real.sqrt s + 2*(M*J)*Real.sqrt (t-s) := add_le_add hb0 hb1
+    _ ≤ 2*(K*(t-s)^(α/2)*J) + 2*(M*J)*(t-s)^(α/2) :=
+      add_le_add (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hs.2.trans hT1)))
+        (mul_le_mul_of_nonneg_left hpow (by positivity))
+    _ = 2*J*(M+K)*(t-s)^(α/2) := by ring
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:400:40: error: failed to prove positivity/nonnegativity/nonzeroness
```

### 020-gradient-time

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 020-gradient-time.lean
@@ -396,0 +397 @@
+  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
@@ -421 +421,0 @@
-  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
```

Actual compiler output:

```text
```

### 021-gradient-holder

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 021-gradient-holder.lean
@@ -436,0 +437,52 @@
+/-- Spatial interpolation and reversed-time integration give the full gradient estimate. -/
+theorem duhamel_gradient_parabolic_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    HasHolderBound α (cylinder T) f K →
+    HasHolderBound α (cylinder T)
+      (fun p : ℝ × E => fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..p.1,
+        heatSolution (p.1-s) (fun y => f (s,y)) z) p.2) (C * (M+K)) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_gradient_spatial_holder α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨C+2*J, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
+      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using
+      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  intro p hp q hq
+  have hs := hCb T hT hT1 f M K hM hK hf hfM hspace p.1 hp.1 p.2 q.2
+  have ht : ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ ≤
+      2*J*(M+K)*|p.1-q.1|^(α/2) := by
+    rcases le_total q.1 p.1 with hqp | hpq
+    · simpa only [abs_of_nonneg (sub_nonneg.mpr hqp)] using
+        duhamel_gradient_time_holder_of_le hα hα1 hT1 hq.1 hp.1 hqp hM hK hf hfM hfK q.2
+    · simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hpq), neg_sub] using
+        duhamel_gradient_time_holder_of_le hα hα1 hT1 hp.1 hq.1 hpq hM hK hf hfM hfK q.2
+  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
+  have htp : |p.1-q.1|^(α/2) ≤ parabolicDist p q ^ α := by
+    calc
+      _ = (Real.sqrt |p.1-q.1|)^α := by
+        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
+        congr 1
+        ring
+      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
+        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
+  calc
+    ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u q.1) q.2‖ ≤
+        ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u p.1) q.2‖ +
+        ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ := norm_sub_le_norm_sub_add_norm_sub ..
+    _ ≤ C*(M+K)*parabolicDist p q ^ α + 2*J*(M+K)*parabolicDist p q ^ α :=
+      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity)))
+        (ht.trans (mul_le_mul_of_nonneg_left htp (by positivity)))
+    _ = (C+2*J)*(M+K)*parabolicDist p q ^ α := by ring
+
```

Actual compiler output:

```text
```

### 022-holder-continuity

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 022-holder-continuity.lean
@@ -488,0 +489,17 @@
+/-- Positive parabolic Hölder control implies continuity on the cylinder. -/
+theorem continuousOn_of_hasHolderBound {F : Type*} [NormedAddCommGroup F]
+    {α T K : ℝ} (hα : 0 < α) {g : ℝ × E → F}
+    (hg : HasHolderBound α (cylinder T) g K) : ContinuousOn g (cylinder T) := by
+  intro p hp
+  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
+  have hc : Continuous (fun q : ℝ × E => K * parabolicDist q p ^ α) := by
+    dsimp [parabolicDist]
+    fun_prop (disch := positivity)
+  have hz : K * parabolicDist p p ^ α = 0 := by
+    simp [parabolicDist, Real.zero_rpow hα.ne']
+  have hlim := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
+  rw [hz] at hlim
+  apply squeeze_zero' (Filter.Eventually.of_forall (fun q => norm_nonneg (g q - g p))) _ hlim
+  filter_upwards [self_mem_nhdsWithin] with q hq
+  exact hg q hq p hp
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:15: error: don't know how to synthesize implicit argument `z`
  @Filter.Tendsto.mono_left (ℝ × E) ℝ (fun q => K * parabolicDist q p ^ α) (nhds ?m.261) (nhdsWithin ?m.261 ?m.262)
    (nhds (K * parabolicDist ?m.261 p ^ α)) (ContinuousAt.tendsto (Continuous.continuousAt hc)) nhdsWithin_le_nhds
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ Filter ℝ
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:15: error: don't know how to synthesize implicit argument `y`
  @Filter.Tendsto.mono_left (ℝ × E) ℝ (fun q => K * parabolicDist q p ^ α) (nhds ?m.261) (nhdsWithin ?m.261 ?m.262)
    (nhds (K * parabolicDist ?m.261 p ^ α)) (ContinuousAt.tendsto (Continuous.continuousAt hc)) nhdsWithin_le_nhds
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ Filter (ℝ × E)
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:15: error: don't know how to synthesize implicit argument `x`
  @Filter.Tendsto.mono_left (ℝ × E) ℝ (fun q => K * parabolicDist q p ^ α) (nhds ?m.261) (nhdsWithin ?m.261 ?m.262)
    (nhds (K * parabolicDist ?m.261 p ^ α)) (ContinuousAt.tendsto (Continuous.continuousAt hc)) nhdsWithin_le_nhds
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ Filter (ℝ × E)
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:49: error: don't know how to synthesize implicit argument `s`
  @nhdsWithin_le_nhds (ℝ × E) instTopologicalSpaceProd ?m.261 ?m.262
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ Set (ℝ × E)
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:49: error: don't know how to synthesize implicit argument `a`
  @nhdsWithin_le_nhds (ℝ × E) instTopologicalSpaceProd ?m.261 ?m.262
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ ℝ × E
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:15: error: don't know how to synthesize implicit argument `x`
  @ContinuousAt.tendsto (ℝ × E) ℝ instTopologicalSpaceProd PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun q => K * parabolicDist q p ^ α) ?m.261 (Continuous.continuousAt hc)
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ ℝ × E
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:15: error: don't know how to synthesize implicit argument `x`
  @Continuous.continuousAt (ℝ × E) ℝ instTopologicalSpaceProd PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun q => K * parabolicDist q p ^ α) ?m.261 hc
context:
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ ℝ × E
Poincare/Global/DuhamelSolutionOperatorBound.lean:500:7: error: failed to infer `have` declaration type
Poincare/Global/DuhamelSolutionOperatorBound.lean:492:78: error: unsolved goals
F : Type u_1
inst✝ : NormedAddCommGroup F
α T K : ℝ
hα : 0 < α
g : ℝ × E → F
hg : HasHolderBound α (cylinder T) g K
p : ℝ × E
hp : p ∈ cylinder T
hc : Continuous fun q => K * parabolicDist q p ^ α
hz : K * parabolicDist p p ^ α = 0
⊢ Filter.Tendsto (fun «e» => ‖g «e» - g p‖) (nhdsWithin p (cylinder T)) (nhds 0)
```

### 023-holder-continuity

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 023-holder-continuity.lean
@@ -500 +500,3 @@
-  have hlim := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
+  have hlim : Filter.Tendsto (fun q => K * parabolicDist q p ^ α)
+      (nhdsWithin p (cylinder T)) (nhds (K * parabolicDist p p ^ α)) :=
+    hc.continuousAt.continuousWithinAt
```

Actual compiler output:

```text
```

### 024-assembly

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 024-assembly.lean
@@ -507,0 +508,135 @@
+/-- The constant-coefficient Duhamel solution is bounded in the full solution graph norm. -/
+theorem exists_solution_graph_bound :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
+    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
+      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
+        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
+      ‖G‖ ≤ C * ‖f‖ := by
+  intro α hα hα1
+  obtain ⟨A, hA, hAb⟩ := duhamel_hessian_bound α hα hα1
+  obtain ⟨B, hB, hBb⟩ := DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
+  obtain ⟨D, hD, hDb⟩ := duhamel_time_derivative_holder α hα hα1
+  obtain ⟨V, hV, hVb⟩ := duhamel_value_time_estimates α hα hα1
+  obtain ⟨W, hW, hWb⟩ := duhamel_value_parabolic_holder α hα hα1
+  obtain ⟨Q, hQ, hQb⟩ := duhamel_gradient_parabolic_holder α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨(1+3*V)+2*W+(1+3*C)+(1+3*D)+2*J+2*Q+A+B, by positivity, ?_⟩
+  intro T hT hT1 f
+  let N := ‖f‖
+  have hN : 0 ≤ N := norm_nonneg f
+  have hfH : HasHolderBound α (cylinder T) f N := ParabolicHolder.hasHolderBound f
+  have hf : ContinuousOn f (cylinder T) := continuousOn_of_hasHolderBound hα hfH
+  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ N :=
+    fun t _ x => ParabolicHolder.norm_le f (t,x)
+  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x)-f (t,y)| ≤ N*‖x-y‖^α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using hfH (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  let v : ℝ × E → ℝ := fun p => f p + (Δ (u p.1)) p.2
+  let d : ℝ × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (u p.1) p.2
+  let dd : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2
+  have hpow (t : ℝ) (ht : t ∈ Icc 0 T) : t^(α/2) ≤ 1 :=
+    Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)
+  have htime := hCb T hT hT1 f N N hN hN hf hfM hfK
+  have hvalue := hVb T hT hT1 f N N hN hN hf hfM hfK
+  have huB : ∀ p ∈ cylinder T, ‖u p.1 p.2‖ ≤ (1+3*V)*N := by
+    intro p hp
+    have hb : N+3*V*N*T^(α/2) ≤ (1+3*V)*N := by
+      have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*V*N)
+        (hpow T ⟨hT.le, le_rfl⟩)
+      nlinarith
+    exact (hvalue.1 p.1 hp.1 p.2).trans ((mul_le_mul_of_nonneg_left hb hp.1.1).trans
+      (mul_le_of_le_one_left (by positivity) (hp.1.2.trans hT1)))
+  have hvB : ∀ p ∈ cylinder T, ‖v p‖ ≤ (1+3*C)*N := by
+    intro p hp
+    have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*C*N) (hpow p.1 hp.1)
+    have hb := (htime p.1 hp.1 p.2).2
+    change |f p + (Δ (u p.1)) p.2| ≤ _
+    nlinarith
+  have hdB : ∀ p ∈ cylinder T, ‖d p‖ ≤ 2*J*N := by
+    intro p hp
+    have h := (duhamel_gradient_bound hp.1 hf hfM p.2).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hp.1.2.trans hT1)))
+    simpa only [d, J, mul_comm, mul_left_comm, mul_assoc] using h
+  have hddB : ∀ p ∈ cylinder T, ‖dd p‖ ≤ A*N := by
+    intro p hp
+    exact (((hAb T hT hT1 f N N hN hN hf hfM hfK).2 p.1 hp.1 p.2).2.2.2).trans
+      (mul_le_of_le_one_right (by positivity) (hpow p.1 hp.1))
+  have huH : HasHolderBound α (cylinder T) (fun p => u p.1 p.2) (2*W*N) := by
+    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1 <;> ring
+  have hvH : HasHolderBound α (cylinder T) v ((1+3*D)*N) := by
+    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1 <;> ring
+  have hdH : HasHolderBound α (cylinder T) d (2*Q*N) := by
+    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1 <;> ring
+  have hddH : HasHolderBound α (cylinder T) dd (B*N) := hBb T hT hT1 f N N hN hN hf hfM hfK
+  have liftB {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
+      (hb : ∀ p ∈ cylinder T, ‖g p‖ ≤ b) :
+      ∀ p ∈ cylinder T, ‖(cylinder T).indicator g p‖ ≤ b := by
+    intro p hp
+    simpa only [indicator_of_mem hp] using hb p hp
+  have liftH {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
+      (hb : HasHolderBound α (cylinder T) g b) :
+      HasHolderBound α (cylinder T) ((cylinder T).indicator g) b := by
+    intro p hp q hq
+    simpa only [indicator_of_mem hp, indicator_of_mem hq] using hb p hp q hq
+  let iu := (cylinder T).indicator (fun p : ℝ × E => u p.1 p.2)
+  let iv := (cylinder T).indicator v
+  let idu := (cylinder T).indicator d
+  let iddu := (cylinder T).indicator dd
+  have huS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => iu (t,z)) = u t := by
+    funext z
+    exact indicator_of_mem ⟨ht, mem_univ z⟩ _
+  have hdS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => idu (t,z)) = fderiv ℝ (u t) := by
+    funext z
+    exact indicator_of_mem ⟨ht, mem_univ z⟩ _
+  have hzero : ∀ x : E, iu (0,x) = 0 := by
+    intro x
+    rw [show iu (0,x) = u 0 x from congrFun (huS 0 ⟨le_rfl, hT.le⟩) x]
+    exact intervalIntegral.integral_same
+  have hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z => iu (t,z)) (idu (t,x)) x := by
+    intro t ht x
+    rw [huS t ht]
+    have hd0 : idu (t,x) = fderiv ℝ (u t) x := congrFun (hdS t ht) x
+    rw [hd0]
+    exact (hasFDerivAt_duhamel ht hf hfM x).differentiableAt.hasFDerivAt
+  have hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z => idu (t,z)) (iddu (t,x)) x := by
+    intro t ht x
+    rw [hdS t ht]
+    change HasFDerivAt (fderiv ℝ (u t)) ((cylinder T).indicator dd (t,x)) x
+    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
+    exact (((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
+      (m := 1) (by norm_num)).differentiable_one x).hasFDerivAt
+  have hut : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun s => iu (s,x)) (iv (t,x)) (Icc 0 T) t := by
+    intro t ht x
+    change HasDerivWithinAt _ ((cylinder T).indicator v (t,x)) _ _
+    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
+    exact ((htime t ht x).1).congr_of_mem (fun s hs => congrFun (huS s hs) x) ht
+  let G : ParabolicSolutionGraph.Graph («E» := E) α T :=
+    ParabolicSolutionGraph.ofDerivatives iu iv idu iddu
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ huB⟩ ⟨_, liftH _ huH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hvB⟩ ⟨_, liftH _ hvH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hdB⟩ ⟨_, liftH _ hdH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hddB⟩ ⟨_, liftH _ hddH⟩
+      hzero hdu hddu hut
+  refine ⟨G, ?_, ?_⟩
+  · intro p hp
+    exact indicator_of_mem hp _
+  · have huN : ‖G.u‖ ≤ (1+3*V)*N+2*W*N :=
+      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB _ huB) (liftH _ huH)
+    have hvN : ‖G.ut‖ ≤ (1+3*C)*N+(1+3*D)*N :=
+      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB _ hvB) (liftH _ hvH)
+    have hdN : ‖G.du‖ ≤ 2*J*N+2*Q*N :=
+      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB _ hdB) (liftH _ hdH)
+    have hddN : ‖G.ddu‖ ≤ A*N+B*N :=
+      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB _ hddB) (liftH _ hddH)
+    rw [ParabolicSolutionGraph.norm_eq]
+    change ‖G.u‖+‖G.ut‖+‖G.du‖+‖G.ddu‖ ≤ _ * N
+    nlinarith
+
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:592:27: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
Poincare/Global/DuhamelSolutionOperatorBound.lean:595:27: error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
Poincare/Global/DuhamelSolutionOperatorBound.lean:626:49: error: Application type mismatch: The argument
  liftB ?m.2178 ?m.2181
has type
  ∀ p ∈ cylinder T, ‖(cylinder T).indicator ?m.2178 p‖ ≤ ?m.2179
but is expected to have type
  ∀ p ∈ cylinder T, ‖iddu p‖ ≤ ?m.2175
in the application
  Exists.intro ?m.2175 (liftB ?m.2178 ?m.2181)
```

### 025-assembly

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 025-assembly.lean
@@ -592 +592 @@
-    exact indicator_of_mem ⟨ht, mem_univ z⟩ _
+    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
@@ -595 +595 @@
-    exact indicator_of_mem ⟨ht, mem_univ z⟩ _
+    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
@@ -623,4 +623,4 @@
-      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ huB⟩ ⟨_, liftH _ huH⟩
-      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hvB⟩ ⟨_, liftH _ hvH⟩
-      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hdB⟩ ⟨_, liftH _ hdH⟩
-      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB _ hddB⟩ ⟨_, liftH _ hddH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB (fun p => u p.1 p.2) huB⟩ ⟨_, liftH (fun p => u p.1 p.2) huH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB v hvB⟩ ⟨_, liftH v hvH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB d hdB⟩ ⟨_, liftH d hdH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB dd hddB⟩ ⟨_, liftH dd hddH⟩
@@ -632 +632 @@
-      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB _ huB) (liftH _ huH)
+      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB (fun p => u p.1 p.2) huB) (liftH (fun p => u p.1 p.2) huH)
@@ -634 +634 @@
-      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB _ hvB) (liftH _ hvH)
+      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB v hvB) (liftH v hvH)
@@ -636 +636 @@
-      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB _ hdB) (liftH _ hdH)
+      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB d hdB) (liftH d hdH)
@@ -638 +638 @@
-      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB _ hddB) (liftH _ hddH)
+      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB dd hddB) (liftH dd hddH)
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:630:10: error: typeclass instance problem is stuck
  Zero ?m.2222

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Zero` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
Poincare/Global/DuhamelSolutionOperatorBound.lean:641:4: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

### 026-component-prints

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/duhamel-solution-probes/026-component-prints.lean
```

Exit: `1`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ParabolicHolderSpace
#print Poincare.ParabolicSolutionGraph.norm_eq
#print Poincare.ParabolicSolutionGraph.norm_u_le
#print Poincare.ParabolicSolutionGraph.norm_ut_le
#print Poincare.ParabolicSolutionGraph.norm_du_le
#print Poincare.ParabolicSolutionGraph.norm_ddu_le
#print Poincare.ParabolicSolutionGraph.sup_u_le
#print Poincare.ParabolicSolutionGraph.holder_u_le
#print Poincare.ParabolicSolutionGraph.sup_ut_le
#print Poincare.ParabolicSolutionGraph.holder_ut_le
#print Poincare.ParabolicSolutionGraph.sup_du_le
#print Poincare.ParabolicSolutionGraph.holder_du_le
#print Poincare.ParabolicSolutionGraph.sup_ddu_le
#print Poincare.ParabolicSolutionGraph.holder_ddu_le
#print Poincare.ParabolicSolutionGraph.holder_tendsto
```

Actual compiler output:

```text
theorem Poincare.ParabolicSolutionGraph.norm_eq.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T),
  ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  id
    (Eq.mpr
      (id
        (congrFun'
          (congrArg Eq
            (Eq.trans (WithLp.prod_norm_eq_of_L1 ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))
              (congr
                (congrArg HAdd.hAdd
                  (WithLp.prod_norm_eq_of_L1 (WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))
                (WithLp.prod_norm_eq_of_L1 (WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))))
          (‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖)))
      (Eq.symm
        (add_assoc
          (‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖ +
            ‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)))
theorem Poincare.ParabolicSolutionGraph.norm_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.u‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.u‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this := norm_nonneg g.ut;
    have this_1 := norm_nonneg g.du;
    have this_2 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.ut‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.ut‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_3))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.du‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.du‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_3))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.ddu‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.ddu‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.sup_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.u) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.u p) (Poincare.ParabolicSolutionGraph.norm_u_le g)
theorem Poincare.ParabolicSolutionGraph.holder_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.u) p - ↑(WithLp.fst ↑g.u) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.u hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_u_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.ut) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.ut p) (Poincare.ParabolicSolutionGraph.norm_ut_le g)
theorem Poincare.ParabolicSolutionGraph.holder_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.ut) p - ↑(WithLp.fst ↑g.ut) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.ut hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_ut_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.du) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.du p) (Poincare.ParabolicSolutionGraph.norm_du_le g)
theorem Poincare.ParabolicSolutionGraph.holder_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.du) p - ↑(WithLp.fst ↑g.du) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.du hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_du_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.ddu) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.ddu p) (Poincare.ParabolicSolutionGraph.norm_ddu_le g)
theorem Poincare.ParabolicSolutionGraph.holder_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.ddu) p - ↑(WithLp.fst ↑g.ddu) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.ddu hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_ddu_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
/tmp/duhamel-solution-probes/026-component-prints.lean:16:7: error(lean.unknownIdentifier): Unknown constant `Poincare.ParabolicSolutionGraph.holder_tendsto`
```

### 027-assembly

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `1`.

```diff
--- previous-module-probe
+++ 027-assembly.lean
@@ -508,0 +509 @@
+set_option maxHeartbeats 800000 in
@@ -629,0 +631 @@
+    change (cylinder T).indicator (fun q : ℝ × E => u q.1 q.2) p = u p.1 p.2
```

Actual compiler output:

```text
Poincare/Global/DuhamelSolutionOperatorBound.lean:508:92: error: unexpected token 'set_option'; expected 'lemma'
Poincare/Global/DuhamelSolutionOperatorBound.lean:571:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/DuhamelSolutionOperatorBound.lean:573:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/DuhamelSolutionOperatorBound.lean:575:56: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

### 028-assembly

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

```diff
--- previous-module-probe
+++ 028-assembly.lean
@@ -507,0 +508 @@
+set_option maxHeartbeats 800000 in
@@ -509 +509,0 @@
-set_option maxHeartbeats 800000 in
@@ -571 +571,2 @@
-    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1 <;> ring
+    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1
+    ring
@@ -573 +574,2 @@
-    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1 <;> ring
+    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1
+    ring
@@ -575 +577,2 @@
-    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1 <;> ring
+    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1
+    ring
```

Actual compiler output:

```text
```

### 029-component-prints

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/duhamel-solution-probes/029-component-prints.lean
```

Exit: `0`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ParabolicHolderSpace
#print Poincare.ParabolicSolutionGraph.norm_eq
#print Poincare.ParabolicSolutionGraph.norm_u_le
#print Poincare.ParabolicSolutionGraph.norm_ut_le
#print Poincare.ParabolicSolutionGraph.norm_du_le
#print Poincare.ParabolicSolutionGraph.norm_ddu_le
#print Poincare.ParabolicSolutionGraph.sup_u_le
#print Poincare.ParabolicSolutionGraph.holder_u_le
#print Poincare.ParabolicSolutionGraph.sup_ut_le
#print Poincare.ParabolicSolutionGraph.holder_ut_le
#print Poincare.ParabolicSolutionGraph.sup_du_le
#print Poincare.ParabolicSolutionGraph.holder_du_le
#print Poincare.ParabolicSolutionGraph.sup_ddu_le
#print Poincare.ParabolicSolutionGraph.holder_ddu_le
```

Actual compiler output:

```text
theorem Poincare.ParabolicSolutionGraph.norm_eq.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T),
  ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  id
    (Eq.mpr
      (id
        (congrFun'
          (congrArg Eq
            (Eq.trans (WithLp.prod_norm_eq_of_L1 ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))
              (congr
                (congrArg HAdd.hAdd
                  (WithLp.prod_norm_eq_of_L1 (WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))
                (WithLp.prod_norm_eq_of_L1 (WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g))))))
          (‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖)))
      (Eq.symm
        (add_assoc
          (‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖ +
            ‖(WithLp.fst ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).fst‖
          ‖(WithLp.snd ↑(Poincare.ParabolicSolutionGraph.graphEquiv g)).snd‖)))
theorem Poincare.ParabolicSolutionGraph.norm_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.u‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.u‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this := norm_nonneg g.ut;
    have this_1 := norm_nonneg g.du;
    have this_2 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.ut‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.ut‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_3))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.du‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.du‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ddu‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_3))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.norm_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.ddu‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.ddu‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
theorem Poincare.ParabolicSolutionGraph.sup_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.u) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.u p) (Poincare.ParabolicSolutionGraph.norm_u_le g)
theorem Poincare.ParabolicSolutionGraph.holder_u_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.u) p - ↑(WithLp.fst ↑g.u) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.u hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_u_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.ut) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.ut p) (Poincare.ParabolicSolutionGraph.norm_ut_le g)
theorem Poincare.ParabolicSolutionGraph.holder_ut_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.ut) p - ↑(WithLp.fst ↑g.ut) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.ut hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_ut_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.du) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.du p) (Poincare.ParabolicSolutionGraph.norm_du_le g)
theorem Poincare.ParabolicSolutionGraph.holder_du_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.du) p - ↑(WithLp.fst ↑g.du) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.du hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_du_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
theorem Poincare.ParabolicSolutionGraph.sup_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × E),
  ‖↑(WithLp.fst ↑g.ddu) p‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g p =>
  LE.le.trans (Poincare.ParabolicHolder.norm_le g.ddu p) (Poincare.ParabolicSolutionGraph.norm_ddu_le g)
theorem Poincare.ParabolicSolutionGraph.holder_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T) {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑g.ddu) p - ↑(WithLp.fst ↑g.ddu) q‖ ≤ ‖g‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g {p q} hp hq =>
  LE.le.trans (Poincare.ParabolicHolder.holder_le g.ddu hp hq)
    (mul_le_mul_of_nonneg_right (Poincare.ParabolicSolutionGraph.norm_ddu_le g)
      (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α))
```

### 030-final-contract-dependencies

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/duhamel-solution-probes/030-final-contract-dependencies.lean
```

Exit: `0`.

Input: final module source followed by these commands.

```lean
#print axioms Poincare.DuhamelSolutionOperatorBound.abs_trace_le
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_bound
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_time_derivative_holder
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_bound
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_value_time_estimates
#print axioms Poincare.DuhamelSolutionOperatorBound.holder_of_bounded_lipschitz
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_spatial_holder
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_value_parabolic_holder
#print axioms Poincare.DuhamelSolutionOperatorBound.gradient_heatSolution_sub_bound
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_reversed
#print axioms Poincare.DuhamelSolutionOperatorBound.norm_integral_inverse_sqrt_le
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_time_holder_of_le
#print axioms Poincare.DuhamelSolutionOperatorBound.duhamel_gradient_parabolic_holder
#print axioms Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound
#print axioms Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound
namespace Poincare.DuhamelSolutionOperatorBound
local notation "E" => Poincare.ClosedSmoothModel 3
example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖ := exists_solution_graph_bound
end Poincare.DuhamelSolutionOperatorBound
```

Actual compiler output:

```text
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
```

### 031-final-module

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorBound.lean
```

Exit: `0`.

Input unchanged from the previous module probe.

Actual compiler output:

```text
```

## Source-name inventory

The following `rg` output records the new declarations and the relevant upstream source spellings.

```sh
rg -n '\b(Icc_subset_Icc|abs_add_le|abs_le|abs_nonneg|abs_of_nonneg|abs_of_nonpos|add_le_add|add_mul|add_sub_add_comm|add_sub_right_comm|ae_restrict_mem|by_cases|comp_continuous|comp_sub_left|congr_of_mem|const_mul|contDiff_two_duhamel|continuous_const|continuous_id|convex_Icc|convex_univ|differentiable_one|div_eq_mul_inv|div_one|duhamel_hessian_bound|duhamel_hessian_parabolic_holder|duhamel_solves_heat_equation|fderiv_right|filter_upwards|fun_prop|hasFDerivAt_duhamel|hasHolderBound_duhamel_hessian|heatSolution_hasFDerivAt|indicator_of_mem|indicator_of_notMem|integrable_smul_fderiv_heatKernel_sub|integral_add_adjacent_intervals|integral_comp_sub_left|integral_const_mul|integral_hessian_majorant|integral_nonneg|integral_of_le|integral_rpow|integral_same|integral_sub|intervalIntegrable_gradient_heatSolution_time|intervalIntegrable_gradient_majorant|intervalIntegrable_iff_integrableOn_Ioo_of_le|intervalIntegrable_rpow|laplacian_eq_hessian_trace|le_add_of_nonneg_left|le_add_of_nonneg_right|le_mul_of_one_le_right|le_of_not_ge|le_opNorm|le_rfl|le_total|lt_of_le_of_lt|measurableSet_Ioo|mem_univ|mono_set|mul_assoc|mul_comm|mul_le_mul_of_nonneg_left|mul_le_mul_of_nonneg_right|mul_le_of_le_one_left|mul_le_of_le_one_right|mul_left_comm|mul_nonneg|mul_one|neg_sub|norm_add_le|norm_eq|norm_eq_abs|norm_eq_one|norm_gradient_heatSolution_le|norm_image_sub_le_of_norm_fderiv_le|norm_image_sub_le_of_norm_hasDerivWithin_le|norm_integral_le_of_norm_le|norm_le|norm_le_of_bounds|norm_nonneg|norm_num|norm_sub_le|norm_sub_le_norm_sub_add_norm_sub|norm_sub_rev|norm_sum_le|of_forall|one_le_rpow|parabolicDist_nonneg|restrict_Ioo_eq_restrict_Ioc|rpow_le_one|rpow_le_rpow|rpow_le_rpow_of_exponent_ge|rpow_mul|rpow_nonneg|rpow_one|self_mem_nhdsWithin|set_option|sq_sqrt|sqrt_eq_rpow|sqrt_le_one|sqrt_nonneg|squeeze_zero|sub_apply|sub_nonneg|sub_nonpos|sub_pos|sub_self|sub_smul|sub_sub_cancel|sub_sub_sub_cancel_right|sub_zero|sum_le_sum|sum_sub_distrib|tendsto_iff_norm_sub_tendsto_zero|uIcc_of_le|zero_lt_one|zero_rpow)\b' Poincare/Global/HeatDuhamelHessianDifferentiation.lean Poincare/Global/HeatDuhamelHeatEquation.lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean Poincare/Global/ParabolicHolderSpace.lean Poincare/Global/ParabolicSolutionGraph.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean .lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean
```

Exit: `0`.

```text
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:49:@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:53:@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:75:@[simp] lemma sqrt_le_one : sqrt x ≤ 1 ↔ x ≤ 1 := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:82:  rw [sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt, sq_sqrt]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:94:@[continuity, fun_prop]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:125:@[continuity, fun_prop]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:126:theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:144:@[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:154:  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:160:    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:174:    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:175:    _ ↔ x = 1 := by rw [eq_comm, mul_one]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:178:theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:187:  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:229:  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:251:  · simpa only [abs_le] using abs_le_sqrt
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:252:  · rw [← abs_le, ← sq_abs]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:253:    exact (le_sqrt (abs_nonneg x) h).mp
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:266:theorem sqrt_eq_zero (h : 0 ≤ x) : √x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:275:/-- Variant of `sq_sqrt` without a non-negativity assumption on `x`. -/
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:276:theorem sq_sqrt' : √x ^ 2 = max x 0 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:277:  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:280:grind_pattern sq_sqrt' => √x
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:287:  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:292:  obtain hy | hy := le_total y 0
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:298:  rw [← sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:300:@[simp] lemma sqrt_le_one : √x ≤ 1 ↔ x ≤ 1 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:335:    | _ => pure (.nonnegative q(Real.sqrt_nonneg $a))
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:357:  rw [mul_comm, sqrt_mul hy, mul_comm]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:385:  rw [← abs_lt, ← sq_abs, lt_sqrt (abs_nonneg _)]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:394:  have hy := x.sqrt_nonneg.trans_lt h
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:422:  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:429:    _ ≤ 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right <| sq_nonneg _
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:453:@[fun_prop]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:457:@[fun_prop]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:461:@[continuity, fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:94:    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:117:    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:140:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:159:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:204:  (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:227:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:261:  exact .symm <| (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:277:    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:286:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:291:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:300:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:304:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:310:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:315:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:331:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:337:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:343:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:348:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:357:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:361:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:367:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:373:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:378:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:384:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:471:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:476:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:482:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:488:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:494:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:499:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:504:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:509:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:515:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:520:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:525:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:530:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:568:  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:593:    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:601:  · refine inter_mem ?_ self_mem_nhdsWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:633:    filter_upwards [hv, ht]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:640:    filter_upwards [hv, ht]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:645:  | (m : ℕ) => exact this _ le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:653:  hf.fderivWithin'' hg ht hmn <| mem_of_superset self_mem_nhdsWithin <| image_subset_iff.mpr hst
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:664:  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:704:    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:714:    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:717:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:724:theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:743:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:750:theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:752:  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:758:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:769:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:775:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:818:  hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop]) |>.continuousAt
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:5:set_option autoImplicit false
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:17:theorem duhamel_hessian_parabolic_holder :
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:43:    Real.rpow_le_rpow (norm_nonneg _)
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:44:      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:48:        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:52:        Real.rpow_le_rpow (Real.sqrt_nonneg _)
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:53:          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:58:      simpa only [sub_add_sub_cancel] using norm_add_le
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:62:      add_le_add hs ht
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:65:      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:66:        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:70:theorem hasHolderBound_duhamel_hessian :
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:82:  obtain ⟨C, hC, hbound⟩ := duhamel_hessian_parabolic_holder α hα hα1
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:130:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:166:  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:180:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:203:  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H m hm => H m hm _ le_rfl⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:255:  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:261:theorem ContDiffWithinAt.congr_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:290:  h.mono_of_mem_nhdsWithin <| Filter.mem_of_superset self_mem_nhdsWithin hst
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:300:  apply h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:326:  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:369:    · convert @self_mem_nhdsWithin _ _ x u
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:399:        norm_num [eq_iff_true_of_subsingleton]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:461:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:469:  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:476:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:491:    simp only [insert_eq_of_mem, hy, self_mem_nhdsWithin]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:515:  · rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, h'u⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:523:  rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, _, hd⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:537:  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:551:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:572:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:593:    rcases Hf'.contDiffOn le_rfl (by simp [hn]) with ⟨v, vu, v'u, hv⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:613:  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:621:    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:642:    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:649:      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:664:    rcases (h x hx).of_le hm _ le_rfl with ⟨u, hu, p, Hp⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:673:      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:674:    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:679:  (((h.ftaylorSeriesWithin ht).mono st).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:703:  exact self_mem_nhdsWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:728:  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:749:  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:769:  ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:823:    exact ⟨s, self_mem_nhdsWithin, (by simp), fderivWithin 𝕜 f s,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:828:    exact ⟨s, self_mem_nhdsWithin, h', fderivWithin 𝕜 f s,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:863:  | (n : ℕ) => exact A n le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:873:  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:926:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:936:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:940:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:952:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:959:  h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:964:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:999:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1013:  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1034:  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1057:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1069:@[simp, fun_prop] theorem contDiffOn_empty : ContDiffOn 𝕜 n f ∅ := fun _x hx ↦ hx.elim
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1097:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1101:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1111:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1130:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1140:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1144:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1149:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1153:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1154:theorem ContDiff.differentiable_one (h : ContDiff 𝕜 1 f) : Differentiable 𝕜 f :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1165:  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ, Set.mem_univ, forall_true_left,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1226:  (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1228:@[fun_prop]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1231:  (contDiff_iff_continuous_differentiable.mp hf).1 m le_rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:104:  intervalIntegrable_congr_ae <| (ae_restrict_mem measurableSet_uIoc).mono h
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:140:theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NoAtoms μ]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:156:  ⟨hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:157:    hf.mono_set (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:201:  ⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:202:    (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:253:theorem mono_set (hf : IntervalIntegrable f μ a b) (h : [[c, d]] ⊆ [[a, b]]) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:255:  hf.mono h le_rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:261:theorem mono_set' (hf : IntervalIntegrable f μ a b) (hsub : Ι c d ⊆ Ι a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:263:  hf.mono_set_ae <| Eventually.of_forall hsub
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:299:  by_cases hab : a ≤ b
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:333:  by_cases h₁ : f.support.Finite
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:352:theorem const_mul {f : ℝ → A} (hf : IntervalIntegrable f μ a b) (c : A) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:382:  simpa only [div_eq_mul_inv] using mul_const h c⁻¹
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:415:  simpa only [mul_comm] using comp_mul_left hf h h'
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:421:    rw [min_sub_sub_right, sub_add, sub_self, sub_zero]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:424:  · apply IntervalIntegrable.symm (this hf.symm ?_ ?_ (le_of_not_ge hab))
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:473:theorem comp_sub_left {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (c : ℝ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:476:  simpa only [neg_sub, ← sub_eq_add_neg] using (iff_comp_neg (by simp)).mp (hf.comp_add_left c h)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:482:  ⟨fun h ↦ by simpa using h.comp_sub_left c, (.comp_sub_left · c h)⟩
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:499:  ContinuousOn.intervalIntegrable ((uIcc_of_le h).symm ▸ hu)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:520:  exact (hu.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:667:theorem integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:671:theorem integral_same : ∫ x in a..a, f x ∂μ = 0 :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:672:  sub_self _
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:675:  simp only [intervalIntegral, neg_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:678:  simp only [integral_symm b, integral_of_le h]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:683:  · simp only [integral_of_le h, uIoc_of_le h, one_smul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:718:  cases le_total a b <;> simp [*, integral_symm a b]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:722:  rw [← norm_integral_min_max, integral_of_le min_le_max, uIoc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:734:  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:739:  norm_integral_le_integral_norm_uIoc.trans_eq <| by rw [uIoc_of_le h, integral_of_le h]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:744:  exact (norm_integral_le_of_norm_le hbound.def' h).trans (le_abs_self _)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:746:theorem norm_integral_le_of_norm_le {g : ℝ → ℝ} (hab : a ≤ b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:749:  simp only [integral_of_le hab, ← ae_restrict_iff' measurableSet_Ioc] at *
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:750:  exact MeasureTheory.norm_integral_le_of_norm_le hbound.1 h
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:761:  norm_integral_le_of_norm_le_const_ae <| Eventually.of_forall h
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:781:theorem integral_sub (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:807:theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:814:  simpa only [mul_comm r] using integral_const_mul r f
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:819:  simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:823:  simp only [measureReal_def, intervalIntegral, setIntegral_const, sub_smul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:827:  simp only [integral_const', Real.volume_Ioc, ENNReal.toReal_ofReal', ← neg_sub b,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:895:    ENNReal.toReal_ofReal (abs_nonneg c)]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:904:  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_right]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:909:  simpa only [mul_comm c] using integral_comp_mul_right f hc
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:914:  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_left]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:924:  by_cases hc : c = 0 <;> simp [hc, integral_comp_div]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:948:  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_add]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:958:  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_mul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:968:  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_add]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:978:  by_cases hc : c = 0 <;> simp [hc, integral_comp_add_div]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:988:  by_cases hc : c = 0 <;> simp [hc, integral_comp_mul_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1000:  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_mul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1010:  by_cases hc : c = 0 <;> simp [hc, integral_comp_div_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1020:  by_cases hc : c = 0 <;> simp [hc, integral_comp_sub_div]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1027:theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1032:  simpa only [zero_sub] using integral_comp_sub_left f 0
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1052:  rcases le_total a b with hab | hab <;>
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1053:    simpa [hab, integral_of_le, integral_of_ge] using
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1068:theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1080:    rw [Finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1082:      exact (Ico_subset_Ico le_rfl (Nat.le_succ _)) hk
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1097:  sub_eq_of_eq_add' <| Eq.symm <| integral_add_adjacent_intervals hac (hac.symm.trans hab)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1103:  rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1104:    integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1123:  · rw [integral_symm, ← this hb ha (le_of_not_ge hab), neg_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1124:  rw [sub_eq_iff_eq_add', integral_of_le hab, ← setIntegral_union (Iic_disjoint_Ioc le_rfl),
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1126:  exacts [measurableSet_Ioc, ha, hb.mono_set fun _ => And.right]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1133:  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1134:  rw [integral_of_le hab, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1135:    (ha.mono_set Ioc_subset_Ioi_self) hb, Ioc_union_Ioi_eq_Ioi hab]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1142:  by_cases! h : a ≤ b
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1145:  · exact hb.mono_set <| Ioi_subset_Ioi h.le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1149:  sub_eq_of_eq_add (integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hab))).symm
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1154:  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1159:  have ha : IntegrableOn f (Iio a) μ := hf.mono_set (Iio_subset_Iio hab)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1160:  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Iio_self
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1168:  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1169:  rw [integral_Iio_sub_Iio hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1173:  have ha : IntegrableOn f (Ici b) μ := hf.mono_set (Ici_subset_Ici.2 hab)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1174:  have h : IntegrableOn f (Ico a b) μ := hf.mono_set Ico_subset_Ici_self
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1182:  · rw [integral_symm, ← this hg hf hab.le, neg_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1183:  rw [integral_Ici_sub_Ici hf hab, integral_of_le hab, integral_Ico_eq_integral_Ioc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1200:  simp only [sub_smul, ← setIntegral_const]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1205:  rcases le_total a b with hab | hab
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1206:  · rw [integral_of_le hab, ← integral_indicator measurableSet_Ioc, indicator_eq_self.2 h]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1239:  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2), integral_indicator,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1253:  rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1258:  rcases le_total a b with hab | hab <;>
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1271:    simp only [hab, true_and, integral_of_le hab.le,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1294:    rw [ae_restrict_iff' measurableSet_Ioo]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1295:    filter_upwards with x hx using (hpos x hx).le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1314:  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1317:    exact fun x hx => (sub_pos.2 hx.out).ne'
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1318:  exacts [hle.mono fun x => sub_nonneg.2, hgi.1.sub hfi.1]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1329:      using (ae_restrict_mem measurableSet_Ioc).mono hle
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1334:      Eventually.of_forall hle) hlt
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1341:  simpa only [integral_of_le hab] using setIntegral_nonneg_of_ae_restrict H
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1347:  integral_nonneg_of_ae hab <| Eventually.of_forall hf
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1349:theorem integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1354:  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1367:  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1372:  have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f := ae_mono (Measure.restrict_mono h le_rfl) hf
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1375:    _ = ∫ x in Ι a b, f x ∂μ := abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae hf')
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1386:  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1389:  simpa only [integral_of_le hab] using setIntegral_mono_ae hf.1 hg.1 h
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1394:  simpa only [integral_of_le hab] using setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc H
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1398:  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1400:  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1401:  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1402:  · exact measurableSet_Ioo
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1418:  simp_rw [integral_of_le (le_add_of_nonneg_right zero_le_one)]
Poincare/Global/ParabolicSolutionGraph.lean:9:set_option synthInstance.maxHeartbeats 200000
Poincare/Global/ParabolicSolutionGraph.lean:10:set_option maxHeartbeats 800000
Poincare/Global/ParabolicSolutionGraph.lean:83:theorem norm_eq (g : Graph (E := E) α T) :
Poincare/Global/ParabolicSolutionGraph.lean:90:  rw [norm_eq]
Poincare/Global/ParabolicSolutionGraph.lean:91:  have := norm_nonneg g.u
Poincare/Global/ParabolicSolutionGraph.lean:92:  have := norm_nonneg g.ut
Poincare/Global/ParabolicSolutionGraph.lean:93:  have := norm_nonneg g.du
Poincare/Global/ParabolicSolutionGraph.lean:94:  have := norm_nonneg g.ddu
Poincare/Global/ParabolicSolutionGraph.lean:98:  rw [norm_eq]
Poincare/Global/ParabolicSolutionGraph.lean:99:  have := norm_nonneg g.u
Poincare/Global/ParabolicSolutionGraph.lean:100:  have := norm_nonneg g.ut
Poincare/Global/ParabolicSolutionGraph.lean:101:  have := norm_nonneg g.du
Poincare/Global/ParabolicSolutionGraph.lean:102:  have := norm_nonneg g.ddu
Poincare/Global/ParabolicSolutionGraph.lean:106:  rw [norm_eq]
Poincare/Global/ParabolicSolutionGraph.lean:107:  have := norm_nonneg g.u
Poincare/Global/ParabolicSolutionGraph.lean:108:  have := norm_nonneg g.ut
Poincare/Global/ParabolicSolutionGraph.lean:109:  have := norm_nonneg g.du
Poincare/Global/ParabolicSolutionGraph.lean:110:  have := norm_nonneg g.ddu
Poincare/Global/ParabolicSolutionGraph.lean:114:  rw [norm_eq]
Poincare/Global/ParabolicSolutionGraph.lean:115:  have := norm_nonneg g.u
Poincare/Global/ParabolicSolutionGraph.lean:116:  have := norm_nonneg g.ut
Poincare/Global/ParabolicSolutionGraph.lean:117:  have := norm_nonneg g.du
Poincare/Global/ParabolicSolutionGraph.lean:118:  have := norm_nonneg g.ddu
Poincare/Global/ParabolicSolutionGraph.lean:123:  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)
Poincare/Global/ParabolicSolutionGraph.lean:129:    (mul_le_mul_of_nonneg_right (norm_u_le g)
Poincare/Global/ParabolicSolutionGraph.lean:130:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicSolutionGraph.lean:134:  (ParabolicHolder.norm_le g.ut p).trans (norm_ut_le g)
Poincare/Global/ParabolicSolutionGraph.lean:140:    (mul_le_mul_of_nonneg_right (norm_ut_le g)
Poincare/Global/ParabolicSolutionGraph.lean:141:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicSolutionGraph.lean:145:  (ParabolicHolder.norm_le g.du p).trans (norm_du_le g)
Poincare/Global/ParabolicSolutionGraph.lean:151:    (mul_le_mul_of_nonneg_right (norm_du_le g)
Poincare/Global/ParabolicSolutionGraph.lean:152:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicSolutionGraph.lean:156:  (ParabolicHolder.norm_le g.ddu p).trans (norm_ddu_le g)
Poincare/Global/ParabolicSolutionGraph.lean:162:    (mul_le_mul_of_nonneg_right (norm_ddu_le g)
Poincare/Global/ParabolicSolutionGraph.lean:163:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicSolutionGraph.lean:167:  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
Poincare/Global/ParabolicSolutionGraph.lean:169:    (fun s _ => ParabolicHolder.norm_le g.ut (s, x)) (convex_Icc (0 : ℝ) T)
Poincare/Global/ParabolicSolutionGraph.lean:170:    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
Poincare/Global/ParabolicSolutionGraph.lean:171:  simpa [g.zero_trace x, Real.norm_of_nonneg ht.1, mul_comm] using h
Poincare/Global/ParabolicSolutionGraph.lean:215:  filter_upwards [(Metric.tendsto_nhds.1 h) ε hε] with n hn p
Poincare/Global/ParabolicSolutionGraph.lean:216:  have hb := Poincare.ParabolicHolder.norm_le (w - v n) p
Poincare/Global/ParabolicSolutionGraph.lean:219:  exact hb.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn)
Poincare/Global/ParabolicSolutionGraph.lean:233:    simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn y hy).le
Poincare/Global/ParabolicSolutionGraph.lean:238:    filter_upwards [eventually_ge_atTop N] with n hn
Poincare/Global/ParabolicSolutionGraph.lean:239:    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
Poincare/Global/ParabolicSolutionGraph.lean:243:      ‖d n z - d N z‖ ≤ ‖d n z - e z‖ + ‖e z - d N z‖ := norm_sub_le_norm_sub_add_norm_sub ..
Poincare/Global/ParabolicSolutionGraph.lean:244:      _ ≤ ε / 2 := by rw [norm_sub_rev (e z)]; linarith [hnear n hn z hz, hnear N le_rfl z hz]
Poincare/Global/ParabolicSolutionGraph.lean:245:  filter_upwards [(hf N x hx).isLittleO.bound hε4, self_mem_nhdsWithin] with y hy hys
Poincare/Global/ParabolicSolutionGraph.lean:247:    rw [norm_mul, mul_comm]
Poincare/Global/ParabolicSolutionGraph.lean:248:    exact mul_le_mul_of_nonneg_right (hnear N le_rfl x hx) (norm_nonneg _)
Poincare/Global/ParabolicSolutionGraph.lean:258:      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
Poincare/Global/ParabolicSolutionGraph.lean:293:    exact closed_time_derivative (convex_Icc 0 T)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:106:    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:145:    · rwa [sub_self, mul_zero, add_zero]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:148:      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:150:      rw [mul_one]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:154:  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 := by fun_prop
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:205:    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:321:  simp only [g, B]; rw [sub_self, norm_zero, sub_self, mul_zero]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:349:  simpa only [sub_zero, mul_one] using
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:357:  simpa only [sub_zero, mul_one] using
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:382:    simpa only [sub_self] using (derivf y hy).sub (derivg y hy)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:500:theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:522:  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hf x) (fun x _ ↦ bound x) convex_univ
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:550:theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:561:    simp only [hf' x hx, norm_zero, le_rfl]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:571:  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:580:  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:609:    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.2)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:629:    hf' hx, sub_self, Pi.zero_apply]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:647:  suffices Set.univ.EqOn f g from funext fun x => this <| mem_univ x
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:648:  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:649:    uniqueDiffOn_univ (fun x _ => by simpa using hf' _) (mem_univ _) hfgx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:656:  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:660:    filter_upwards [h1, hs.eventually_nhdsWithin_segment hx₀s (hf' hc)] with x hxs h
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:664:  filter_upwards [this] with x ⟨h_segment, h⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:692:theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:712:  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:728:  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:744:    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x
Poincare/Global/ParabolicHolderSpace.lean:32:theorem parabolicDist_nonneg (p q : ℝ × E) : 0 ≤ parabolicDist p q := by
Poincare/Global/ParabolicHolderSpace.lean:33:  exact add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
Poincare/Global/ParabolicHolderSpace.lean:37:  simp only [parabolicDist, norm_sub_rev, abs_sub_comm]
Poincare/Global/ParabolicHolderSpace.lean:40:  by_cases hx : p.2 = q.2
Poincare/Global/ParabolicHolderSpace.lean:42:    exact add_pos_of_nonneg_of_pos (norm_nonneg _)
Poincare/Global/ParabolicHolderSpace.lean:45:      (Real.sqrt_nonneg _)
Poincare/Global/ParabolicHolderSpace.lean:123:  exact mul_comm _ _
Poincare/Global/ParabolicHolderSpace.lean:129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
Poincare/Global/ParabolicHolderSpace.lean:132:    (le_add_of_nonneg_right (norm_nonneg _))
Poincare/Global/ParabolicHolderSpace.lean:137:  by_cases h : p = q
Poincare/Global/ParabolicHolderSpace.lean:139:    simp only [sub_self, norm_zero]
Poincare/Global/ParabolicHolderSpace.lean:140:    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
Poincare/Global/ParabolicHolderSpace.lean:146:      exact le_add_of_nonneg_left (norm_nonneg _)
Poincare/Global/ParabolicHolderSpace.lean:151:    ∃ M : ℝ, ∀ p ∈ cylinder T, ‖f p‖ ≤ M := ⟨‖f‖, fun p _ => norm_le f p⟩
Poincare/Global/ParabolicHolderSpace.lean:161:  exact mul_comm _ _
Poincare/Global/ParabolicHolderSpace.lean:173:    by_cases hp : p ∈ cylinder T
Poincare/Global/ParabolicHolderSpace.lean:211:@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
Poincare/Global/ParabolicHolderSpace.lean:222:    by_cases hp : p ∈ cylinder T
Poincare/Global/ParabolicHolderSpace.lean:240:  · exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:250:    · exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:264:  · exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:272:    · exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:278:    by_cases hp : p ∈ cylinder T
Poincare/Global/ParabolicHolderSpace.lean:286:theorem norm_eq (f : Y (E := E) α T F) :
Poincare/Global/ParabolicHolderSpace.lean:290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
Poincare/Global/ParabolicHolderSpace.lean:294:  apply add_le_add
Poincare/Global/ParabolicHolderSpace.lean:297:    by_cases hp : p ∈ cylinder T
Poincare/Global/ParabolicHolderSpace.lean:319:        isClosed_eq (ev₁ p) (continuous_const : Continuous (fun _ : Ambient T E F => (0 : F))))
Poincare/Global/ParabolicHolderSpace.lean:329:  exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:334:  exact norm_nonneg _
Poincare/Global/ParabolicHolderSpace.lean:345:  by_cases h : p = q
Poincare/Global/ParabolicHolderSpace.lean:347:    simp only [sub_self, norm_zero]
Poincare/Global/ParabolicHolderSpace.lean:348:    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
Poincare/Global/ParabolicHolderSpace.lean:363:    _ ≤ ‖f p * (g p - g q)‖ + ‖(f p - f q) * g q‖ := norm_add_le _ _
Poincare/Global/ParabolicHolderSpace.lean:369:      apply add_le_add
Poincare/Global/ParabolicHolderSpace.lean:371:          (norm_nonneg _) (supNorm_nonneg f)
Poincare/Global/ParabolicHolderSpace.lean:373:          (norm_nonneg _) (mul_nonneg (holderSeminorm_nonneg f)
Poincare/Global/ParabolicHolderSpace.lean:374:            (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicHolderSpace.lean:382:      exact mul_le_mul (le_supNorm f p) (le_supNorm g p) (norm_nonneg _) (supNorm_nonneg f)⟩
Poincare/Global/ParabolicHolderSpace.lean:394:    apply norm_le_of_bounds (f * g)
Poincare/Global/ParabolicHolderSpace.lean:395:    · exact mul_nonneg (supNorm_nonneg f) (supNorm_nonneg g)
Poincare/Global/ParabolicHolderSpace.lean:397:        (mul_nonneg (supNorm_nonneg f) (holderSeminorm_nonneg g))
Poincare/Global/ParabolicHolderSpace.lean:398:        (mul_nonneg (holderSeminorm_nonneg f) (supNorm_nonneg g))
Poincare/Global/ParabolicHolderSpace.lean:401:      exact mul_le_mul (le_supNorm f p) (le_supNorm g p) (norm_nonneg _) (supNorm_nonneg f)
Poincare/Global/ParabolicHolderSpace.lean:403:  rw [norm_eq f, norm_eq g]
Poincare/Global/ParabolicHolderSpace.lean:404:  nlinarith [mul_nonneg (holderSeminorm_nonneg f) (holderSeminorm_nonneg g)]
Poincare/Global/ParabolicHolderSpace.lean:422:    ⟨‖f‖, fun p hp => by dsimp only; rw [if_pos hp]; exact norm_le f p⟩
Poincare/Global/ParabolicHolderSpace.lean:435:  rw [norm_eq f]
Poincare/Global/ParabolicHolderSpace.lean:436:  apply norm_le_of_bounds _ (supNorm_nonneg f) (holderSeminorm_nonneg f)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:3:set_option autoImplicit false
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:43:  have h := (integrable_smul_fderiv_heatKernel_sub («E» := E) ht
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:45:    (C := 1) (by intro y; simp) (0 : E)).comp_sub_left (0 : E)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:46:  simpa only [one_smul, sub_sub_cancel] using h
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:65:      rw [integral_const_mul]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:72:  rw [Real.sq_sqrt ht.le] at h
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:73:  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:81:  rw [(heatSolution_hasFDerivAt ht hf hM x).fderiv]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:84:  simpa only [sub_sub_cancel] using hc.symm
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:87:theorem norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:95:      apply norm_integral_le_of_norm_le ((integrable_gradient ht).norm.const_mul M)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:96:      exact Filter.Eventually.of_forall fun y =>
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:98:          (mul_le_mul_of_nonneg_right (hM (x - y)) (norm_nonneg _))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:100:      rw [integral_const_mul, gradient_integral ht, mul_assoc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:108:    (contDiff_heatKernel_spatial («E» := E) 1).fderiv_right (m := 0) (by norm_num)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:123:  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:157:    Real.continuous_sqrt.comp (continuous_const.sub hs)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:159:    Real.sqrt_pos.2 (sub_pos.mpr p.1.property.2)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:161:    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:162:      (m := 0) (by norm_num)).continuous
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:167:      exact ((hf.comp_continuous
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:168:        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:169:        (fun y => ⟨hmem p.1, mem_univ _⟩)).smul hunit).aestronglyMeasurable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:171:      exact Filter.Eventually.of_forall fun y =>
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:173:          (mul_le_mul_of_nonneg_right (hM p.1 (hmem p.1) _ ) (norm_nonneg _))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:174:    · exact (integrable_gradient zero_lt_one).norm.const_mul M
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:175:    · exact Filter.Eventually.of_forall fun y =>
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:176:        (hf.comp_continuous (hs.prodMk (continuous_snd.sub (ha.smul continuous_const)))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:177:          (fun p => ⟨hmem p.1, mem_univ _⟩)).smul continuous_const
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:181:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:182:      (fun y => ⟨hmem p.1, mem_univ y⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:183:  rw [gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.2)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:184:    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM p.1 (hmem p.1))]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:187:  rw [Real.sq_sqrt (sub_pos.mpr p.1.property.2).le] at h
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:191:theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:193:  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:194:  norm_num
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:197:theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:203:    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:205:  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:206:    (intervalIntegrable_gradient_majorant t A)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:207:  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:208:    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:209:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:210:  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:213:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:214:      (fun y => ⟨hmem, mem_univ y⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:215:  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:216:    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:225:  · apply Continuous.rpow_const (by fun_prop)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:228:    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht p).ne'
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:230:    apply Continuous.div (by fun_prop) (by fun_prop)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:232:    exact mul_ne_zero (by norm_num) (ht p).ne'
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:245:    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:246:      (fun p => ⟨hmem p.1, mem_univ _⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:249:      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:252:  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:254:  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:255:    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:256:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:258:    (Filter.Eventually.of_forall fun s => ?_)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:259:  have hpos := sub_pos.mpr s.property.2
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:265:      apply norm_integral_le_of_norm_le ((heatKernel_integrable («E» := E) hpos).const_mul M)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:266:      refine Filter.Eventually.of_forall fun y => ?_
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:267:      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hpos y), mul_comm]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:268:      exact mul_le_mul_of_nonneg_right (hM s (hmem s) _) (heatKernel_nonneg hpos y)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:269:    _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:272:theorem hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Icc 0 T)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:282:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:283:      (fun y => ⟨hmem s hs, mem_univ y⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:287:  · exact Filter.Eventually.of_forall fun z => by
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:292:      (intervalIntegrable_gradient_heatSolution_time ht hf hM x).aestronglyMeasurable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:293:  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:294:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:295:    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:296:      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:297:  · exact intervalIntegrable_gradient_majorant t A
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:298:  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:299:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:300:    exact (heatSolution_hasFDerivAt (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:301:      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z).differentiableAt.hasFDerivAt
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:319:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:320:      (fun y => ⟨hmem s hs, mem_univ y⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:324:  · exact Filter.Eventually.of_forall fun z => by
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:326:        (intervalIntegrable_gradient_heatSolution_time ht hf hM z).aestronglyMeasurable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:327:  · exact intervalIntegrable_gradient_heatSolution_time ht hf hM x
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:328:  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:331:  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:332:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:334:      (sub_pos.mpr hs.2) (hK s (hmem s hs)) z
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:336:  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:337:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:339:      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:341:      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:342:    have hd := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:343:      (by norm_num) z).hasFDerivAt
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:345:      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:361:  simp_rw [intervalIntegral.integral_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:366:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:368:      (sub_pos.mpr hs.2) (hK s (hmem s hs)) x
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:369:  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:371:  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:373:      hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:374:        (fun y => ⟨hmem s hs, mem_univ y⟩)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:376:      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:378:      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:379:    have hc := ((htwo.fderiv_right (m := 1) (by norm_num)).fderiv_right
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:380:      (m := 0) (by norm_num)).continuous
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:382:      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs x)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:394:  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:399:theorem contDiff_two_duhamel {α T t M K : ℝ}
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:406:  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:410:    ⟨fun z => (hasFDerivAt_duhamel ht hf hM z).differentiableAt, by norm_num, ?_⟩
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:418:theorem duhamel_hessian_bound :
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:436:  refine ⟨max 1 (J * (2 / α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:441:    exact intervalIntegral.integral_same
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:443:    refine ⟨contDiff_two_duhamel hα hα1 ht hf hM hK,
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:454:        mul_le_mul_of_nonneg_right
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:455:          (mul_le_mul_of_nonneg_right (le_max_right _ _) hK0)
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:456:          (Real.rpow_nonneg ht.1 _)
Poincare/Global/HeatDuhamelHeatEquation.lean:3:set_option autoImplicit false
Poincare/Global/HeatDuhamelHeatEquation.lean:21:theorem laplacian_eq_hessian_trace (g : E → ℝ) (x : E) :
Poincare/Global/HeatDuhamelHeatEquation.lean:37:  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
Poincare/Global/HeatDuhamelHeatEquation.lean:39:  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
Poincare/Global/HeatDuhamelHeatEquation.lean:42:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHeatEquation.lean:43:      (fun y => ⟨hsT, mem_univ y⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:44:  exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
Poincare/Global/HeatDuhamelHeatEquation.lean:45:    hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
Poincare/Global/HeatDuhamelHeatEquation.lean:57:  simp_rw [laplacian_eq_hessian_trace]
Poincare/Global/HeatDuhamelHeatEquation.lean:82:    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHeatEquation.lean:83:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
Poincare/Global/HeatDuhamelHeatEquation.lean:86:      hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHeatEquation.lean:87:        (fun y => ⟨hsT, mem_univ y⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:88:    exact (hessian_heatSolution_eq_cancelled_integral (sub_pos.mpr hs.2)
Poincare/Global/HeatDuhamelHeatEquation.lean:89:      hc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hsT) x).symm
Poincare/Global/HeatDuhamelHeatEquation.lean:93:  simp_rw [laplacian_eq_hessian_trace]
Poincare/Global/HeatDuhamelHeatEquation.lean:109:    hf.comp_continuous (continuous_const.prodMk continuous_id)
Poincare/Global/HeatDuhamelHeatEquation.lean:110:      (fun y => ⟨hs, mem_univ y⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:112:    simpa only [Real.norm_eq_abs] using hM s hs
Poincare/Global/HeatDuhamelHeatEquation.lean:113:  have hd := heatKernel_time_deriv_integral_hasDerivAt (sub_pos.mpr hst)
Poincare/Global/HeatDuhamelHeatEquation.lean:120:    (sub_pos.mpr hst) hc.aestronglyMeasurable hb x] at hp
Poincare/Global/HeatDuhamelHeatEquation.lean:121:  simpa only [mul_one] using hp.comp t ((hasDerivAt_id t).sub_const s)
Poincare/Global/HeatDuhamelHeatEquation.lean:130:    smul_eq_mul, mul_assoc, integral_const_mul] at hc
Poincare/Global/HeatDuhamelHeatEquation.lean:142:      hf.comp_continuous
Poincare/Global/HeatDuhamelHeatEquation.lean:143:        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
Poincare/Global/HeatDuhamelHeatEquation.lean:144:        (fun y => ⟨hp.2, mem_univ _⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:147:    exact Filter.Eventually.of_forall fun y => by
Poincare/Global/HeatDuhamelHeatEquation.lean:148:      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg zero_lt_one y), Real.norm_eq_abs]
Poincare/Global/HeatDuhamelHeatEquation.lean:149:      exact mul_le_mul_of_nonneg_left (hM p.2 hp.2 _) (heatKernel_nonneg zero_lt_one y)
Poincare/Global/HeatDuhamelHeatEquation.lean:150:  · exact (heatKernel_integrable («E» := E) zero_lt_one).mul_const M
Poincare/Global/HeatDuhamelHeatEquation.lean:151:  · refine Filter.Eventually.of_forall fun y => ?_
Poincare/Global/HeatDuhamelHeatEquation.lean:154:        (continuous_const.sub ((Real.continuous_sqrt.comp continuous_fst).smul continuous_const))
Poincare/Global/HeatDuhamelHeatEquation.lean:155:    exact continuousOn_const.mul (hf.comp hc.continuousOn (fun p hp => ⟨hp.2, mem_univ _⟩))
Poincare/Global/HeatDuhamelHeatEquation.lean:164:    (show Ici (0 : ℝ) ×ˢ Icc 0 T ⊆ univ ×ˢ Icc 0 T from fun p hp => ⟨mem_univ _, hp.2⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:168:  by_cases hz : p.1 = 0
Poincare/Global/HeatDuhamelHeatEquation.lean:169:  · simp [hz, integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
Poincare/Global/HeatDuhamelHeatEquation.lean:174:    rwa [Real.sq_sqrt hpos.le] at he
Poincare/Global/HeatDuhamelHeatEquation.lean:185:      ((continuous_const.sub continuous_id).prodMk continuous_id).continuousOn
Poincare/Global/HeatDuhamelHeatEquation.lean:186:      (fun s hs => ⟨mem_univ _, hs⟩)
Poincare/Global/HeatDuhamelHeatEquation.lean:192:    simp [integral_mul_const, integral_heatKernel_eq_one (show (0 : ℝ) < 1 by norm_num)]
Poincare/Global/HeatDuhamelHeatEquation.lean:195:  filter_upwards [self_mem_nhdsWithin] with s hs
Poincare/Global/HeatDuhamelHeatEquation.lean:196:  have hpos : 0 < t - s := sub_pos.mpr hs.2
Poincare/Global/HeatDuhamelHeatEquation.lean:199:  rw [Real.sq_sqrt hpos.le] at he
Poincare/Global/HeatDuhamelHeatEquation.lean:218:    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
Poincare/Global/HeatDuhamelHeatEquation.lean:219:    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
Poincare/Global/HeatDuhamelHeatEquation.lean:228:  exact intervalIntegral.integral_same
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:98:      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:102:      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:110:set_option linter.flexible false in
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:128:theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:134:    by_cases h : x = 0
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:141:    · exact zero_rpow h
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:148:theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:157:  by_cases h : x = 0 <;> simp [h, zero_le_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:160:  by_cases h : x = 0 <;> simp [h, zero_le_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:163:theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:168:  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg hx_nonneg _
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:177:    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:181:  by_cases hx : x = 0
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:182:  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:195:  obtain hx | hx := (abs_nonneg x).eq_or_lt'
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:202:  simp_rw [Real.norm_eq_abs]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:212:  · rw [zero_rpow h, zero_eq_mul]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:214:    exact this.imp zero_rpow zero_rpow
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:232:  · by_cases h : y + z = 0
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:263:  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:267:  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:271:  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:291:  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:298:  · simp [ofReal_cpow le_rfl]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:299:  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:301:    rw [re_ofReal_mul, im_ofReal_mul, log_re, log_im, mul_comm y, mul_comm y, Real.exp_mul,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:321:  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:325:  by_cases! h : z = 0 → w.re = 0 → w = 0
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:339:    zero_mul, Real.exp_zero, div_one, Complex.norm_of_nonneg hx.le]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:343:  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:348:  filter_upwards [eventually_gt_atTop 0] with t ht
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:397:        pure (.nonnegative q(Real.rpow_nonneg $pa $b))
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:412:theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:413:  rw [← Complex.ofReal_inj, Complex.ofReal_cpow (rpow_nonneg hx _),
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:419:  simp_rw [← rpow_natCast, ← rpow_mul hx, mul_comm y]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:422:  simp_rw [← rpow_intCast, ← rpow_mul hx, mul_comm y]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:427:    Complex.cpow_intCast, ← Complex.ofReal_zpow, mul_comm, Complex.re_ofReal_mul, mul_comm]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:457:  rw [rpow_add' hx h, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:460:  rw [rpow_add' hx h, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:463:  rw [rpow_sub' hx h, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:466:  rw [rpow_sub' hx h, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:472:  rw [rpow_neg_eq_inv_rpow, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:475:set_option linter.flexible false in
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:478:  · rw [log_mul ‹_› ‹_›, add_mul, exp_add, rpow_def_of_pos (hy.lt_of_ne' ‹_›)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:485:  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:492:  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:500:  rw [← rpow_mul hx, mul_inv_cancel₀ hy, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:503:  rw [← rpow_mul hx, inv_mul_cancel₀ hy, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:507:  rw [← rpow_natCast, ← rpow_mul hx, mul_inv_cancel₀ hn0, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:511:  rw [← rpow_natCast, ← rpow_mul hx, inv_mul_cancel₀ hn0, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:514:  rw [rpow_mul hx, rpow_natCast]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:517:  rw [rpow_mul hx, rpow_natCast]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:520:  rw [rpow_mul hx, rpow_intCast]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:523:  rw [rpow_mul hx, rpow_intCast]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:536:  · rw [← hx, zero_rpow (ne_of_gt hz)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:546:theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:553:  fun _ ha _ _ hab => rpow_le_rpow ha hab hr
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:564:  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:609:  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:614:  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:633:  have x_pos : 0 < x := lt_trans zero_lt_one hx
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:645:theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:664:theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:680:theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:691:  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:700:  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:712:  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' ℝ).not_gt]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:715:/-- This is a more general but less convenient version of `rpow_le_rpow_of_exponent_ge`.
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:723:    · rw [zero_rpow hy0]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:725:  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:727:/-- This version of `rpow_le_rpow_of_exponent_ge` allows `x = 0` but requires `0 ≤ z`.
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:729:theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:735:  rcases le_total x y with hxy | hxy
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:740:  simpa only [rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:744:  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:747:  simpa only [rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:751:  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:754:  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:757:  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:760:  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:763:  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:767:  rw [← rpow_one y, ← rpow_one z, ← mul_inv_cancel₀ hx, rpow_mul hy, rpow_mul hz, hyz]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:883:  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:884:  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:889:  · rw [log_zero, zero_rpow hε.ne', zero_div]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:901:  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:902:  exact exp_strictMono.comp <| StrictMono.const_mul strictMono_id <| Real.log_pos hb
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:934:  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:954:  norm_num at this
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:969:  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988:theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:990:  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:991:      ← rpow_natCast, ← rpow_mul h]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:997:  rw [sqrt_eq_rpow, ← rpow_mul hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1008:  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_re, ← div_eq_mul_inv, ← one_div,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1009:    ← Real.sqrt_eq_rpow, cos_half, ← sqrt_mul, ← mul_div_assoc, mul_add, mul_one, norm_mul_cos_arg]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1010:  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1014:  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1015:    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1016:    mul_one, norm_mul_cos_arg]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1022:  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1023:    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (norm_nonneg _),
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1024:    ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1029:  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1030:    ← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1031:    ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1122:  rw [hb.to_eq rfl rfl, div_eq_mul_inv, Real.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1170:@[norm_num (_ : ℝ) ^ (_ : ℝ)]
```

## Final proof diff

```diff
diff --git a/Poincare/Global/DuhamelSolutionOperatorBound.lean b/Poincare/Global/DuhamelSolutionOperatorBound.lean
new file mode 100644
index 00000000..72c1207e
--- /dev/null
+++ b/Poincare/Global/DuhamelSolutionOperatorBound.lean
@@ -0,0 +1,648 @@
+import Poincare.Global.MovingLimitLeibniz
+import Poincare.Global.DuhamelParabolicHolderSeminorm
+import Poincare.Global.ParabolicSolutionGraph
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Interval Laplacian
+
+namespace Poincare.DuhamelSolutionOperatorBound
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+open HeatDuhamelHessianDifferentiation HeatDuhamelHeatEquation ParabolicHolder
+
+/-- The three coordinate diagonal evaluations are bounded by three operator norms. -/
+theorem abs_trace_le (A : E →L[ℝ] E →L[ℝ] ℝ) :
+    |∑ i : Fin 3, A (e i) (e i)| ≤ 3 * ‖A‖ := by
+  calc
+    |∑ i : Fin 3, A (e i) (e i)| ≤ ∑ i : Fin 3, ‖A (e i) (e i)‖ := by
+      simpa only [Real.norm_eq_abs] using
+        norm_sum_le Finset.univ (fun i : Fin 3 => A (e i) (e i))
+    _ ≤ ∑ _i : Fin 3, ‖A‖ := by
+      apply Finset.sum_le_sum
+      intro i _
+      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
+        ContinuousLinearMap.le_opNorm₂ A (e i) (e i)
+    _ = 3 * ‖A‖ := by simp
+
+/-- The within-interval time derivative has the expected sup estimate. -/
+theorem duhamel_time_derivative_bound :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun r => u r x) (f (t,x) + (Δ (u t)) x) (Icc 0 T) t ∧
+      |f (t,x) + (Δ (u t)) x| ≤ M + 3 * C * K * t ^ (α / 2) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  dsimp only
+  intro t ht x
+  have hd := (MovingLimitLeibniz.duhamel_solves_heat_equation
+    α hα hα1 T hT hT1 f M K hM hK hf hfM hfK).2 t ht x
+  rw [← laplacian_eq_hessian_trace] at hd
+  refine ⟨hd, ?_⟩
+  have hb := ((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht x).2.2.2
+  rw [laplacian_eq_hessian_trace]
+  calc
+    _ ≤ |f (t,x)| + 3 * ‖fderiv ℝ (fderiv ℝ (fun z : E =>
+        ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) z)) x‖ :=
+      (abs_add_le _ _).trans (add_le_add le_rfl (abs_trace_le _))
+    _ ≤ M + 3 * (C * K * t ^ (α / 2)) :=
+      add_le_add (hfM t ht x) (mul_le_mul_of_nonneg_left hb (by norm_num))
+    _ = M + 3 * C * K * t ^ (α / 2) := by ring
+
+/-- Tracing the parabolic Hessian increment controls the time derivative increment. -/
+theorem duhamel_time_derivative_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    HasHolderBound α (cylinder T) f K →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    HasHolderBound α (cylinder T) (fun p => f p + (Δ (u p.1)) p.2)
+      (K + 3 * C * K) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ :=
+    DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
+      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using
+      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  dsimp only
+  intro p hp q hq
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  have hb := hCb T hT hT1 f M K hM hK hf hfM hspace p hp q hq
+  have htrace : |(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2| ≤
+      3 * ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 -
+        fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
+    simpa only [laplacian_eq_hessian_trace, ContinuousLinearMap.sub_apply,
+      Finset.sum_sub_distrib] using abs_trace_le
+        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
+  change ‖(f p + (Δ (u p.1)) p.2) - (f q + (Δ (u q.1)) q.2)‖ ≤ _
+  rw [add_sub_add_comm]
+  calc
+    _ ≤ ‖f p - f q‖ + ‖(Δ (u p.1)) p.2 - (Δ (u q.1)) q.2‖ := norm_add_le _ _
+    _ ≤ K * parabolicDist p q ^ α + 3 * (C * K * parabolicDist p q ^ α) :=
+      add_le_add (hfK p hp q hq)
+        (htrace.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
+    _ = (K + 3 * C * K) * parabolicDist p q ^ α := by ring
+
+/-- Integrating the gradient kernel gives the sharp square-root time factor. -/
+theorem duhamel_gradient_bound {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
+    ‖fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t-s) (fun y => f (s,y)) z) x‖ ≤
+      2 * M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * Real.sqrt t := by
+  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
+  let A := M * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖)
+  have hb : ‖∫ s in (0 : ℝ)..t,
+      fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) x‖ ≤
+      ∫ s in (0 : ℝ)..t, A * (t-s) ^ (-(1/2 : ℝ)) := by
+    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
+      ← restrict_Ioo_eq_restrict_Ioc]
+    apply MeasureTheory.norm_integral_le_of_norm_le
+      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+        (intervalIntegrable_gradient_majorant t A))
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
+    have hc : Continuous (fun y : E => f (s,y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) hc.aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s hsT) x
+  have he := HeatDuhamelSpatialHolderHessian.integral_hessian_majorant zero_lt_one t A
+  norm_num only [div_one, show (1 : ℝ) / 2 - 1 = -(1/2 : ℝ) by norm_num] at he
+  rw [he] at hb
+  simpa [A, Real.sqrt_eq_rpow, mul_assoc, mul_left_comm, mul_comm] using hb
+
+/-- A uniform time-derivative bound controls all value increments and the initial trace. -/
+theorem duhamel_value_time_estimates :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    (∀ t ∈ Icc 0 T, ∀ x : E, |u t x| ≤ t * (M + 3 * C * K * T ^ (α/2))) ∧
+    (∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T, ∀ x : E,
+      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s|) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
+  refine ⟨C, hC, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  have hd := hCb T hT hT1 f M K hM hK hf hfM hfK
+  have hb (r : ℝ) (hr : r ∈ Icc 0 T) (x : E) :
+      ‖f (r,x) + (Δ (u r)) x‖ ≤ M + 3 * C * K * T ^ (α/2) := by
+    apply (hd r hr x).2.trans
+    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow hr.1 hr.2 (by linarith)) (by positivity))
+  have hi (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 T) (x : E) :
+      |u t x - u s x| ≤ (M + 3 * C * K * T ^ (α/2)) * |t-s| := by
+    simpa only [Real.norm_eq_abs] using
+      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+        (fun r hr => (hd r hr x).1) (fun r hr => hb r hr x) (convex_Icc (0 : ℝ) T) hs ht
+  refine ⟨?_, hi⟩
+  intro t ht x
+  simpa [u, abs_of_nonneg ht.1, mul_comm] using hi t ht 0 ⟨le_rfl, hT.le⟩ x
+
+/-- Bounded Lipschitz increments give every intermediate Hölder exponent. -/
+theorem holder_of_bounded_lipschitz {F : Type*} [NormedAddCommGroup F]
+    {α A B : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
+    {g : E → F} (hg : ∀ x, ‖g x‖ ≤ A)
+    (hlip : ∀ x y, ‖g x - g y‖ ≤ B * ‖x-y‖) (x y : E) :
+    ‖g x - g y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+  by_cases hr : ‖x-y‖ ≤ 1
+  · have hp : ‖x-y‖ ≤ ‖x-y‖ ^ α := by
+      simpa only [Real.rpow_one] using
+        Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hr hα hα1
+    exact (hlip x y).trans ((mul_le_mul_of_nonneg_left hp hB).trans
+      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2*A+B)
+        (Real.rpow_nonneg (norm_nonneg _) _)))
+  · have hp : 1 ≤ ‖x-y‖ ^ α := Real.one_le_rpow (le_of_not_ge hr) hα
+    calc
+      ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
+      _ ≤ 2*A := by linarith [hg x, hg y]
+      _ ≤ (2*A+B) * ‖x-y‖ ^ α := by
+        calc
+          2*A ≤ 2*A+B := by linarith
+          _ ≤ (2*A+B) * ‖x-y‖ ^ α := le_mul_of_one_le_right (by positivity) hp
+
+/-- The gradient is spatially Hölder with a constant uniform on short time intervals. -/
+theorem duhamel_gradient_spatial_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    let u : ℝ → E → ℝ := fun t x =>
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+    ∀ t ∈ Icc 0 T, ∀ x y : E,
+      ‖fderiv ℝ (u t) x - fderiv ℝ (u t) y‖ ≤ C * (M+K) * ‖x-y‖ ^ α := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_hessian_bound α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨4*J+C, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  dsimp only
+  intro t ht x y
+  let u : E → ℝ := fun z => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun w => f (s,w)) z
+  have hg (z : E) : ‖fderiv ℝ u z‖ ≤ 2*M*J :=
+    (duhamel_gradient_bound ht hf hfM z).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
+  have hh (z : E) : ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ C*K :=
+    (((hCb T hT hT1 f M K hM hK hf hfM hfK).2 t ht z).2.2.2).trans
+      (mul_le_of_le_one_right (by positivity)
+        (Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)))
+  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
+    ((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
+      (m := 1) (by norm_num)).differentiable_one
+  have hlip (a b : E) : ‖fderiv ℝ u a - fderiv ℝ u b‖ ≤ C*K*‖a-b‖ :=
+    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
+      (fun z _ => hh z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ b) (mem_univ a)
+  have hb := holder_of_bounded_lipschitz hα.le hα1.le
+    (by positivity : 0 ≤ 2*M*J) (by positivity : 0 ≤ C*K) hg hlip x y
+  exact hb.trans (mul_le_mul_of_nonneg_right
+    (by nlinarith [mul_nonneg hJ hK, mul_nonneg hC.le hM] :
+      2*(2*M*J)+C*K ≤ (4*J+C)*(M+K)) (Real.rpow_nonneg (norm_nonneg _) _))
+
+/-- Value increments obey a parabolic Hölder bound uniform for times at most one. -/
+theorem duhamel_value_parabolic_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+    HasHolderBound α (cylinder T)
+      (fun p : ℝ × E => ∫ s in (0 : ℝ)..p.1,
+        heatSolution (p.1-s) (fun y => f (s,y)) p.2) (C * (M+K)) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_value_time_estimates α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨3+9*C+2*J, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  let D := M+3*C*K
+  have hD : 0 ≤ D := by dsimp [D]; positivity
+  have hd : M+3*C*K*T^(α/2) ≤ D := by
+    exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity)
+      (Real.rpow_le_one hT.le hT1 (by linarith)))
+  have hv := hCb T hT hT1 f M K hM hK hf hfM hfK
+  have hu (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖u t x‖ ≤ D := by
+    exact (hv.1 t ht x).trans ((mul_le_mul_of_nonneg_left hd ht.1).trans
+      (mul_le_of_le_one_left hD (ht.2.trans hT1)))
+  have hg (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) : ‖fderiv ℝ (u t) x‖ ≤ 2*M*J :=
+    (duhamel_gradient_bound ht hf hfM x).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (ht.2.trans hT1)))
+  intro p hp q hq
+  have hs : ‖u p.1 p.2 - u p.1 q.2‖ ≤ (2*D+2*M*J)*‖p.2-q.2‖^α := by
+    apply holder_of_bounded_lipschitz hα.le hα1.le hD (by positivity) (hu p.1 hp.1)
+    intro a b
+    exact Convex.norm_image_sub_le_of_norm_fderiv_le
+      (fun z _ => (hasFDerivAt_duhamel hp.1 hf hfM z).differentiableAt)
+      (fun z _ => hg p.1 hp.1 z) (convex_univ : Convex ℝ (univ : Set E))
+      (mem_univ b) (mem_univ a)
+  have hab : |p.1-q.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2],
+    by linarith [hp.1.1, hp.1.2, hq.1.1, hq.1.2]⟩
+  have htp : |p.1-q.1| ≤ parabolicDist p q ^ α := by
+    calc
+      |p.1-q.1| ≤ |p.1-q.1|^(α/2) := by
+        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
+          (abs_nonneg (p.1-q.1)) hab (by linarith : 0 ≤ α/2) (by linarith : α/2 ≤ 1)
+      _ = (Real.sqrt |p.1-q.1|)^α := by
+        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
+        congr 1
+        ring
+      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
+        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
+  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
+  have ht : ‖u p.1 q.2 - u q.1 q.2‖ ≤ D * parabolicDist p q ^ α :=
+    (hv.2 p.1 hp.1 q.1 hq.1 q.2).trans
+      ((mul_le_mul_of_nonneg_right hd (abs_nonneg _)).trans (mul_le_mul_of_nonneg_left htp hD))
+  calc
+    ‖u p.1 p.2 - u q.1 q.2‖ ≤ ‖u p.1 p.2 - u p.1 q.2‖ + ‖u p.1 q.2 - u q.1 q.2‖ :=
+      norm_sub_le_norm_sub_add_norm_sub ..
+    _ ≤ (2*D+2*M*J)*parabolicDist p q ^ α + D*parabolicDist p q ^ α :=
+      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity))) ht
+    _ ≤ (3+9*C+2*J)*(M+K)*parabolicDist p q ^ α := by
+      rw [← add_mul]
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (parabolicDist_nonneg _ _) _)
+      dsimp [D]
+      nlinarith [mul_nonneg hC.le hM, mul_nonneg hJ hK]
+
+/-- A difference of bounded data has the same gradient kernel estimate. -/
+theorem gradient_heatSolution_sub_bound {t M N L : ℝ} (ht : 0 < t)
+    {f g : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hg : AEStronglyMeasurable g volume) (hfM : ∀ y, ‖f y‖ ≤ M)
+    (hgN : ∀ y, ‖g y‖ ≤ N) (hL : ∀ y, ‖f y - g y‖ ≤ L) (x : E) :
+    ‖fderiv ℝ (heatSolution t f) x - fderiv ℝ (heatSolution t g) x‖ ≤
+      L * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * t ^ (-(1/2 : ℝ)) := by
+  have hi := integrable_smul_fderiv_heatKernel_sub ht hf hfM x
+  have hj := integrable_smul_fderiv_heatKernel_sub ht hg hgN x
+  rw [(heatSolution_hasFDerivAt ht hf hfM x).fderiv,
+    (heatSolution_hasFDerivAt ht hg hgN x).fderiv, ← integral_sub hi hj]
+  have he : (fun y : E => f y • fderiv ℝ (heatKernel t) (x-y) -
+      g y • fderiv ℝ (heatKernel t) (x-y)) =
+      fun y => (f y - g y) • fderiv ℝ (heatKernel t) (x-y) := by
+    ext y v
+    simp [sub_smul]
+  rw [he]
+  have hb := norm_gradient_heatSolution_le ht (hf.sub hg) hL x
+  rw [(heatSolution_hasFDerivAt ht (hf.sub hg) hL x).fderiv] at hb
+  exact hb
+
+/-- Reversing Duhamel time keeps the gradient kernel fixed when comparing forcing times. -/
+theorem duhamel_gradient_reversed {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (cylinder T))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s,y)| ≤ M) (x : E) :
+    fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t-s) (fun y => f (s,y)) z) x =
+      ∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x := by
+  rw [(hasFDerivAt_duhamel ht hf hM x).fderiv]
+  have he := intervalIntegral.integral_comp_sub_left
+    (fun s : ℝ => fderiv ℝ (heatSolution s (fun y => f (t-s,y))) x)
+    (a := 0) (b := t) t
+  simpa only [sub_sub_cancel, sub_self, sub_zero] using he
+
+/-- The inverse square-root majorant controls an arbitrary nonnegative time interval. -/
+theorem norm_integral_inverse_sqrt_le {F : Type*} [NormedAddCommGroup F]
+    [NormedSpace ℝ F] {a b A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A)
+    {g : ℝ → F} (hg : ∀ r ∈ Ioo a b, ‖g r‖ ≤ A * r ^ (-(1/2 : ℝ))) :
+    ‖∫ r in a..b, g r‖ ≤ 2*A*Real.sqrt (b-a) := by
+  have hb : 0 ≤ b := ha.trans hab
+  have hi : IntervalIntegrable (fun r : ℝ => A * r ^ (-(1/2 : ℝ))) volume a b :=
+    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2 : ℝ))).const_mul A
+  have hbound : ‖∫ r in a..b, g r‖ ≤ ∫ r in a..b, A * r ^ (-(1/2 : ℝ)) := by
+    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
+      ← restrict_Ioo_eq_restrict_Ioc]
+    apply MeasureTheory.norm_integral_le_of_norm_le
+      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
+    exact hg r hr
+  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))] at hbound
+  norm_num only [show -(1/2 : ℝ)+1 = 1/2 by norm_num] at hbound
+  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hbound
+  have hs : Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b-a) := by
+    have h1 := Real.sq_sqrt ha
+    have h2 := Real.sq_sqrt hb
+    have h3 := Real.sq_sqrt (sub_nonneg.mpr hab)
+    have h4 := Real.sqrt_nonneg a
+    have h5 := Real.sqrt_nonneg b
+    have h6 := Real.sqrt_nonneg (b-a)
+    nlinarith [mul_nonneg h4 h6]
+  calc
+    _ ≤ A * ((Real.sqrt b - Real.sqrt a) / (1/2)) := hbound
+    _ = 2*A*(Real.sqrt b - Real.sqrt a) := by ring
+    _ ≤ 2*A*Real.sqrt (b-a) := mul_le_mul_of_nonneg_left hs (by positivity)
+
+/-- Reversed time separates a forcing increment from a short gradient tail. -/
+theorem duhamel_gradient_time_holder_of_le {α T s t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hT1 : T ≤ 1)
+    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t)
+    (hM : 0 ≤ M) (hK : 0 ≤ K) {f : ℝ × E → ℝ}
+    (hf : ContinuousOn f (cylinder T))
+    (hfM : ∀ r ∈ Icc 0 T, ∀ y : E, |f (r,y)| ≤ M)
+    (hfK : HasHolderBound α (cylinder T) f K) (x : E) :
+    let u : ℝ → E → ℝ := fun r z =>
+      ∫ v in (0 : ℝ)..r, heatSolution (r-v) (fun y => f (v,y)) z
+    ‖fderiv ℝ (u t) x - fderiv ℝ (u s) x‖ ≤
+      2 * (∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖) * (M+K) * (t-s)^(α/2) := by
+  dsimp only
+  rw [duhamel_gradient_reversed ht hf hfM, duhamel_gradient_reversed hs hf hfM]
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  let v : ℝ → ℝ → E →L[ℝ] ℝ := fun a r =>
+    fderiv ℝ (heatSolution r (fun y => f (a-r,y))) x
+  have hi (a : ℝ) (ha : a ∈ Icc 0 T) : IntervalIntegrable (v a) volume 0 a := by
+    have h := (intervalIntegrable_gradient_heatSolution_time ha hf hfM x).comp_sub_left a
+    simpa only [v, sub_zero, sub_self, sub_sub_cancel] using h.symm
+  have hsub0 : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
+    simpa only [uIcc_of_le hs.1, uIcc_of_le ht.1] using Icc_subset_Icc le_rfl hst
+  have hsub1 : uIcc s t ⊆ uIcc 0 t := by
+    simpa only [uIcc_of_le hst, uIcc_of_le ht.1] using Icc_subset_Icc hs.1 le_rfl
+  have hit0 := (hi t ht).mono_set hsub0
+  have hit1 := (hi t ht).mono_set hsub1
+  have hc (a : ℝ) (ha : a ∈ Icc 0 T) (r : ℝ) (hr : r ∈ Icc 0 a) :
+      Continuous (fun y : E => f (a-r,y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨⟨by linarith [hr.2], by linarith [hr.1, ha.2]⟩, mem_univ y⟩)
+  have hδ : 0 ≤ t-s := sub_nonneg.mpr hst
+  have hb0 : ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ ≤
+      2 * (K * (t-s)^(α/2) * J) * Real.sqrt s := by
+    simpa only [sub_zero] using norm_integral_inverse_sqrt_le
+      (a := 0) (b := s) le_rfl hs.1 (by positivity : 0 ≤ K*(t-s)^(α/2)*J)
+      (g := fun r => v t r - v s r) (by
+        intro r hr
+        have hrt : r ∈ Icc 0 t := ⟨hr.1.le, hr.2.le.trans hst⟩
+        have hrs : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.le⟩
+        apply gradient_heatSolution_sub_bound hr.1 (hc t ht r hrt).aestronglyMeasurable
+          (hc s hs r hrs).aestronglyMeasurable
+          (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y)
+          (fun y => hfM (s-r) ⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩ y)
+        intro y
+        have h := hfK (t-r,y) ⟨⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩, mem_univ y⟩
+          (s-r,y) ⟨⟨by linarith [hrs.2], by linarith [hrs.1, hs.2]⟩, mem_univ y⟩
+        simpa [parabolicDist, sub_sub_sub_cancel_right, abs_of_nonneg (sub_nonneg.mpr hst),
+          Real.sqrt_eq_rpow, ← Real.rpow_mul (sub_nonneg.mpr hst), mul_comm, div_eq_mul_inv] using h)
+  have hb1 : ‖∫ r in s..t, v t r‖ ≤ 2*(M*J)*Real.sqrt (t-s) := by
+    apply norm_integral_inverse_sqrt_le hs.1 hst (by positivity)
+    intro r hr
+    have hrt : r ∈ Icc 0 t := ⟨hs.1.trans hr.1.le, hr.2.le⟩
+    exact norm_gradient_heatSolution_le (lt_of_le_of_lt hs.1 hr.1)
+      (hc t ht r hrt).aestronglyMeasurable
+      (fun y => hfM (t-r) ⟨by linarith [hrt.2], by linarith [hrt.1, ht.2]⟩ y) x
+  have hδ1 : t-s ≤ 1 := by linarith [ht.2, hs.1]
+  have hpow : Real.sqrt (t-s) ≤ (t-s)^(α/2) := by
+    rw [Real.sqrt_eq_rpow]
+    exact Real.rpow_le_rpow_of_exponent_ge' hδ hδ1 (by linarith) (by linarith)
+  change ‖(∫ r in (0 : ℝ)..t, v t r) - ∫ r in (0 : ℝ)..s, v s r‖ ≤ _
+  rw [← intervalIntegral.integral_add_adjacent_intervals hit0 hit1,
+    add_sub_right_comm, ← intervalIntegral.integral_sub hit0 (hi s hs)]
+  calc
+    _ ≤ ‖∫ r in (0 : ℝ)..s, v t r - v s r‖ + ‖∫ r in s..t, v t r‖ := norm_add_le _ _
+    _ ≤ 2*(K*(t-s)^(α/2)*J)*Real.sqrt s + 2*(M*J)*Real.sqrt (t-s) := add_le_add hb0 hb1
+    _ ≤ 2*(K*(t-s)^(α/2)*J) + 2*(M*J)*(t-s)^(α/2) :=
+      add_le_add (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hs.2.trans hT1)))
+        (mul_le_mul_of_nonneg_left hpow (by positivity))
+    _ = 2*J*(M+K)*(t-s)^(α/2) := by ring
+
+/-- Spatial interpolation and reversed-time integration give the full gradient estimate. -/
+theorem duhamel_gradient_parabolic_holder :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+    ContinuousOn f (cylinder T) →
+    (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+    HasHolderBound α (cylinder T) f K →
+    HasHolderBound α (cylinder T)
+      (fun p : ℝ × E => fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..p.1,
+        heatSolution (p.1-s) (fun y => f (s,y)) z) p.2) (C * (M+K)) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_gradient_spatial_holder α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨C+2*J, by positivity, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  have hspace : ∀ t ∈ Icc 0 T, ∀ x y : E,
+      |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using
+      hfK (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  intro p hp q hq
+  have hs := hCb T hT hT1 f M K hM hK hf hfM hspace p.1 hp.1 p.2 q.2
+  have ht : ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ ≤
+      2*J*(M+K)*|p.1-q.1|^(α/2) := by
+    rcases le_total q.1 p.1 with hqp | hpq
+    · simpa only [abs_of_nonneg (sub_nonneg.mpr hqp)] using
+        duhamel_gradient_time_holder_of_le hα hα1 hT1 hq.1 hp.1 hqp hM hK hf hfM hfK q.2
+    · simpa only [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hpq), neg_sub] using
+        duhamel_gradient_time_holder_of_le hα hα1 hT1 hp.1 hq.1 hpq hM hK hf hfM hfK q.2
+  have hsp : ‖p.2-q.2‖^α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
+  have htp : |p.1-q.1|^(α/2) ≤ parabolicDist p q ^ α := by
+    calc
+      _ = (Real.sqrt |p.1-q.1|)^α := by
+        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
+        congr 1
+        ring
+      _ ≤ parabolicDist p q ^ α := Real.rpow_le_rpow (Real.sqrt_nonneg _)
+        (le_add_of_nonneg_left (norm_nonneg _)) hα.le
+  calc
+    ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u q.1) q.2‖ ≤
+        ‖fderiv ℝ (u p.1) p.2 - fderiv ℝ (u p.1) q.2‖ +
+        ‖fderiv ℝ (u p.1) q.2 - fderiv ℝ (u q.1) q.2‖ := norm_sub_le_norm_sub_add_norm_sub ..
+    _ ≤ C*(M+K)*parabolicDist p q ^ α + 2*J*(M+K)*parabolicDist p q ^ α :=
+      add_le_add (hs.trans (mul_le_mul_of_nonneg_left hsp (by positivity)))
+        (ht.trans (mul_le_mul_of_nonneg_left htp (by positivity)))
+    _ = (C+2*J)*(M+K)*parabolicDist p q ^ α := by ring
+
+/-- Positive parabolic Hölder control implies continuity on the cylinder. -/
+theorem continuousOn_of_hasHolderBound {F : Type*} [NormedAddCommGroup F]
+    {α T K : ℝ} (hα : 0 < α) {g : ℝ × E → F}
+    (hg : HasHolderBound α (cylinder T) g K) : ContinuousOn g (cylinder T) := by
+  intro p hp
+  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
+  have hc : Continuous (fun q : ℝ × E => K * parabolicDist q p ^ α) := by
+    dsimp [parabolicDist]
+    fun_prop (disch := positivity)
+  have hz : K * parabolicDist p p ^ α = 0 := by
+    simp [parabolicDist, Real.zero_rpow hα.ne']
+  have hlim : Filter.Tendsto (fun q => K * parabolicDist q p ^ α)
+      (nhdsWithin p (cylinder T)) (nhds (K * parabolicDist p p ^ α)) :=
+    hc.continuousAt.continuousWithinAt
+  rw [hz] at hlim
+  apply squeeze_zero' (Filter.Eventually.of_forall (fun q => norm_nonneg (g q - g p))) _ hlim
+  filter_upwards [self_mem_nhdsWithin] with q hq
+  exact hg q hq p hp
+
+set_option maxHeartbeats 800000 in
+/-- The constant-coefficient Duhamel solution is bounded in the full solution graph norm. -/
+theorem exists_solution_graph_bound :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
+    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
+      (∀ p ∈ ParabolicHolder.cylinder («E» := E) T,
+        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
+      ‖G‖ ≤ C * ‖f‖ := by
+  intro α hα hα1
+  obtain ⟨A, hA, hAb⟩ := duhamel_hessian_bound α hα hα1
+  obtain ⟨B, hB, hBb⟩ := DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian α hα hα1
+  obtain ⟨C, hC, hCb⟩ := duhamel_time_derivative_bound α hα hα1
+  obtain ⟨D, hD, hDb⟩ := duhamel_time_derivative_holder α hα hα1
+  obtain ⟨V, hV, hVb⟩ := duhamel_value_time_estimates α hα hα1
+  obtain ⟨W, hW, hWb⟩ := duhamel_value_parabolic_holder α hα hα1
+  obtain ⟨Q, hQ, hQb⟩ := duhamel_gradient_parabolic_holder α hα hα1
+  let J := ∫ y : E, ‖fderiv ℝ (heatKernel 1) y‖
+  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
+  refine ⟨(1+3*V)+2*W+(1+3*C)+(1+3*D)+2*J+2*Q+A+B, by positivity, ?_⟩
+  intro T hT hT1 f
+  let N := ‖f‖
+  have hN : 0 ≤ N := norm_nonneg f
+  have hfH : HasHolderBound α (cylinder T) f N := ParabolicHolder.hasHolderBound f
+  have hf : ContinuousOn f (cylinder T) := continuousOn_of_hasHolderBound hα hfH
+  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ N :=
+    fun t _ x => ParabolicHolder.norm_le f (t,x)
+  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x)-f (t,y)| ≤ N*‖x-y‖^α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using hfH (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  let v : ℝ × E → ℝ := fun p => f p + (Δ (u p.1)) p.2
+  let d : ℝ × E → E →L[ℝ] ℝ := fun p => fderiv ℝ (u p.1) p.2
+  let dd : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2
+  have hpow (t : ℝ) (ht : t ∈ Icc 0 T) : t^(α/2) ≤ 1 :=
+    Real.rpow_le_one ht.1 (ht.2.trans hT1) (by linarith)
+  have htime := hCb T hT hT1 f N N hN hN hf hfM hfK
+  have hvalue := hVb T hT hT1 f N N hN hN hf hfM hfK
+  have huB : ∀ p ∈ cylinder T, ‖u p.1 p.2‖ ≤ (1+3*V)*N := by
+    intro p hp
+    have hb : N+3*V*N*T^(α/2) ≤ (1+3*V)*N := by
+      have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*V*N)
+        (hpow T ⟨hT.le, le_rfl⟩)
+      nlinarith
+    exact (hvalue.1 p.1 hp.1 p.2).trans ((mul_le_mul_of_nonneg_left hb hp.1.1).trans
+      (mul_le_of_le_one_left (by positivity) (hp.1.2.trans hT1)))
+  have hvB : ∀ p ∈ cylinder T, ‖v p‖ ≤ (1+3*C)*N := by
+    intro p hp
+    have h := mul_le_of_le_one_right (by positivity : 0 ≤ 3*C*N) (hpow p.1 hp.1)
+    have hb := (htime p.1 hp.1 p.2).2
+    change |f p + (Δ (u p.1)) p.2| ≤ _
+    nlinarith
+  have hdB : ∀ p ∈ cylinder T, ‖d p‖ ≤ 2*J*N := by
+    intro p hp
+    have h := (duhamel_gradient_bound hp.1 hf hfM p.2).trans
+      (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr (hp.1.2.trans hT1)))
+    simpa only [d, J, mul_comm, mul_left_comm, mul_assoc] using h
+  have hddB : ∀ p ∈ cylinder T, ‖dd p‖ ≤ A*N := by
+    intro p hp
+    exact (((hAb T hT hT1 f N N hN hN hf hfM hfK).2 p.1 hp.1 p.2).2.2.2).trans
+      (mul_le_of_le_one_right (by positivity) (hpow p.1 hp.1))
+  have huH : HasHolderBound α (cylinder T) (fun p => u p.1 p.2) (2*W*N) := by
+    convert hWb T hT hT1 f N N hN hN hf hfM hfK using 1
+    ring
+  have hvH : HasHolderBound α (cylinder T) v ((1+3*D)*N) := by
+    convert hDb T hT hT1 f N N hN hN hf hfM hfH using 1
+    ring
+  have hdH : HasHolderBound α (cylinder T) d (2*Q*N) := by
+    convert hQb T hT hT1 f N N hN hN hf hfM hfH using 1
+    ring
+  have hddH : HasHolderBound α (cylinder T) dd (B*N) := hBb T hT hT1 f N N hN hN hf hfM hfK
+  have liftB {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
+      (hb : ∀ p ∈ cylinder T, ‖g p‖ ≤ b) :
+      ∀ p ∈ cylinder T, ‖(cylinder T).indicator g p‖ ≤ b := by
+    intro p hp
+    simpa only [indicator_of_mem hp] using hb p hp
+  have liftH {F : Type} [NormedAddCommGroup F] (g : ℝ × E → F) {b : ℝ}
+      (hb : HasHolderBound α (cylinder T) g b) :
+      HasHolderBound α (cylinder T) ((cylinder T).indicator g) b := by
+    intro p hp q hq
+    simpa only [indicator_of_mem hp, indicator_of_mem hq] using hb p hp q hq
+  let iu := (cylinder T).indicator (fun p : ℝ × E => u p.1 p.2)
+  let iv := (cylinder T).indicator v
+  let idu := (cylinder T).indicator d
+  let iddu := (cylinder T).indicator dd
+  have huS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => iu (t,z)) = u t := by
+    funext z
+    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
+  have hdS (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => idu (t,z)) = fderiv ℝ (u t) := by
+    funext z
+    exact indicator_of_mem (show (t,z) ∈ cylinder T from ⟨ht, mem_univ z⟩) _
+  have hzero : ∀ x : E, iu (0,x) = 0 := by
+    intro x
+    rw [show iu (0,x) = u 0 x from congrFun (huS 0 ⟨le_rfl, hT.le⟩) x]
+    exact intervalIntegral.integral_same
+  have hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z => iu (t,z)) (idu (t,x)) x := by
+    intro t ht x
+    rw [huS t ht]
+    have hd0 : idu (t,x) = fderiv ℝ (u t) x := congrFun (hdS t ht) x
+    rw [hd0]
+    exact (hasFDerivAt_duhamel ht hf hfM x).differentiableAt.hasFDerivAt
+  have hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z => idu (t,z)) (iddu (t,x)) x := by
+    intro t ht x
+    rw [hdS t ht]
+    change HasFDerivAt (fderiv ℝ (u t)) ((cylinder T).indicator dd (t,x)) x
+    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
+    exact (((contDiff_two_duhamel hα hα1 ht hf hfM hfK).fderiv_right
+      (m := 1) (by norm_num)).differentiable_one x).hasFDerivAt
+  have hut : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun s => iu (s,x)) (iv (t,x)) (Icc 0 T) t := by
+    intro t ht x
+    change HasDerivWithinAt _ ((cylinder T).indicator v (t,x)) _ _
+    rw [indicator_of_mem (show (t,x) ∈ cylinder T from ⟨ht, mem_univ x⟩)]
+    exact ((htime t ht x).1).congr_of_mem (fun s hs => congrFun (huS s hs) x) ht
+  let G : ParabolicSolutionGraph.Graph («E» := E) α T :=
+    ParabolicSolutionGraph.ofDerivatives iu iv idu iddu
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB (fun p => u p.1 p.2) huB⟩ ⟨_, liftH (fun p => u p.1 p.2) huH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB v hvB⟩ ⟨_, liftH v hvH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB d hdB⟩ ⟨_, liftH d hdH⟩
+      (fun p hp => indicator_of_notMem hp _) ⟨_, liftB dd hddB⟩ ⟨_, liftH dd hddH⟩
+      hzero hdu hddu hut
+  refine ⟨G, ?_, ?_⟩
+  · intro p hp
+    change (cylinder T).indicator (fun q : ℝ × E => u q.1 q.2) p = u p.1 p.2
+    exact indicator_of_mem hp _
+  · have huN : ‖G.u‖ ≤ (1+3*V)*N+2*W*N :=
+      norm_le_of_bounds G.u (by positivity) (by positivity) (liftB (fun p => u p.1 p.2) huB) (liftH (fun p => u p.1 p.2) huH)
+    have hvN : ‖G.ut‖ ≤ (1+3*C)*N+(1+3*D)*N :=
+      norm_le_of_bounds G.ut (by positivity) (by positivity) (liftB v hvB) (liftH v hvH)
+    have hdN : ‖G.du‖ ≤ 2*J*N+2*Q*N :=
+      norm_le_of_bounds G.du (by positivity) (by positivity) (liftB d hdB) (liftH d hdH)
+    have hddN : ‖G.ddu‖ ≤ A*N+B*N :=
+      norm_le_of_bounds G.ddu (by positivity) (by positivity) (liftB dd hddB) (liftH dd hddH)
+    rw [ParabolicSolutionGraph.norm_eq]
+    change ‖G.u‖+‖G.ut‖+‖G.du‖+‖G.ddu‖ ≤ _ * N
+    nlinarith
+
+end Poincare.DuhamelSolutionOperatorBound
```
