# Heat Duhamel Hessian differentiation: completed worker proof

Date: 2026-09-10. Class B. The frozen K2 theorem is proved as
`Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound`.
The exact statement assignment, focused compiler gate, token scan, exact
dependency scan and whitespace gate pass. This is a worker result awaiting
independent orchestrator review, not a merge or task acceptance.

Base: `0642d40ece03832420101813ecfc8224472a0552`.
Proof head: `2807e7630b5aa326dfe0e4896a26ea23df885e7a`.
Branch: `worker/heat-duhamel-hessian-differentiation`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.
Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.

The initial checkout was clean at the recorded base. Git status, worktree
inventory and HEAD were checked before editing. The supplied worker branch
takes precedence over the general branch-prefix convention. No subagent was
launched. The task owns this new Lean file exclusively.

## What is proved

The new module is `Poincare/Global/HeatDuhamelHessianDifferentiation.lean`,
with exactly the requested namespace and one import of the landed
`HeatDuhamelSpatialHolderHessian` module. It contains 20 theorems and the
required local normed-group instance. Every one of these 21 declarations has
exactly `[propext, Classical.choice, Quot.sound]` as its foundational dependency
set. The module has no new definitions or analytic assumptions hidden behind
local notation. The `E`, `Hess` and operator-norm conventions agree with the
frozen target.

1. `gradient_eq`, `gradient_sq_smul`, `integrable_gradient`,
   `gradient_integral_sq`, `gradient_integral` prove the full gradient formula,
   Bochner integrability and the exact moment identity
   `∫ ‖Grad t y‖ = (∫ ‖Grad 1 y‖) * t^(-1/2)` for every positive time.
   `gradient_heatSolution_eq_integral` and `norm_gradient_heatSolution_le`
   identify the bounded measurable-data convolution gradient and bound it
   uniformly by `M * (∫ ‖Grad 1 y‖) * t^(-1/2)`.
2. `continuous_gradient_pos`, `gradient_convolution_sq` and
   `continuous_gradient_heatSolution_time` prove joint positive-time gradient
   continuity and joint continuity of the actual Duhamel gradient integrand.
   The convolution is dilated to a fixed unit-time kernel, with domination
   `M * ‖Grad 1 y‖`. `intervalIntegrable_gradient_majorant` and
   `intervalIntegrable_gradient_heatSolution_time` prove endpoint time
   integrability. This closes both branches left by the prior step-3 probe;
   the measurability branch follows for every observation point from the
   actual interval-integrability theorem.
3. `continuous_kernel_pos`, `intervalIntegrable_heatSolution_time` and
   `hasFDerivAt_duhamel` prove actual first spatial differentiation of the
   specified Duhamel value through its time integral. Scalar kernel mass one
   bounds the value integrand by `M` for its integrability proof.
4. `hasFDerivAt_duhamel_gradient` proves the second differentiation with the
   cancelled Hessian as derivative candidate and the landed integrable
   majorant `K * Jα * (t-s)^(α/2-1)`.
5. `continuous_duhamel_hessian` proves continuity of the double integral by
   dominated convergence. At each positive elapsed time its spatial
   continuity follows from the landed bounded-data C² theorem and the
   cancelled-kernel identity. `hessian_duhamel_eq_integral` identifies the
   actual second derivative, and `contDiff_two_duhamel` proves spatial C²
   regularity using the two derivative theorems and continuity.
6. `duhamel_hessian_bound` assembles the exact frozen statement with
   `C = max 1 (Jα * (2 / α))`, where
   `Jα = ∫ y, ‖Hess 1 y‖ * ‖y‖^α`. This positive constant depends only on
   `α`. All time endpoints and forcing hypotheses are retained, including
   `t = 0`; the zero initial trace uses `intervalIntegral.integral_same`.

The proof does not require a positive time lower bound, time Hölder control,
uniform continuity in time in a supremum norm, or any extra forcing premise.
It proves the spatial K2 estimate. It does not claim the later parabolic
Hölder estimate, time PDE, variable-coefficient solvability, or the Poincare
conjecture.

## Scope and review

Exactly one new repository Lean file is delivered. Existing Lean sources,
`Poincare.lean`, frozen task files, ledgers, missions and audit wiring were
not edited. This report and a dated `HANDOFF.md` entry are the other changes.
Every verified theorem was committed separately on the supplied branch.
No full build or root integration audit was run; these belong to integration.

First action for independent review:

```sh
git diff 0642d40ece03832420101813ecfc8224472a0552..2807e7630b5aa326dfe0e4896a26ea23df885e7a -- Poincare/Global/HeatDuhamelHessianDifferentiation.lean
```

Then rerun the focused gate and the exact assignment and dependency probes
below against the base cache. The report embeds every compiler probe's actual
output, source deltas, final dependency checks and the final proof diff.
Scratch files remain under `/tmp/heat-duhamel-hessian-differentiation` for this
session; the embedded evidence and git history suffice after they disappear.

## Final gates

All Lean commands below used `LEAN_NUM_THREADS=1`. An empty token scan exits
1 because `rg` found no matches. The compiler and whitespace gates exit 0.

### focused-gate

```text
$ lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

### token-scan

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=1
```

### diff-check

```text
$ git diff --check

exit=0
```

### module-scan

```text
$ lake env lean /tmp/heat-duhamel-hessian-differentiation/module-scan.lean
Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.gradient_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_pos: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.gradient_eq: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.continuous_kernel_pos: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient: [propext, Classical.choice, Quot.sound]
EXACT_DEPENDENCY_SCAN declarations=21 PASS

exit=0
```

### all-dependencies

```text
$ lake env lean /tmp/heat-duhamel-hessian-differentiation/all-dependencies.lean
'Poincare.HeatDuhamelHessianDifferentiation.gradient_heatSolution_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_duhamel_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_convolution_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_heatSolution_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.norm_gradient_heatSolution_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_gradient_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_gradient_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.continuous_kernel_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.hasFDerivAt_duhamel_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### exact-target

```text
$ lake env lean /tmp/heat-duhamel-hessian-differentiation/exact-target.lean

exit=0
```

The declaration-wide scan source, appended after a copy of the module:

```lean


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "Poincare.HeatDuhamelHessianDifferentiation." && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"{n}: {axs}"
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected dependency set for {n}"
      count := count + 1
  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
```

The exact target check copies the displayed proposition directly from the
frozen task and assigns the new theorem to it. The displayed task has a final
closing parenthesis inherited from its original `#check`; the probe and the
new theorem supply the matching outer opening parenthesis. No mathematical
binder, hypothesis or conclusion is changed.

```lean


namespace FrozenTargetCheck
open Set MeasureTheory
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
example : (
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  (∀ x, u 0 x = 0) ∧
  ∀ t ∈ Icc 0 T, ∀ x : E,
    ContDiff ℝ 2 (u t) ∧
    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
    fderiv ℝ (fderiv ℝ (u t)) x =
      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2)) := Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound
end FrozenTargetCheck
```

## Proof commits

```text
$ git log --reverse --format=%h %s 0642d40ece03832420101813ecfc8224472a0552..HEAD
e3355f68 Express the spatial heat gradient as an inner-product functional
1362315a Prove parabolic dilation of the heat gradient
55790d22 Prove Bochner integrability of the gradient kernel
9c6940c3 Compute the gradient moment under dilation
75d9a599 Prove the exact inverse-square-root gradient moment
4cbbc7cc Identify the full gradient of the heat convolution
862c23cd Bound the gradient of bounded heat data by the first moment
f441f487 Prove joint continuity of the positive-time gradient kernel
9617d2ab Dilate the gradient convolution to a fixed kernel
11426648 Prove joint continuity of the Duhamel gradient integrand
aaa4ab85 Prove endpoint integrability of the gradient majorant
4922b0cf Prove time integrability of the actual heat gradient
608139da Prove joint positive-time continuity of the scalar heat kernel
5308ddc8 Prove time integrability of the Duhamel value integrand
21663729 Differentiate the Duhamel value in space under its time integral
74ed2034 Differentiate the Duhamel gradient using Hessian cancellation
4b4707fe Prove continuity of the cancelled Duhamel Hessian by domination
57f1e10e Identify the actual Duhamel Hessian with its cancelled double integral
6fe98f57 Prove spatial C2 regularity of the Duhamel solution
2807e763 Prove the frozen Duhamel Hessian bound from spatial Holder forcing

exit=0
```

## Compiler probe record

### Probe 001

```diff
--- previous-probe
+++ probe-001.lean
@@ -0,0 +1,29 @@
+import Poincare.Global.HeatDuhamelSpatialHolderHessian
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology RealInnerProductSpace Interval
+
+namespace Poincare.HeatDuhamelHessianDifferentiation
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Grad" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fun z : E => Poincare.heatKernel t z) x
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+
+/-- The spatial gradient as an inner-product functional. -/
+theorem gradient_eq {t : ℝ} (ht : t ≠ 0) (x : E) :
+    Grad t x = (heatKernel t x * (-(1 / (2 * t)))) • innerSL ℝ x := by
+  rw [(hasFDerivAt_heatKernel_spatial ht x).fderiv]
+  simp only [smul_smul, heatKernel]
+  congr 1
+  ring
+
+end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:24:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fderiv ℝ (fun z => heatKernel t z) x
in the target expression
  (fun t x => fderiv ℝ (fun z => heatKernel t z) x) t x = (heatKernel t x * -(1 / (2 * t))) • (innerSL ℝ) x

t : ℝ
ht : t ≠ 0
x : E
⊢ (fun t x => fderiv ℝ (fun z => heatKernel t z) x) t x = (heatKernel t x * -(1 / (2 * t))) • (innerSL ℝ) x

exit=1
```

### Probe 002

```diff
--- previous-probe
+++ probe-002.lean
@@ -21,7 +21,8 @@
 /-- The spatial gradient as an inner-product functional. -/
 theorem gradient_eq {t : ℝ} (ht : t ≠ 0) (x : E) :
     Grad t x = (heatKernel t x * (-(1 / (2 * t)))) • innerSL ℝ x := by
-  rw [(hasFDerivAt_heatKernel_spatial ht x).fderiv]
+  dsimp only
+  rw [(hasFDerivAt_heatKernel_spatial («E» := E) ht x).fderiv]
   simp only [smul_smul, heatKernel]
   congr 1
   ring
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-002.lean
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### Probe 003

```diff
--- previous-probe
+++ probe-003.lean
@@ -27,4 +27,15 @@
   congr 1
   ring

+/-- Parabolic dilation of the spatial gradient. -/
+theorem gradient_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    Grad (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * a⁻¹) • Grad 1 x := by
+  rw [gradient_eq (pow_ne_zero _ ha.ne'), gradient_eq one_ne_zero,
+    heatKernel_sq_smul a ha x]
+  ext v
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
+    inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
+  field_simp
+  <;> ring
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:39:6: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:39:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-003.lean
/tmp/heat-duhamel-hessian-differentiation/dep-003.lean:39:6: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/heat-duhamel-hessian-differentiation/dep-003.lean:39:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### Probe 004

```diff
--- previous-probe
+++ probe-004.lean
@@ -36,6 +36,13 @@
   simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
     inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
   field_simp
-  <;> ring
+
+/-- The gradient kernel is Bochner integrable at positive time. -/
+theorem integrable_gradient {t : ℝ} (ht : 0 < t) :
+    Integrable (Grad t) := by
+  have h := (integrable_smul_fderiv_heatKernel_sub («E» := E) ht
+    (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E)).comp_sub_left (0 : E)
+  simpa only [one_smul, sub_sub_cancel] using h

 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-004.lean
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### Probe 005

```diff
--- previous-probe
+++ probe-005.lean
@@ -45,4 +45,21 @@
     (C := 1) (by intro y; simp) (0 : E)).comp_sub_left (0 : E)
   simpa only [one_smul, sub_sub_cancel] using h

+/-- The spatial Jacobian leaves exactly one inverse length in the gradient moment. -/
+theorem gradient_integral_sq (a : ℝ) (ha : 0 < a) :
+    (∫ y : E, ‖Grad (a ^ 2) y‖) = a⁻¹ * (∫ y : E, ‖Grad 1 y‖) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Grad (a ^ 2) y‖) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ y : E, ‖Grad (a ^ 2) y‖) =
+        ∫ y : E, ‖Grad (a ^ 2) (a • y)‖ := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul]
+        using hchange.symm
+    _ = ((a ^ 3)⁻¹ * a⁻¹) * (∫ y : E, ‖Grad 1 y‖) := by
+      simp_rw [gradient_sq_smul a ha,
+        norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:61:8: error: `simp` made no progress

exit=1
```

### Probe 006

```diff
--- previous-probe
+++ probe-006.lean
@@ -48,6 +48,8 @@
 /-- The spatial Jacobian leaves exactly one inverse length in the gradient moment. -/
 theorem gradient_integral_sq (a : ℝ) (ha : 0 < a) :
     (∫ y : E, ‖Grad (a ^ 2) y‖) = a⁻¹ * (∫ y : E, ‖Grad 1 y‖) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
   have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
     (fun y : E => ‖Grad (a ^ 2) y‖) a (hR := ha.le)
   apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:63:8: error: `simp` made no progress

exit=1
```

### Probe 007

```diff
--- previous-probe
+++ probe-007.lean
@@ -59,8 +59,8 @@
       simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul]
         using hchange.symm
     _ = ((a ^ 3)⁻¹ * a⁻¹) * (∫ y : E, ‖Grad 1 y‖) := by
-      simp_rw [gradient_sq_smul a ha,
-        norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)]
+      simp_rw [gradient_sq_smul a ha]
+      trace_state
       rw [integral_const_mul]
     _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring

```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:64:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : ?m.442), ?r * ?f a ∂?m.444
in the target expression
  ∫ (y : E), ‖((a ^ 3)⁻¹ * a⁻¹) • fderiv ℝ (fun z => heatKernel 1 z) y‖ =
    (a ^ 3)⁻¹ * a⁻¹ * ∫ (y : E), ‖fderiv ℝ (fun z => heatKernel 1 z) y‖

a : ℝ
ha : 0 < a
this : NormedSpace ℝ (E →L[ℝ] ℝ) := { toModule := ContinuousLinearMap.module, norm_smul_le := ⋯ }
hchange :
  ∫ (x : E), (fun y => ‖(fun t x => fderiv ℝ (fun z => heatKernel t z) x) (a ^ 2) y‖) (a • x) =
    (a ^ Module.finrank ℝ E)⁻¹ • ∫ (x : E), (fun y => ‖(fun t x => fderiv ℝ (fun z => heatKernel t z) x) (a ^ 2) y‖) x
⊢ ∫ (y : E), ‖((a ^ 3)⁻¹ * a⁻¹) • fderiv ℝ (fun z => heatKernel 1 z) y‖ =
    (a ^ 3)⁻¹ * a⁻¹ * ∫ (y : E), ‖fderiv ℝ (fun z => heatKernel 1 z) y‖
a : ℝ
ha : 0 < a
this : NormedSpace ℝ (E →L[ℝ] ℝ) := { toModule := ContinuousLinearMap.module, norm_smul_le := ⋯ }
hchange :
  ∫ (x : E), (fun y => ‖(fun t x => fderiv ℝ (fun z => heatKernel t z) x) (a ^ 2) y‖) (a • x) =
    (a ^ Module.finrank ℝ E)⁻¹ • ∫ (x : E), (fun y => ‖(fun t x => fderiv ℝ (fun z => heatKernel t z) x) (a ^ 2) y‖) x
⊢ ∫ (y : E), ‖((a ^ 3)⁻¹ * a⁻¹) • fderiv ℝ (fun z => heatKernel 1 z) y‖ =
    (a ^ 3)⁻¹ * a⁻¹ * ∫ (y : E), ‖fderiv ℝ (fun z => heatKernel 1 z) y‖

exit=1
```

### Probe 008

```diff
--- previous-probe
+++ probe-008.lean
@@ -60,7 +60,8 @@
         using hchange.symm
     _ = ((a ^ 3)⁻¹ * a⁻¹) * (∫ y : E, ‖Grad 1 y‖) := by
       simp_rw [gradient_sq_smul a ha]
-      trace_state
+      simp_rw [norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)
+        (fderiv ℝ (fun z : E => heatKernel 1 z) _)]
       rw [integral_const_mul]
     _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring

```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-008.lean
'Poincare.HeatDuhamelHessianDifferentiation.gradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.integrable_gradient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianDifferentiation.gradient_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### Probe 009

```diff
--- previous-probe
+++ probe-009.lean
@@ -65,4 +65,12 @@
       rw [integral_const_mul]
     _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring

+/-- The exact first gradient moment has the inverse square-root time power. -/
+theorem gradient_integral {t : ℝ} (ht : 0 < t) :
+    (∫ y : E, ‖Grad t y‖) = (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+  have h := gradient_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht)
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
+  ring
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-009.lean
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

exit=0
```

### Probe 010

```diff
--- previous-probe
+++ probe-010.lean
@@ -73,4 +73,14 @@
   rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
   ring

+/-- The full gradient of bounded measurable heat data in translated coordinates. -/
+theorem gradient_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (heatSolution t f) x = ∫ y : E, f (x - y) • Grad t y := by
+  rw [(heatSolution_hasFDerivAt ht hf hM x).fderiv]
+  have hc := integral_sub_left_eq_self
+    (fun y : E => f y • Grad t (x - y)) volume x
+  simpa only [sub_sub_cancel] using hc.symm
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-010.lean
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

exit=0
```

### Probe 011

```diff
--- previous-probe
+++ probe-011.lean
@@ -83,4 +83,20 @@
     (fun y : E => f y • Grad t (x - y)) volume x
   simpa only [sub_sub_cancel] using hc.symm

+/-- The sharp gradient majorant is uniform over observation points. -/
+theorem norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    ‖fderiv ℝ (heatSolution t f) x‖ ≤
+      M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+  rw [gradient_heatSolution_eq_integral ht hf hM]
+  calc
+    ‖∫ y : E, f (x - y) • Grad t y‖ ≤ ∫ y : E, M * ‖Grad t y‖ := by
+      apply norm_integral_le_of_norm_le ((integrable_gradient ht).norm.const_mul M)
+      exact Filter.Eventually.of_forall fun y =>
+        (norm_real_smul_continuousLinearMap_one_le _ _).trans
+          (mul_le_mul_of_nonneg_right (hM (x - y)) (norm_nonneg _))
+    _ = M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+      rw [integral_const_mul, gradient_integral ht, mul_assoc]
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-011.lean
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

exit=0
```

### Probe 012

```diff
--- previous-probe
+++ probe-012.lean
@@ -99,4 +99,27 @@
     _ = M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
       rw [integral_const_mul, gradient_integral ht, mul_assoc]

+/-- Dilation gives joint continuity of the positive-time gradient kernel. -/
+theorem continuous_gradient_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => Grad p.1 p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hunit : ContDiff ℝ 0 (Grad 1) :=
+    (contDiff_heatKernel_spatial («E» := E) 1).fderiv_right (m := 0) (by norm_num)
+  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
+    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
+  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
+    Real.sqrt_pos.2 p.1.property
+  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
+      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * (Real.sqrt (p.1 : ℝ))⁻¹) •
+        Grad 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
+    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
+      (ha.inv₀ (fun p => (hapos p).ne')) |>.smul
+      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
+  apply hc.congr
+  intro p
+  have h := gradient_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
+    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
+  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-012.lean
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

exit=0
```

### Probe 013

```diff
--- previous-probe
+++ probe-013.lean
@@ -122,4 +122,23 @@
     ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
   simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm

+/-- Dilation puts the convolution gradient against a fixed unit-time kernel. -/
+theorem gradient_convolution_sq (a : ℝ) (ha : 0 < a) (f : E → ℝ) (x : E) :
+    (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
+      a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => f (x - y) • Grad (a ^ 2) y) a (hR := ha.le)
+  apply (smul_right_injective (M := E →L[ℝ] ℝ) (inv_ne_zero (pow_ne_zero 3 ha.ne')))
+  calc
+    (a ^ 3)⁻¹ • (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
+        ∫ y : E, f (x - a • y) • Grad (a ^ 2) (a • y) := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * a⁻¹) • (∫ y : E, f (x - a • y) • Grad 1 y) := by
+      simp_rw [gradient_sq_smul a ha, smul_comm (f (x - a • _))]
+      rw [integral_smul]
+    _ = (a ^ 3)⁻¹ • (a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y)) := by
+      rw [smul_smul]
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-013.lean
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

exit=0
```

### Probe 014

```diff
--- previous-probe
+++ probe-014.lean
@@ -141,4 +141,50 @@
     _ = (a ^ 3)⁻¹ • (a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y)) := by
       rw [smul_smul]

+/-- The positive elapsed-time convolution gradient is jointly continuous. -/
+theorem continuous_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) :
+    Continuous (fun p : Ioo (0 : ℝ) t × E =>
+      fderiv ℝ (heatSolution (t - p.1) (fun y => f (p.1, y))) p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have ha : Continuous (fun p : Ioo (0 : ℝ) t × E => Real.sqrt (t - p.1)) :=
+    Real.continuous_sqrt.comp (continuous_const.sub hs)
+  have hapos (p : Ioo (0 : ℝ) t × E) : 0 < Real.sqrt (t - p.1) :=
+    Real.sqrt_pos.2 (sub_pos.mpr p.1.property.2)
+  have hunit : Continuous (Grad 1) :=
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 0) (by norm_num)).continuous
+  have hn : Continuous (fun p : Ioo (0 : ℝ) t × E =>
+      ∫ y : E, f (p.1, p.2 - Real.sqrt (t - p.1) • y) • Grad 1 y) := by
+    apply continuous_of_dominated (bound := fun y : E => M * ‖Grad 1 y‖)
+    · intro p
+      exact ((hf.comp_continuous
+        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
+        (fun y => ⟨hmem p.1, mem_univ _⟩)).smul hunit).aestronglyMeasurable
+    · intro p
+      exact Filter.Eventually.of_forall fun y =>
+        (norm_real_smul_continuousLinearMap_one_le _ _).trans
+          (mul_le_mul_of_nonneg_right (hM p.1 (hmem p.1) _ ) (norm_nonneg _))
+    · exact (integrable_gradient zero_lt_one).norm.const_mul M
+    · exact Filter.Eventually.of_forall fun y =>
+        (hf.comp_continuous (hs.prodMk (continuous_snd.sub (ha.smul continuous_const)))
+          (fun p => ⟨hmem p.1, mem_univ _⟩)).smul continuous_const
+  apply ((ha.inv₀ (fun p => (hapos p).ne')).smul hn).congr
+  intro p
+  have hfc : Continuous (fun y : E => f (p.1, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem p.1, mem_univ y⟩)
+  rw [gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.2)
+    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM p.1 (hmem p.1))]
+  have h := gradient_convolution_sq (Real.sqrt (t - p.1)) (hapos p)
+    (fun y => f (p.1, y)) p.2
+  rw [Real.sq_sqrt (sub_pos.mpr p.1.property.2).le] at h
+  exact h.symm
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-014.lean
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

exit=0
```

### Probe 015

```diff
--- previous-probe
+++ probe-015.lean
@@ -187,4 +187,9 @@
   rw [Real.sq_sqrt (sub_pos.mpr p.1.property.2).le] at h
   exact h.symm

+/-- The gradient time majorant is integrable through the endpoint. -/
+theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
+    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
+  simpa using intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:193:2: error: Type mismatch: After simplification, term
  intervalIntegrable_hessian_majorant zero_lt_one t A
 has type
  IntervalIntegrable (fun s => A * (t - s) ^ (2⁻¹ - 1)) volume 0 t
but is expected to have type
  IntervalIntegrable (fun s => A * (t - s) ^ (-2⁻¹)) volume 0 t

exit=1
```

### Probe 016

```diff
--- previous-probe
+++ probe-016.lean
@@ -192,4 +192,26 @@
     IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
   simpa using intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A

+/-- The actual first spatial derivative is integrable in Duhamel time. -/
+theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    IntervalIntegrable
+      (fun s : ℝ => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) volume 0 t := by
+  have hc := (continuous_gradient_heatSolution_time ht hf hM).comp
+    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
+  let A := M * (∫ y : E, ‖Grad 1 y‖)
+  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+    (intervalIntegrable_gradient_majorant t A)
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
+    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
+  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
+  have hmem : (s : ℝ) ∈ Icc 0 T := ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hfc : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem, mem_univ y⟩)
+  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
+    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:193:2: error: Type mismatch: After simplification, term
  intervalIntegrable_hessian_majorant zero_lt_one t A
 has type
  IntervalIntegrable (fun s => A * (t - s) ^ (2⁻¹ - 1)) volume 0 t
but is expected to have type
  IntervalIntegrable (fun s => A * (t - s) ^ (-2⁻¹)) volume 0 t

exit=1
```

### Probe 017

```diff
--- previous-probe
+++ probe-017.lean
@@ -190,28 +190,6 @@
 /-- The gradient time majorant is integrable through the endpoint. -/
 theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
     IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
-  simpa using intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A
-
-/-- The actual first spatial derivative is integrable in Duhamel time. -/
-theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
-    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
-    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
-    IntervalIntegrable
-      (fun s : ℝ => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) volume 0 t := by
-  have hc := (continuous_gradient_heatSolution_time ht hf hM).comp
-    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
-  let A := M * (∫ y : E, ‖Grad 1 y‖)
-  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
-    (intervalIntegrable_gradient_majorant t A)
-  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
-    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
-  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
-  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
-  have hmem : (s : ℝ) ∈ Icc 0 T := ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
-  have hfc : Continuous (fun y : E => f (s, y)) :=
-    hf.comp_continuous (continuous_const.prodMk continuous_id)
-      (fun y => ⟨hmem, mem_univ y⟩)
-  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
-    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x
+  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1 <;> norm_num

 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:193:79: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-017.lean
/tmp/heat-duhamel-hessian-differentiation/dep-017.lean:193:79: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
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

exit=0
```

### Probe 018

```diff
--- previous-probe
+++ probe-018.lean
@@ -190,6 +190,30 @@
 /-- The gradient time majorant is integrable through the endpoint. -/
 theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
     IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
-  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1 <;> norm_num
+  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1
+  norm_num
+
+/-- The actual first spatial derivative is integrable in Duhamel time. -/
+theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    IntervalIntegrable
+      (fun s : ℝ => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) volume 0 t := by
+  have hc := (continuous_gradient_heatSolution_time ht hf hM).comp
+    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
+  let A := M * (∫ y : E, ‖Grad 1 y‖)
+  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+    (intervalIntegrable_gradient_majorant t A)
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
+    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
+  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
+  have hmem : (s : ℝ) ∈ Icc 0 T := ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hfc : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem, mem_univ y⟩)
+  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
+    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x
+

 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-018.lean
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

exit=0
```

### Probe 019

```diff
--- previous-probe
+++ probe-019.lean
@@ -216,4 +216,11 @@
     hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x


+/-- The heat kernel is jointly continuous away from zero time. -/
+theorem continuous_kernel_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => heatKernel (p.1 : ℝ) p.2) := by
+  have ht (p : Ioi (0 : ℝ) × E) : 0 < (p.1 : ℝ) := p.1.property
+  unfold heatKernel
+  fun_prop (disch := positivity)
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:224:2: error: `fun_prop` was unable to prove `Continuous fun p => (4 * Real.pi * ↑p.1) ^ (-↑(Module.finrank ℝ E) / 2) * Real.exp (-‖p.2‖ ^ 2 / (4 * ↑p.1))`

Issues:
  Failed to prove necessary assumption `0 ≤ -↑(Module.finrank ℝ E) / 2` when applying theorem `Real.continuous_rpow_const`.

exit=1
```

### Probe 020

```diff
--- previous-probe
+++ probe-020.lean
@@ -221,6 +221,11 @@
     Continuous (fun p : Ioi (0 : ℝ) × E => heatKernel (p.1 : ℝ) p.2) := by
   have ht (p : Ioi (0 : ℝ) × E) : 0 < (p.1 : ℝ) := p.1.property
   unfold heatKernel
-  fun_prop (disch := positivity)
+  apply Continuous.mul
+  · apply Continuous.rpow_const (by fun_prop)
+    intro p
+    left
+    positivity
+  · fun_prop (disch := positivity)

 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:228:4: error: failed to prove positivity/nonnegativity/nonzeroness
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:229:4: error: `fun_prop` was unable to prove `Continuous fun p => Real.exp (-‖p.2‖ ^ 2 / (4 * ↑p.1))`

Issues:
  Failed to prove necessary assumption `∀ (x : ℝ × ℝ), x.2 ≠ 0` when applying theorem `Continuous.div₀`.
  Failed to prove necessary assumption `∀ (x : ↑(Ioi 0) × E), 4 * ↑x.1 ≠ 0` when applying theorem `Continuous.div₀`.

exit=1
```

### Probe 021

```diff
--- previous-probe
+++ probe-021.lean
@@ -225,7 +225,10 @@
   · apply Continuous.rpow_const (by fun_prop)
     intro p
     left
-    positivity
-  · fun_prop (disch := positivity)
+    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht p).ne'
+  · apply Continuous.rexp
+    apply Continuous.div (by fun_prop) (by fun_prop)
+    intro p
+    exact mul_ne_zero (by norm_num) (ht p).ne'

 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-021.lean
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

exit=0
```

### Probe 022

```diff
--- previous-probe
+++ probe-022.lean
@@ -231,4 +231,40 @@
     intro p
     exact mul_ne_zero (by norm_num) (ht p).ne'

+/-- Bounded cylinder data give a genuine time integral for the heat evolution. -/
+theorem intervalIntegrable_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    IntervalIntegrable
+      (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x) volume 0 t := by
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have hfc : Continuous (fun p : Ioo (0 : ℝ) t × E => f (p.1, x - p.2)) :=
+    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hk : Continuous (fun p : Ioo (0 : ℝ) t × E => heatKernel (t - p.1) p.2) :=
+    continuous_kernel_pos.comp
+      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
+        continuous_snd)
+  have hm := (hk.mul hfc).stronglyMeasurable.integral_prod_right' (ν := volume)
+  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 t)
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
+    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
+  refine hi.mono' (by simpa only [heatSolution_apply] using hm.aestronglyMeasurable)
+    (Filter.Eventually.of_forall fun s => ?_)
+  have hpos := sub_pos.mpr s.property.2
+  rw [heatSolution_apply]
+  calc
+    ‖∫ y : E, heatKernel (t - s) y * f (s, x - y)‖ ≤
+        ∫ y : E, M * heatKernel (t - s) y := by
+      apply norm_integral_le_of_norm_le ((heatKernel_integrable («E» := E) hpos).const_mul M)
+      refine Filter.Eventually.of_forall fun y => ?_
+      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hpos y), mul_comm]
+      exact mul_le_mul_of_nonneg_right (hM s (hmem s) _) (heatKernel_nonneg hpos y)
+    _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:260:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  heatSolution ?t ?f ?x
in the target expression
  ‖((fun s => heatSolution (t - s) (fun y => f (s, y)) x) ∘ Subtype.val) s‖ ≤ ((fun x => M) ∘ Subtype.val) s

T t M : ℝ
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
x : E
hmem : ∀ (s : ↑(Ioo 0 t)), ↑s ∈ Icc 0 T
hs : Continuous fun p => ↑p.1
hfc : Continuous fun p => f (↑p.1, x - p.2)
hk : Continuous fun p => heatKernel (t - ↑p.1) p.2
hm :
  StronglyMeasurable fun x_1 => ∫ (y : E), ((fun p => heatKernel (t - ↑p.1) p.2) * fun p => f (↑p.1, x - p.2)) (x_1, y)
hi : Integrable ((fun x => M) ∘ Subtype.val) (Measure.comap Subtype.val volume)
s : ↑(Ioo 0 t)
hpos : 0 < t - ↑s
⊢ ‖((fun s => heatSolution (t - s) (fun y => f (s, y)) x) ∘ Subtype.val) s‖ ≤ ((fun x => M) ∘ Subtype.val) s

exit=1
```

### Probe 023

```diff
--- previous-probe
+++ probe-023.lean
@@ -257,6 +257,7 @@
   refine hi.mono' (by simpa only [heatSolution_apply] using hm.aestronglyMeasurable)
     (Filter.Eventually.of_forall fun s => ?_)
   have hpos := sub_pos.mpr s.property.2
+  dsimp only [Function.comp_apply]
   rw [heatSolution_apply]
   calc
     ‖∫ y : E, heatKernel (t - s) y * f (s, x - y)‖ ≤
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-023.lean
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

exit=0
```

### Probe 024

```diff
--- previous-probe
+++ probe-024.lean
@@ -268,4 +268,36 @@
       exact mul_le_mul_of_nonneg_right (hM s (hmem s) _) (heatKernel_nonneg hpos y)
     _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]

+/-- First spatial differentiation under the Duhamel time integral. -/
+theorem hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z)
+      (∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) x := by
+  let A := M * (∫ y : E, ‖Grad 1 y‖)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem s hs, mem_univ y⟩)
+  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
+    (F' := fun z s => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
+    (s := univ) (bound := fun s => A * (t - s) ^ (-(1 / 2 : ℝ))) (by simp)
+  · exact Filter.Eventually.of_forall fun z => by
+      simpa only [uIoc_of_le ht.1] using
+        (intervalIntegrable_heatSolution_time ht hf hM z).aestronglyMeasurable
+  · exact intervalIntegrable_heatSolution_time ht hf hM x
+  · simpa only [uIoc_of_le ht.1] using
+      (intervalIntegrable_gradient_heatSolution_time ht hf hM x).aestronglyMeasurable
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z
+  · exact intervalIntegrable_gradient_majorant t A
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact (heatSolution_hasFDerivAt (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z).differentiableAt.hasFDerivAt
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-024.lean
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

exit=0
```

### Probe 025

```diff
--- previous-probe
+++ probe-025.lean
@@ -300,4 +300,49 @@
     exact (heatSolution_hasFDerivAt (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
       (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z).differentiableAt.hasFDerivAt

+/-- Second spatial differentiation uses the integrable cancelled Hessian. -/
+theorem hasFDerivAt_duhamel_gradient {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
+      fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
+      (∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) x := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem s hs, mem_univ y⟩)
+  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
+    (F' := fun z s => ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)
+    (s := univ) (bound := fun s => A * (t - s) ^ (α / 2 - 1)) (by simp)
+  · exact Filter.Eventually.of_forall fun z => by
+      simpa only [uIoc_of_le ht.1] using
+        (intervalIntegrable_gradient_heatSolution_time ht hf hM z).aestronglyMeasurable
+  · exact intervalIntegrable_gradient_heatSolution_time ht hf hM x
+  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
+      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x)
+    simpa only [uIoc_of_le ht.1] using hi.aestronglyMeasurable
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s (hmem s hs)) z
+  · exact intervalIntegrable_hessian_majorant hα t A
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
+      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
+    have htwo := contDiff_two_heatSolution_of_bounded_measurable
+      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs
+    have hd := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
+      (by norm_num) z).hasFDerivAt
+    rw [hessian_heatSolution_eq_cancelled_integral
+      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
+    exact hd
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-025.lean
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

exit=0
```

### Probe 026

```diff
--- previous-probe
+++ probe-026.lean
@@ -345,4 +345,40 @@
       (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
     exact hd

+/-- The cancelled time-integrated Hessian is continuous in the observation point. -/
+theorem continuous_duhamel_hessian {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
+    Continuous (fun x : E => ∫ s in (0 : ℝ)..t, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  simp_rw [intervalIntegral.integral_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+  apply continuous_of_dominated (bound := fun s : ℝ => A * (t - s) ^ (α / 2 - 1))
+  · intro x
+    exact (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).aestronglyMeasurable
+  · intro x
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s (hmem s hs)) x
+  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    have hfc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hmem s hs, mem_univ y⟩)
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
+      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
+    have htwo := contDiff_two_heatSolution_of_bounded_measurable
+      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs
+    have hc := ((htwo.fderiv_right (m := 1) (by norm_num)).fderiv_right
+      (m := 0) (by norm_num)).continuous
+    exact hc.congr (fun x => hessian_heatSolution_eq_cancelled_integral
+      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs x)
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-026.lean
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

exit=0
```

### Probe 027

```diff
--- previous-probe
+++ probe-027.lean
@@ -381,4 +381,18 @@
     exact hc.congr (fun x => hessian_heatSolution_eq_cancelled_integral
       (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs x)

+/-- The actual second derivative equals the cancelled double integral. -/
+theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    fderiv ℝ (fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z)) x =
+      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y := by
+  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
+  rw [hD]
+  exact (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x).fderiv
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-027.lean
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

exit=0
```

### Probe 028

```diff
--- previous-probe
+++ probe-028.lean
@@ -395,4 +395,23 @@
   rw [hD]
   exact (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x).fderiv

+/-- Spatial C² regularity of the Duhamel formula under the frozen forcing hypotheses. -/
+theorem contDiff_two_duhamel {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
+    ContDiff ℝ 2 (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z) := by
+  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
+  have hDD := funext (fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).fderiv)
+  change ContDiff ℝ (1 + 1) _
+  refine contDiff_succ_iff_fderiv.mpr
+    ⟨fun z => (hasFDerivAt_duhamel ht hf hM z).differentiableAt, by norm_num, ?_⟩
+  rw [hD]
+  apply contDiff_one_iff_fderiv.mpr
+  refine ⟨fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).differentiableAt, ?_⟩
+  rw [hDD]
+  exact continuous_duhamel_hessian hα hα1 ht hf hM hK
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-028.lean
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

exit=0
```

### Probe 029

```diff
--- previous-probe
+++ probe-029.lean
@@ -414,4 +414,45 @@
   rw [hDD]
   exact continuous_duhamel_hessian hα hα1 ht hf hM hK

+/-- The frozen spatial Hölder Duhamel Hessian estimate. -/
+theorem duhamel_hessian_bound :
+  (∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  (∀ x, u 0 x = 0) ∧
+  ∀ t ∈ Icc 0 T, ∀ x : E,
+    ContDiff ℝ 2 (u t) ∧
+    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
+    fderiv ℝ (fderiv ℝ (u t)) x =
+      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
+    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2)) := by
+  intro α hα hα1
+  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
+  refine ⟨max 1 (J * (2 / α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro T _ _ f M K _ hK0 hf hM hK
+  dsimp only
+  refine ⟨?_, ?_⟩
+  · intro x
+    exact intervalIntegral.integral_same
+  · intro t ht x
+    refine ⟨contDiff_two_duhamel hα hα1 ht hf hM hK,
+      integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
+      hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, ?_⟩
+    rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x]
+    calc
+      ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+          (K * J) * (2 / α) * t ^ (α / 2) :=
+        norm_integral_cancelled_hessian_time_le hα hα1 ht.1
+          (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x
+      _ = (J * (2 / α)) * K * t ^ (α / 2) := by ring
+      _ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2) :=
+        mul_le_mul_of_nonneg_right
+          (mul_le_mul_of_nonneg_right (le_max_right _ _) hK0)
+          (Real.rpow_nonneg ht.1 _)
+
 end Poincare.HeatDuhamelHessianDifferentiation
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianDifferentiation.lean

exit=0
```

Dependency probe used the same source followed by `#print axioms` for each theorem declared so far.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-hessian-differentiation/dep-029.lean
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

exit=0
```

## Source-name verification

The combined grep found all 140 searched source identifiers, including the
exact interval differentiation and continuity APIs used by the proof.

```text
$ rg -n --glob *.lean <combined source identifiers> Poincare .lake/packages/mathlib/Mathlib
exit=0
First actual source match for each name:
AEStronglyMeasurable
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyMaximumDifferentialDecay.lean:80:    (hMeasurable : AEStronglyMeasurable
ClosedSmoothModel
Poincare/Global/CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction.lean:31:local notation "E" => ClosedSmoothModel 3
ContDiff
Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:20:open scoped Manifold ContDiff
Continuous
Poincare/Global/CartanRootedOverlapReparameterizedBoundary.lean:110:    Continuous (boundaryReparameterization endpoint x N) :=
ContinuousOn
Poincare/Global/DeTurckFlowVariationalIdentification.lean:156:  have hbaseContOn : ContinuousOn (alpha z₀) (Icc (-ε) ε) :=
HasFDerivAt
Poincare/Global/DeTurckFlowVariationalIdentification.lean:48:    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
Integrable
Poincare/Global/HeatCauchyUniform.lean:42:    Integrable (fun y : E => heatKernelUniformTranslateEnvelope (E := E) t A y) := by
IntegrableOn
Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:283:    (hIntegrable : IntegrableOn D (Ici (0 : ℝ))) :
IntervalIntegrable
Poincare/Global/HeatSemigroupBUCGeneratorCore.lean:54:  have hint : IntervalIntegrable orbit volume (0 : ℝ) (ε : ℝ) :=
NormedAddCommGroup
Poincare/CurvatureConditions.lean:17:variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
NormedSpace
Poincare/CurvatureConditions.lean:17:variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
ae_restrict_mem
Poincare/Global/NormalizedFlowAbsoluteDissipationDecay.lean:49:  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
aestronglyMeasurable
Poincare/Global/HeatEnvelopes.lean:98:    exact ((continuous_const.add hnormsq).mul hexp).aestronglyMeasurable
aestronglyMeasurable_const
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:44:    (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
comp_apply
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:376:      simp only [Function.comp_apply, ι_def]
comp_continuous
Poincare/Global/DeTurckFlowVariationalIdentification.lean:165:      hbaseContOn.comp_continuous hclamp
comp_sub_left
Poincare/Global/HeatEnvelopes.lean:106:  exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) ha).comp_sub_left x
conj_trivial
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:37:    inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
const_mul
Poincare/CurvatureConditions.lean:328:        ((hasDerivAt_id t₀).const_mul (2 * lam * (g₀ x (Z x) w)))
contDiff_heatKernel_spatial
Poincare/Global/HeatEnvelopes.lean:164:      (contDiff_heatKernel_spatial (E := E) s).continuous.comp hsub
contDiff_one_iff_fderiv
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:412:  apply contDiff_one_iff_fderiv.mpr
contDiff_succ_iff_fderiv
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:409:  refine contDiff_succ_iff_fderiv.mpr
contDiff_two_duhamel
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:399:theorem contDiff_two_duhamel {α T t M K : ℝ}
contDiff_two_heatSolution_of_bounded_measurable
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:42:  have htwo := contDiff_two_heatSolution_of_bounded_measurable ht hf hM
continuous
Poincare/ProofProgress/OnePointTwoPointComplementTopology.lean:25:  exact e.symm.surjective.pathConnectedSpace e.symm.continuous
continuous_const
Poincare/CurvatureConditions.lean:612:        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
continuous_duhamel_hessian
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:349:theorem continuous_duhamel_hessian {α T t M K : ℝ}
continuous_fst
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:161:        continuous_fst).rexp)).comp continuous_id)
continuous_gradient_heatSolution_time
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:145:theorem continuous_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
continuous_gradient_pos
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:103:theorem continuous_gradient_pos :
continuous_id
Poincare/CurvatureConditions.lean:612:        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
continuous_kernel_pos
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:220:theorem continuous_kernel_pos :
continuous_of_dominated
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:165:    apply continuous_of_dominated (bound := fun y : E => M * ‖Grad 1 y‖)
continuous_snd
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:220:    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
continuous_sqrt
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:186:    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
continuous_subtype_val
Poincare/Global/DeTurckFlowVariationalIdentification.lean:162:    exact continuous_subtype_val.comp continuous_projIcc
differentiableAt
Poincare/ModelChristoffel.lean:76:      fderiv_comp x L.differentiableAt hGd, L.fderiv]
div
.lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Basic.lean:335:@[simps -isSimp, simps!] instance : Div (QuadraticAlgebra K a b) where div w z := w * z⁻¹
duhamel_hessian_bound
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:418:theorem duhamel_hessian_bound :
fderiv
Poincare/ModelChristoffel.lean:35:    ((fderiv ℝ G x u) v w + (fderiv ℝ G x v) u w - (fderiv ℝ G x w) u v)
fderiv_right
Poincare/ModelChristoffel.lean:383:  have hdf := hGc.fderiv_right (m := k) le_rfl
field_simp
.lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:87:  field_simp
filter_upwards
Poincare/CurvatureConditions.lean:99:    filter_upwards [interior_mem_nhds.mpr hv'] with y hy
finrank_euclideanSpace_fin
Poincare/TopologyExtraction.lean:28:  rw [finrank_euclideanSpace_fin]
fun_prop
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:491:@[continuity, fun_prop]
gradient_convolution_sq
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:126:theorem gradient_convolution_sq (a : ℝ) (ha : 0 < a) (f : E → ℝ) (x : E) :
gradient_eq
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:22:theorem gradient_eq {t : ℝ} (ht : t ≠ 0) (x : E) :
gradient_heatSolution_eq_integral
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:77:theorem gradient_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
gradient_integral
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:69:theorem gradient_integral {t : ℝ} (ht : 0 < t) :
gradient_integral_sq
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:49:theorem gradient_integral_sq (a : ℝ) (ha : 0 < a) :
gradient_sq_smul
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:31:theorem gradient_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
hasFDerivAt_duhamel
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:272:theorem hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Icc 0 T)
hasFDerivAt_duhamel_gradient
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:304:theorem hasFDerivAt_duhamel_gradient {α T t M K : ℝ}
hasFDerivAt_heatKernel_spatial
Poincare/Global/HeatCauchyUniform.lean:326:    rw [(hasFDerivAt_heatKernel_spatial (E := E) ht.ne' u).fderiv]
hasFDerivAt_integral_of_dominated_of_fderiv_le''
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:284:  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
heatKernel
Poincare/Global/HeatCauchyFrechet.lean:9:derivative integrand for `x ↦ heatKernel t (x - y) * c` is dominated, in
heatKernel_integrable
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:183:    (heatKernel_integrable (E := E) ht).const_mul ‖f‖
heatKernel_nonneg
Poincare/Global/HeatCauchyFrechet.lean:57:  have hk_nonneg : 0 ≤ hk := heatKernel_nonneg (E := E) ht (x - y)
heatKernel_sq_smul
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:299:    heatKernel_sq_smul (E := E) a ha x, norm_smul,
heatSolution
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:40:    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
heatSolution_apply
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:257:  refine hi.mono' (by simpa only [heatSolution_apply] using hm.aestronglyMeasurable)
heatSolution_hasFDerivAt
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:81:  rw [(heatSolution_hasFDerivAt ht hf hM x).fderiv]
hessian_duhamel_eq_integral
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:385:theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
hessian_heatSolution_eq_cancelled_integral
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:81:theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
innerSL
Poincare/Global/HeatCauchyFrechet.lean:29:  (c * heatKernel (E := E) t (x - y) * (-(1 / (2 * t)))) • innerSL ℝ (x - y)
innerSL_apply_apply
Poincare/Global/HeatCauchyFrechet.lean:75:    simpa only [innerSL_apply_apply, Real.norm_eq_abs] using abs_real_inner_le_norm (x - y) v
inner_smul_left
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:213:    simp only [inner_smul_left, e.repr_apply_apply, smul_smul,
integrableOn_cancelled_hessian_time
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:202:theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
integrableOn_iff_comap_subtypeVal
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:230:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
integrable_gradient
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:41:theorem integrable_gradient {t : ℝ} (ht : 0 < t) :
integrable_smul_fderiv_heatKernel_sub
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:43:  have h := (integrable_smul_fderiv_heatKernel_sub («E» := E) ht
integral_comp_smul_of_nonneg
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:320:  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
integral_const_mul
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:336:    rw [integral_const_mul]
integral_heatKernel_eq_one
Poincare/Global/HeatKernelSemigroup.lean:93:    exact integral_heatKernel_eq_one (E := E) hr
integral_of_le
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:201:          intervalIntegral.integral_of_le hn
integral_prod_right'
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:225:  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
integral_same
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:441:    exact intervalIntegral.integral_same
integral_smul
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:93:    hc, integral_smul,
integral_sub_left_eq_self
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:68:  have hc := integral_sub_left_eq_self
intervalIntegrable_const
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:84:        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := (1 : ℝ)))
intervalIntegrable_gradient_heatSolution_time
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:197:theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
intervalIntegrable_gradient_majorant
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:191:theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
intervalIntegrable_heatSolution_time
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:235:theorem intervalIntegrable_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
intervalIntegrable_hessian_majorant
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:158:theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
intervalIntegrable_iff_integrableOn_Ioo_of_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:228:    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
inv_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/NeZero.lean:48:theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
inv₀
Poincare/Global/HamiltonChartDensityLocalDomination.lean:74:      ((continuous_id.matrix_det.continuousAt.comp hG).inv₀ hdet).smul
le_max_left
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:111:      (N' : K) ≤ (N : K) := by exact_mod_cast le_max_left _ _
le_max_right
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:113:      _ ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
lt_of_lt_of_le
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/EraseLead.lean:162:    simpa using (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le pq degree_le_natDegree)).symm
measurableSet_Ioo
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:230:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
mem_univ
Poincare/ProofProgress/OnePointTwoPointComplementTopology.lean:67:    exact Set.mem_univ z
mul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:44:   It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
mul_assoc
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:131:  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
mul_comm
.lake/packages/mathlib/Mathlib/Algebra/Squarefree/Basic.lean:197:  rw [mul_comm] at h
mul_le_mul_of_nonneg_right
Poincare/Global/HeatCauchyFrechet.lean:72:    exact mul_le_mul_of_nonneg_right
mul_left_cancel
.lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:69:  apply mul_left_cancel₀ ha
mul_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:68:  have ha : 2 * 2 * a ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne _) (NeZero.ne _)) ha
mul_one
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:133:  | mul_one {a : Pre R X} : Rel (a * 1) a
norm_cancelled_hessian_integral_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:124:theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
norm_eq_abs
Poincare/Global/HeatCauchyFrechet.lean:75:    simpa only [innerSL_apply_apply, Real.norm_eq_abs] using abs_real_inner_le_norm (x - y) v
norm_gradient_heatSolution_le
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:87:theorem norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
norm_integral_cancelled_hessian_time_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:236:theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
norm_integral_le_of_norm_le
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:274:    MeasureTheory.norm_integral_le_of_norm_le hbound
norm_mul
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_nonneg
Poincare/Global/HeatCauchyFrechet.lean:56:  have hC_nonneg : 0 ≤ C := (norm_nonneg c).trans hc
norm_num
Poincare/CurvatureConditions.lean:98:      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
norm_of_nonneg
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_real_smul_continuousLinearMap_one_le
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:52:    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
norm_real_smul_continuousLinearMap_two_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:32:        norm_real_smul_continuousLinearMap_two_le _ _
norm_smul_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:87:    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
norm_smul_of_nonneg
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:63:      simp_rw [norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)
of_forall
Poincare/ModelChristoffel.lean:510:  exact hgoal.congr_of_eventuallyEq (Filter.Eventually.of_forall
one_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:508:        one_ne_zero <| hfy1.symm.trans hfy0
one_smul
.lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Defs.lean:260:  one_smul _ := by ext <;> simp
pi_ne_zero
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:228:    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht p).ne'
pow_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/Prime/Lemmas.lean:89:    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ, mul_left_comm]
prodMk
Poincare/Global/DeTurckFlowVariationalIdentification.lean:38:    contDiff_fst.prodMk contDiff_snd
restrict_Ioo_eq_restrict_Ioc
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:253:  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
rpow_const
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:225:  · apply Continuous.rpow_const (by fun_prop)
rpow_neg
.lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:279:      Equiv.smulRight_apply, Real.rpow_neg hc₁, Set.smul_mem_smul_set_iff₀ aux₃,
rpow_nonneg
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:585:        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)
set_option
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:315:set_option backward.privateInPublic true in
simp_rw
.lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:106:  simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
smul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:179:  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ ↦ Rel.mul_compat_right
smul_apply
Poincare/CurvatureConditions.lean:61:        LinearMap.smul_apply, smul_eq_mul]
smul_comm
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:294:  smul_comm r s x := smul_comm (algebraMap R A r) (algebraMap S A s) x
smul_eq_mul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:289:    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
smul_inv_smul
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Pointwise/Set.lean:168:  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩
smul_right_injective
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Tower.lean:398:  smul_right_injective M hx
smul_smul
Poincare/Global/FixedChartUniformJacobiComparison.lean:335:  · simpa [hΦ0, smul_smul, C.T_pos.ne'] using hscaled
sq_sqrt
Poincare/Global/SpeedPackage.lean:60:  exact Real.sq_sqrt
sqrt_eq_rpow
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:73:  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
sqrt_pos
Poincare/Global/HausdorffInverseChartLocalFrozenBilipschitz.lean:93:    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
stronglyMeasurable
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:225:  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
sub_pos
Poincare/Global/HausdorffInverseChartLocalFrozenBilipschitz.lean:93:    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
sub_sub_cancel
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:70:  simpa only [sub_sub_cancel] using hc.symm
subtype_mk
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:874:theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
uIoc_of_le
Poincare/Global/DuhamelLocalContraction.lean:65:      simpa [Set.uIoc_of_le t.property.1] using hs
zero_lt_one
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/EraseLead.lean:83:    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm
```

## Final proof diff

```diff
$ git diff 0642d40ece03832420101813ecfc8224472a0552 -- Poincare/Global/HeatDuhamelHessianDifferentiation.lean
diff --git a/Poincare/Global/HeatDuhamelHessianDifferentiation.lean b/Poincare/Global/HeatDuhamelHessianDifferentiation.lean
new file mode 100644
index 00000000..c46fb082
--- /dev/null
+++ b/Poincare/Global/HeatDuhamelHessianDifferentiation.lean
@@ -0,0 +1,458 @@
+import Poincare.Global.HeatDuhamelSpatialHolderHessian
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology RealInnerProductSpace Interval
+
+namespace Poincare.HeatDuhamelHessianDifferentiation
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Grad" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fun z : E => Poincare.heatKernel t z) x
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+
+/-- The spatial gradient as an inner-product functional. -/
+theorem gradient_eq {t : ℝ} (ht : t ≠ 0) (x : E) :
+    Grad t x = (heatKernel t x * (-(1 / (2 * t)))) • innerSL ℝ x := by
+  dsimp only
+  rw [(hasFDerivAt_heatKernel_spatial («E» := E) ht x).fderiv]
+  simp only [smul_smul, heatKernel]
+  congr 1
+  ring
+
+/-- Parabolic dilation of the spatial gradient. -/
+theorem gradient_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    Grad (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * a⁻¹) • Grad 1 x := by
+  rw [gradient_eq (pow_ne_zero _ ha.ne'), gradient_eq one_ne_zero,
+    heatKernel_sq_smul a ha x]
+  ext v
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
+    inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
+  field_simp
+
+/-- The gradient kernel is Bochner integrable at positive time. -/
+theorem integrable_gradient {t : ℝ} (ht : 0 < t) :
+    Integrable (Grad t) := by
+  have h := (integrable_smul_fderiv_heatKernel_sub («E» := E) ht
+    (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E)).comp_sub_left (0 : E)
+  simpa only [one_smul, sub_sub_cancel] using h
+
+/-- The spatial Jacobian leaves exactly one inverse length in the gradient moment. -/
+theorem gradient_integral_sq (a : ℝ) (ha : 0 < a) :
+    (∫ y : E, ‖Grad (a ^ 2) y‖) = a⁻¹ * (∫ y : E, ‖Grad 1 y‖) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Grad (a ^ 2) y‖) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ y : E, ‖Grad (a ^ 2) y‖) =
+        ∫ y : E, ‖Grad (a ^ 2) (a • y)‖ := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul]
+        using hchange.symm
+    _ = ((a ^ 3)⁻¹ * a⁻¹) * (∫ y : E, ‖Grad 1 y‖) := by
+      simp_rw [gradient_sq_smul a ha]
+      simp_rw [norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)
+        (fderiv ℝ (fun z : E => heatKernel 1 z) _)]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (a⁻¹ * (∫ y : E, ‖Grad 1 y‖)) := by ring
+
+/-- The exact first gradient moment has the inverse square-root time power. -/
+theorem gradient_integral {t : ℝ} (ht : 0 < t) :
+    (∫ y : E, ‖Grad t y‖) = (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+  have h := gradient_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht)
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
+  ring
+
+/-- The full gradient of bounded measurable heat data in translated coordinates. -/
+theorem gradient_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (heatSolution t f) x = ∫ y : E, f (x - y) • Grad t y := by
+  rw [(heatSolution_hasFDerivAt ht hf hM x).fderiv]
+  have hc := integral_sub_left_eq_self
+    (fun y : E => f y • Grad t (x - y)) volume x
+  simpa only [sub_sub_cancel] using hc.symm
+
+/-- The sharp gradient majorant is uniform over observation points. -/
+theorem norm_gradient_heatSolution_le {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    ‖fderiv ℝ (heatSolution t f) x‖ ≤
+      M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+  rw [gradient_heatSolution_eq_integral ht hf hM]
+  calc
+    ‖∫ y : E, f (x - y) • Grad t y‖ ≤ ∫ y : E, M * ‖Grad t y‖ := by
+      apply norm_integral_le_of_norm_le ((integrable_gradient ht).norm.const_mul M)
+      exact Filter.Eventually.of_forall fun y =>
+        (norm_real_smul_continuousLinearMap_one_le _ _).trans
+          (mul_le_mul_of_nonneg_right (hM (x - y)) (norm_nonneg _))
+    _ = M * (∫ y : E, ‖Grad 1 y‖) * t ^ (-(1 / 2 : ℝ)) := by
+      rw [integral_const_mul, gradient_integral ht, mul_assoc]
+
+/-- Dilation gives joint continuity of the positive-time gradient kernel. -/
+theorem continuous_gradient_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => Grad p.1 p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hunit : ContDiff ℝ 0 (Grad 1) :=
+    (contDiff_heatKernel_spatial («E» := E) 1).fderiv_right (m := 0) (by norm_num)
+  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
+    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
+  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
+    Real.sqrt_pos.2 p.1.property
+  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
+      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * (Real.sqrt (p.1 : ℝ))⁻¹) •
+        Grad 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
+    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
+      (ha.inv₀ (fun p => (hapos p).ne')) |>.smul
+      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
+  apply hc.congr
+  intro p
+  have h := gradient_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
+    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
+  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
+
+/-- Dilation puts the convolution gradient against a fixed unit-time kernel. -/
+theorem gradient_convolution_sq (a : ℝ) (ha : 0 < a) (f : E → ℝ) (x : E) :
+    (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
+      a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => f (x - y) • Grad (a ^ 2) y) a (hR := ha.le)
+  apply (smul_right_injective (M := E →L[ℝ] ℝ) (inv_ne_zero (pow_ne_zero 3 ha.ne')))
+  calc
+    (a ^ 3)⁻¹ • (∫ y : E, f (x - y) • Grad (a ^ 2) y) =
+        ∫ y : E, f (x - a • y) • Grad (a ^ 2) (a • y) := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * a⁻¹) • (∫ y : E, f (x - a • y) • Grad 1 y) := by
+      simp_rw [gradient_sq_smul a ha, smul_comm (f (x - a • _))]
+      rw [integral_smul]
+    _ = (a ^ 3)⁻¹ • (a⁻¹ • (∫ y : E, f (x - a • y) • Grad 1 y)) := by
+      rw [smul_smul]
+
+/-- The positive elapsed-time convolution gradient is jointly continuous. -/
+theorem continuous_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) :
+    Continuous (fun p : Ioo (0 : ℝ) t × E =>
+      fderiv ℝ (heatSolution (t - p.1) (fun y => f (p.1, y))) p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_one_le }
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have ha : Continuous (fun p : Ioo (0 : ℝ) t × E => Real.sqrt (t - p.1)) :=
+    Real.continuous_sqrt.comp (continuous_const.sub hs)
+  have hapos (p : Ioo (0 : ℝ) t × E) : 0 < Real.sqrt (t - p.1) :=
+    Real.sqrt_pos.2 (sub_pos.mpr p.1.property.2)
+  have hunit : Continuous (Grad 1) :=
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 0) (by norm_num)).continuous
+  have hn : Continuous (fun p : Ioo (0 : ℝ) t × E =>
+      ∫ y : E, f (p.1, p.2 - Real.sqrt (t - p.1) • y) • Grad 1 y) := by
+    apply continuous_of_dominated (bound := fun y : E => M * ‖Grad 1 y‖)
+    · intro p
+      exact ((hf.comp_continuous
+        (continuous_const.prodMk (continuous_const.sub (continuous_const.smul continuous_id)))
+        (fun y => ⟨hmem p.1, mem_univ _⟩)).smul hunit).aestronglyMeasurable
+    · intro p
+      exact Filter.Eventually.of_forall fun y =>
+        (norm_real_smul_continuousLinearMap_one_le _ _).trans
+          (mul_le_mul_of_nonneg_right (hM p.1 (hmem p.1) _ ) (norm_nonneg _))
+    · exact (integrable_gradient zero_lt_one).norm.const_mul M
+    · exact Filter.Eventually.of_forall fun y =>
+        (hf.comp_continuous (hs.prodMk (continuous_snd.sub (ha.smul continuous_const)))
+          (fun p => ⟨hmem p.1, mem_univ _⟩)).smul continuous_const
+  apply ((ha.inv₀ (fun p => (hapos p).ne')).smul hn).congr
+  intro p
+  have hfc : Continuous (fun y : E => f (p.1, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem p.1, mem_univ y⟩)
+  rw [gradient_heatSolution_eq_integral (sub_pos.mpr p.1.property.2)
+    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM p.1 (hmem p.1))]
+  have h := gradient_convolution_sq (Real.sqrt (t - p.1)) (hapos p)
+    (fun y => f (p.1, y)) p.2
+  rw [Real.sq_sqrt (sub_pos.mpr p.1.property.2).le] at h
+  exact h.symm
+
+/-- The gradient time majorant is integrable through the endpoint. -/
+theorem intervalIntegrable_gradient_majorant (t A : ℝ) :
+    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
+  convert intervalIntegrable_hessian_majorant (α := 1) zero_lt_one t A using 1
+  norm_num
+
+/-- The actual first spatial derivative is integrable in Duhamel time. -/
+theorem intervalIntegrable_gradient_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    IntervalIntegrable
+      (fun s : ℝ => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) volume 0 t := by
+  have hc := (continuous_gradient_heatSolution_time ht hf hM).comp
+    (continuous_id.prodMk (continuous_const : Continuous (fun _ : Ioo (0 : ℝ) t => x)))
+  let A := M * (∫ y : E, ‖Grad 1 y‖)
+  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+    (intervalIntegrable_gradient_majorant t A)
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
+    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
+  refine hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
+  have hmem : (s : ℝ) ∈ Icc 0 T := ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hfc : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem, mem_univ y⟩)
+  exact norm_gradient_heatSolution_le (sub_pos.mpr s.property.2)
+    hfc.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM s hmem) x
+
+
+/-- The heat kernel is jointly continuous away from zero time. -/
+theorem continuous_kernel_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => heatKernel (p.1 : ℝ) p.2) := by
+  have ht (p : Ioi (0 : ℝ) × E) : 0 < (p.1 : ℝ) := p.1.property
+  unfold heatKernel
+  apply Continuous.mul
+  · apply Continuous.rpow_const (by fun_prop)
+    intro p
+    left
+    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ht p).ne'
+  · apply Continuous.rexp
+    apply Continuous.div (by fun_prop) (by fun_prop)
+    intro p
+    exact mul_ne_zero (by norm_num) (ht p).ne'
+
+/-- Bounded cylinder data give a genuine time integral for the heat evolution. -/
+theorem intervalIntegrable_heatSolution_time {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    IntervalIntegrable
+      (fun s : ℝ => heatSolution (t - s) (fun y => f (s, y)) x) volume 0 t := by
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have hfc : Continuous (fun p : Ioo (0 : ℝ) t × E => f (p.1, x - p.2)) :=
+    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hk : Continuous (fun p : Ioo (0 : ℝ) t × E => heatKernel (t - p.1) p.2) :=
+    continuous_kernel_pos.comp
+      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
+        continuous_snd)
+  have hm := (hk.mul hfc).stronglyMeasurable.integral_prod_right' (ν := volume)
+  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 t)
+  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1,
+    integrableOn_iff_comap_subtypeVal measurableSet_Ioo]
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi
+  refine hi.mono' (by simpa only [heatSolution_apply] using hm.aestronglyMeasurable)
+    (Filter.Eventually.of_forall fun s => ?_)
+  have hpos := sub_pos.mpr s.property.2
+  dsimp only [Function.comp_apply]
+  rw [heatSolution_apply]
+  calc
+    ‖∫ y : E, heatKernel (t - s) y * f (s, x - y)‖ ≤
+        ∫ y : E, M * heatKernel (t - s) y := by
+      apply norm_integral_le_of_norm_le ((heatKernel_integrable («E» := E) hpos).const_mul M)
+      refine Filter.Eventually.of_forall fun y => ?_
+      rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hpos y), mul_comm]
+      exact mul_le_mul_of_nonneg_right (hM s (hmem s) _) (heatKernel_nonneg hpos y)
+    _ = M := by rw [integral_const_mul, integral_heatKernel_eq_one hpos, mul_one]
+
+/-- First spatial differentiation under the Duhamel time integral. -/
+theorem hasFDerivAt_duhamel {T t M : ℝ} (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M) (x : E) :
+    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z)
+      (∫ s in (0 : ℝ)..t, fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) x) x := by
+  let A := M * (∫ y : E, ‖Grad 1 y‖)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem s hs, mem_univ y⟩)
+  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
+    (F' := fun z s => fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
+    (s := univ) (bound := fun s => A * (t - s) ^ (-(1 / 2 : ℝ))) (by simp)
+  · exact Filter.Eventually.of_forall fun z => by
+      simpa only [uIoc_of_le ht.1] using
+        (intervalIntegrable_heatSolution_time ht hf hM z).aestronglyMeasurable
+  · exact intervalIntegrable_heatSolution_time ht hf hM x
+  · simpa only [uIoc_of_le ht.1] using
+      (intervalIntegrable_gradient_heatSolution_time ht hf hM x).aestronglyMeasurable
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact norm_gradient_heatSolution_le (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z
+  · exact intervalIntegrable_gradient_majorant t A
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact (heatSolution_hasFDerivAt (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable
+      (by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)) z).differentiableAt.hasFDerivAt
+
+/-- Second spatial differentiation uses the integrable cancelled Hessian. -/
+theorem hasFDerivAt_duhamel_gradient {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
+      fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
+      (∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) x := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hmem s hs, mem_univ y⟩)
+  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
+    (F' := fun z s => ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)
+    (s := univ) (bound := fun s => A * (t - s) ^ (α / 2 - 1)) (by simp)
+  · exact Filter.Eventually.of_forall fun z => by
+      simpa only [uIoc_of_le ht.1] using
+        (intervalIntegrable_gradient_heatSolution_time ht hf hM z).aestronglyMeasurable
+  · exact intervalIntegrable_gradient_heatSolution_time ht hf hM x
+  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
+      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x)
+    simpa only [uIoc_of_le ht.1] using hi.aestronglyMeasurable
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s (hmem s hs)) z
+  · exact intervalIntegrable_hessian_majorant hα t A
+  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
+      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
+    have htwo := contDiff_two_heatSolution_of_bounded_measurable
+      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs
+    have hd := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
+      (by norm_num) z).hasFDerivAt
+    rw [hessian_heatSolution_eq_cancelled_integral
+      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
+    exact hd
+
+/-- The cancelled time-integrated Hessian is continuous in the observation point. -/
+theorem continuous_duhamel_hessian {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
+    Continuous (fun x : E => ∫ s in (0 : ℝ)..t, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
+    ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  simp_rw [intervalIntegral.integral_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+  apply continuous_of_dominated (bound := fun s : ℝ => A * (t - s) ^ (α / 2 - 1))
+  · intro x
+    exact (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x).aestronglyMeasurable
+  · intro x
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s (hmem s hs)) x
+  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    have hfc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hmem s hs, mem_univ y⟩)
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by
+      simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
+    have htwo := contDiff_two_heatSolution_of_bounded_measurable
+      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs
+    have hc := ((htwo.fderiv_right (m := 1) (by norm_num)).fderiv_right
+      (m := 0) (by norm_num)).continuous
+    exact hc.congr (fun x => hessian_heatSolution_eq_cancelled_integral
+      (sub_pos.mpr hs.2) hfc.aestronglyMeasurable hMs x)
+
+/-- The actual second derivative equals the cancelled double integral. -/
+theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    fderiv ℝ (fderiv ℝ (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z)) x =
+      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y := by
+  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
+  rw [hD]
+  exact (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK x).fderiv
+
+/-- Spatial C² regularity of the Duhamel formula under the frozen forcing hypotheses. -/
+theorem contDiff_two_duhamel {α T t M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) :
+    ContDiff ℝ 2 (fun z : E => ∫ s in (0 : ℝ)..t,
+      heatSolution (t - s) (fun y => f (s, y)) z) := by
+  have hD := funext (fun z => (hasFDerivAt_duhamel ht hf hM z).fderiv)
+  have hDD := funext (fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).fderiv)
+  change ContDiff ℝ (1 + 1) _
+  refine contDiff_succ_iff_fderiv.mpr
+    ⟨fun z => (hasFDerivAt_duhamel ht hf hM z).differentiableAt, by norm_num, ?_⟩
+  rw [hD]
+  apply contDiff_one_iff_fderiv.mpr
+  refine ⟨fun z => (hasFDerivAt_duhamel_gradient hα hα1 ht hf hM hK z).differentiableAt, ?_⟩
+  rw [hDD]
+  exact continuous_duhamel_hessian hα hα1 ht hf hM hK
+
+/-- The frozen spatial Hölder Duhamel Hessian estimate. -/
+theorem duhamel_hessian_bound :
+  (∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  (∀ x, u 0 x = 0) ∧
+  ∀ t ∈ Icc 0 T, ∀ x : E,
+    ContDiff ℝ 2 (u t) ∧
+    IntegrableOn (fun s : ℝ => ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y) (Ioo 0 t) ∧
+    fderiv ℝ (fderiv ℝ (u t)) x =
+      ∫ s in (0 : ℝ)..t, ∫ y : E, (f (s,x-y)-f (s,x)) • Hess (t-s) y ∧
+    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2)) := by
+  intro α hα hα1
+  let J := ∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α
+  refine ⟨max 1 (J * (2 / α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro T _ _ f M K _ hK0 hf hM hK
+  dsimp only
+  refine ⟨?_, ?_⟩
+  · intro x
+    exact intervalIntegral.integral_same
+  · intro t ht x
+    refine ⟨contDiff_two_duhamel hα hα1 ht hf hM hK,
+      integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
+      hessian_duhamel_eq_integral hα hα1 ht hf hM hK x, ?_⟩
+    rw [hessian_duhamel_eq_integral hα hα1 ht hf hM hK x]
+    calc
+      ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+          (K * J) * (2 / α) * t ^ (α / 2) :=
+        norm_integral_cancelled_hessian_time_le hα hα1 ht.1
+          (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht.2⟩) x
+      _ = (J * (2 / α)) * K * t ^ (α / 2) := by ring
+      _ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2) :=
+        mul_le_mul_of_nonneg_right
+          (mul_le_mul_of_nonneg_right (le_max_right _ _) hK0)
+          (Real.rpow_nonneg ht.1 _)
+
+end Poincare.HeatDuhamelHessianDifferentiation

exit=0
```
