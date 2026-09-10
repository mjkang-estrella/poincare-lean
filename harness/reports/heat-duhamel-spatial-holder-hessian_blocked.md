# Heat Duhamel spatial Hölder Hessian: verified partial result

Date: 2026-09-10. Class B, blocked at step 3. The frozen `duhamel_hessian_bound` is **not proved** and is not declared in the new module. Steps 1 and 2 are proved, including the full heat-convolution Hessian identity, cancellation, actual time integrability of the cancelled integral, and its sharp time-integrated norm bound.

Base: `4c991f21338119d3cf0881e13b2ffaff465b902f`. Proof head: `eac76c3ac15c77f798f4101da2051512481a14ba`.
Branch: `worker/heat-duhamel-spatial-holder-hessian`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.
Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.

The worktree was clean at the recorded base. `git status --short --branch`, `git worktree list --porcelain`, and `git rev-parse eac76c3ac15c77f798f4101da2051512481a14ba` were checked before editing. README, HANDOFF's top section, PROJECT_MAP, AGENTS, the task file, the survey's requested sections and Appendix D2, K1, and the relevant landed heat definitions/imports were read. The task's supplied `worker/*` branch takes precedence over the general branch-prefix rule. The task assigns this file exclusively; no other worker was launched.

Exactly one new repository Lean module is delivered: `Poincare/Global/HeatDuhamelSpatialHolderHessian.lean`. No existing Lean file, root import, task, frozen contract, ledger, or mission was edited. This report and a dated HANDOFF entry are the only other deliverables. The worker neither merged the branch nor marked the task accepted. No full project build or root integration audits are claimed.

## Compiled result

All theorem names below are in `Poincare.HeatDuhamelSpatialHolderHessian`. `E`, `Hess`, and the local normed-group instance match K1 and Appendix D2.

- `hessian_heatSolution_eq_integral` lifts the landed evaluated derivative theorem to the full nested continuous-linear-map equality for bounded a.e. strongly measurable data.
- `hessian_heatSolution_eq_integral_sub` changes variables to `∫ y, f (x-y) • Hess t y`.
- `hessian_heatSolution_eq_cancelled_integral` proves equality with `∫ y, (f (x-y)-f x) • Hess t y`, using K1's tensor cancellation. The three corresponding integrability lemmas prove genuine Bochner integrability.
- `norm_cancelled_hessian_integrand_le` and `norm_cancelled_hessian_integral_le` prove the weighted majorant and its sharp scaling. If `Jα = ∫ y, ‖Hess 1 y‖ * ‖y‖^α`, the bound is `K * Jα * t^(α/2-1)`. `exists_heat_hessian_holder_bound` gives a positive forcing-independent constant `max 1 Jα` for the actual heat-solution Hessian, at every positive time.
- `intervalIntegrable_hessian_majorant` and `integral_hessian_majorant` prove endpoint integrability and the exact integral `A * (2/α) * t^(α/2)`.
- `continuous_hessian_pos` proves joint positive-time Hessian continuity by dilation to time one.
- `integrableOn_cancelled_hessian_time` proves the actual K2 time-integrability clause from cylinder continuity and uniform spatial Hölder control. No extra temporal regularity assumption is introduced. This lemma does not need the forcing's boundedness premise.
- `norm_integral_cancelled_hessian_time_le` proves the bound on the double integral with coefficient `K * Jα * (2/α)`. Together with the preceding integrability theorem, this is a bound on a genuine time integral. The norm inequality alone is more general and does not assume measurability; that generality is not used to claim time integrability.

The proofs retain the task's operator-norm convention. Generic `norm_smul`/`norm_smul_le` instance search initially failed on the nested operator space. The first bound uses the landed explicit bilinear scalar-norm inequality. Proof-local `NormedSpace` instances built from that proved inequality enable the ordinary scalar-action and Bochner lemmas. These instances introduce no premise and do not change the target norm.

Each of the 14 theorems was checked and committed separately. The full new module is 257 lines. Its 14 theorems and generated local instance all have exactly the required three foundational dependencies. The final checks are reproduced below, including a scan of all 15 noninternal declarations and explicit `#print axioms` output for each.

## Exact remaining step

The step-3 probe applies `hasFDerivAt_integral_of_dominated_of_fderiv_le''` to

```lean
fun z : E => ∫ s in (0 : ℝ)..t,
  fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) z
```

with derivative candidate

```lean
∫ s in (0 : ℝ)..t, ∫ y : E,
  (f (s,x-y)-f (s,x)) • Hess (t-s) y
```

and majorant `(K * Jα) * (t-s)^(α/2-1)`, under the full frozen forcing hypotheses. The derivative-candidate measurability, uniform derivative bound, time-majorant integrability, and pointwise spatial differentiability branches close. The following two branches remain unproved:

```lean
∀ᶠ z in 𝓝 x,
  AEStronglyMeasurable
    (fun s => fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) z)
    (volume.restrict (Ι 0 t))

IntervalIntegrable
  (fun s => fderiv ℝ (heatSolution (t-s) (fun y => f (s,y))) x)
  volume 0 t
```

This is an unfinished library/proof step, not a counterexample or a claim of nonderivability. The expected continuation is to prove the positive-time gradient kernel's joint measurability and an integrable gradient time bound, using its explicit formula and dilation. The landed spatial integral integrability theorem controls integration in `y` at fixed positive time; it does not directly discharge integration in `s` down to `t-s=0`. The locally uniform translated Gaussian envelopes have inverse-time exponential dependence and do not themselves give the required endpoint bound.

Even after those two branches close, the first differentiation of `u t` and continuity of the resulting second spatial derivative must still be proved. This worker does not claim `ContDiff ℝ 2 (u t)`, equality of its Hessian with the double integral, or the complete frozen theorem. The empty-interval value at zero is not the resisting step. No replacement target or conditional theorem with extra analytic hypotheses is exported.

First action for the next proof attempt:

```sh
rg -n 'hasFDerivAt_heatKernel_spatial|integrable_smul_fderiv_heatKernel_sub' Poincare/Global/HeatCauchyTheorem.lean Poincare/Global/HeatCauchyNext2.lean
```

## Reproducing the unfinished step-3 probe

Append the following code to a copy of the delivered module, outside the repository Lean tree, and run `LEAN_NUM_THREADS=1 lake env lean <copy>`. The two `skip` branches are deliberately left open to display the exact unresolved goals; the compiler exits 1. This scratch probe is not a delivered Lean theorem.

```lean
namespace Poincare.HeatDuhamelSpatialHolderHessian
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
open scoped Interval
example {α T t M K : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) (ht : t ∈ Icc 0 T)
    (f : ℝ × E → ℝ) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K)
    (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
    (x : E) :
    HasFDerivAt (fun z : E => ∫ s in (0 : ℝ)..t,
      fderiv ℝ (heatSolution (t - s) (fun y => f (s, y))) z)
      (∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y) x := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
  have hmem (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Icc 0 T :=
    ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hfc (s : ℝ) (hs : s ∈ Ioo 0 t) : Continuous (fun y : E => f (s, y)) :=
    hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hmem s hs, mem_univ y⟩)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun z s => ∫ y : E, (f (s, z - y) - f (s, z)) • Hess (t - s) y)
    (s := univ) (bound := fun s => A * (t - s) ^ (α / 2 - 1)) (by simp)
  · skip
  · skip
  · have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mpr
      (integrableOn_cancelled_hessian_time hα hα1 ht hf hK x)
    simpa only [uIoc_of_le ht.1] using hi.aestronglyMeasurable
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
      (sub_pos.mpr hs.2) (hK s (hmem s hs)) z
  · exact intervalIntegrable_hessian_majorant hα t A
  · rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s (hmem s hs)
    have htwo := contDiff_two_heatSolution_of_bounded_measurable
      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs
    have hd := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z).hasFDerivAt
    rw [hessian_heatSolution_eq_cancelled_integral
      (sub_pos.mpr hs.2) (hfc s hs).aestronglyMeasurable hMs z] at hd
    exact hd
end Poincare.HeatDuhamelSpatialHolderHessian
```

Actual final step-3 output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/23-step3.lean
/tmp/heat-duhamel-spatial-holder-hessian/23-step3.lean:286:2: error: unsolved goals
case hF_meas
α T t M K : ℝ
hα : 0 < α
hα1 : α < 1
hT : 0 < T
hT1 : T ≤ 1
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
hK : ∀ s ∈ Icc 0 T, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
this : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ⋯
A : ℝ := ⋯
hmem : ∀ s ∈ Ioo 0 t, s ∈ Icc 0 T
hfc : ∀ s ∈ Ioo 0 t, Continuous fun y => f (s, y)
⊢ ∀ᶠ (x : E) in 𝓝 x,
    AEStronglyMeasurable (fun t_1 => fderiv ℝ (heatSolution (t - t_1) fun y => f (t_1, y)) x) (volume.restrict (Ι 0 t))
/tmp/heat-duhamel-spatial-holder-hessian/23-step3.lean:287:2: error: unsolved goals
case hF_int
α T t M K : ℝ
hα : 0 < α
hα1 : α < 1
hT : 0 < T
hT1 : T ≤ 1
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
hK : ∀ s ∈ Icc 0 T, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
this : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ⋯
A : ℝ := ⋯
hmem : ∀ s ∈ Ioo 0 t, s ∈ Icc 0 T
hfc : ∀ s ∈ Ioo 0 t, Continuous fun y => f (s, y)
⊢ IntervalIntegrable (fun t_1 => fderiv ℝ (heatSolution (t - t_1) fun y => f (t_1, y)) x) volume 0 t

exit=1
```

## Proof commits

```text
9748fb4e Prove bounded-data full Hessian integrability
61c5e8da Identify the full spatial Hessian of bounded heat data
53359b63 Put the heat Hessian formula in cancelled-kernel coordinates
d109ad7a Prove translated bounded-data Hessian integrability
ee1562ac Prove the cancelled heat Hessian identity
afa4f924 Prove Bochner integrability of the cancelled Hessian kernel
00dce682 Bound the cancelled Hessian integrand by its fractional moment
aacf6aa0 Prove the sharp spatial Holder Hessian integral estimate
47f189d3 Bound actual heat Hessians uniformly in the forcing
c1aba1ef Prove time integrability of the sharp Hessian majorant
d306f83b Evaluate the integrable Hessian time majorant exactly
fa4b2506 Prove joint continuity of the positive-time kernel Hessian
de0b21f9 Prove time integrability of the cancelled Duhamel Hessian integral
eac76c3a Bound the cancelled Duhamel Hessian time integral
```

## Final dependency and target checks

The frozen target is only checked as a proposition in probe 25. This checks the statement, not a proof. The source theorem gate exited 0 with no output in probe 21. The token scan exited 1 with no matches, and the whitespace check exited 0.

### 21-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/21-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 24-module-scan

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/24-module-scan.lean
Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_sub_smul_hessian: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_cancelled_integral: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.intervalIntegrable_hessian_majorant: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.integral_hessian_majorant: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.integrable_cancelled_hessian: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integral_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral_sub: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le: [propext,
 Classical.choice,
 Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.norm_cancelled_hessian_integrand_le: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.continuous_hessian_pos: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral: [propext, Classical.choice, Quot.sound]
Poincare.HeatDuhamelSpatialHolderHessian.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
EXACT_DEPENDENCY_SCAN declarations=15 PASS

exit=0
```

### 25-target

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/25-target.lean
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × E → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Icc 0 T ×ˢ univ) →
                        (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                          (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            (∀ (x : E), u 0 x = 0) ∧
                              ∀ t ∈ Icc 0 T,
                                ∀ (x : E),
                                  ContDiff ℝ 2 (u t) ∧
                                    IntegrableOn
                                        (fun s =>
                                          ∫ (y : E),
                                            (f (s, x - y) - f (s, x)) •
                                              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                (t - s) y)
                                        (Ioo 0 t) volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : E),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2) : Prop

exit=0
```

### 27-all-dependencies

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/27-all-dependencies.lean
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
'Poincare.HeatDuhamelSpatialHolderHessian.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

The scan used the following source after the module:

```lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "Poincare.HeatDuhamelSpatialHolderHessian." && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"{n}: {axs}"
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected dependency set for {n}"
      count := count + 1
  logInfo m!"EXACT_DEPENDENCY_SCAN declarations={count} PASS"
```

## Complete compiler probe record

Each numbered proof probe below includes its source delta from the preceding probe and its actual output. Blank context lines in displayed diffs have their trailing spaces removed for the repository whitespace gate. Deltas describe scratch states, including failed states; the final module is the committed source. The cumulative dependency checks between proof commits are preserved separately. All scratch originals remain under `/tmp/heat-duhamel-spatial-holder-hessian` for this worktree session; the evidence needed to review the failures is embedded here.

### Proof probe 01

```diff
--- previous-probe
+++ 01.lean
@@ -0,0 +1,33 @@
+import Poincare.Global.HeatKernelHessianMoments
+import Poincare.Global.HeatCauchyNext2
+import Poincare.Global.HeatMildBUCPositiveHolder
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology
+
+namespace Poincare.HeatDuhamelSpatialHolderHessian
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+open HeatKernelHessianMoments
+
+/-- The full translated Hessian integrand is integrable for bounded measurable data. -/
+theorem integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => f y • Hess t (x - y)) := by
+  have hi := (integrable_hessian ht).norm.comp_sub_left x
+  refine (hi.const_mul M).mono'
+    (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
+  exact Filter.Eventually.of_forall fun y => by
+    rw [norm_smul]
+    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
+
+end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:30:8: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:29:45: error: unsolved goals
t M : ℝ
ht : 0 < t
f : E → ℝ
hf : AEStronglyMeasurable f volume
hM : ∀ (y : E), ‖f y‖ ≤ M
x : E
hi : Integrable (fun t_1 => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - t_1)‖) volume
y : E
⊢ NormSMulClass ℝ (E →L[ℝ] E →L[ℝ] ℝ)

exit=1
```

### Proof probe 02

```diff
--- previous-probe
+++ 02.lean
@@ -27,7 +27,9 @@
   refine (hi.const_mul M).mono'
     (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
   exact Filter.Eventually.of_forall fun y => by
-    rw [norm_smul]
-    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
+    calc
+      ‖f y • Hess t (x - y)‖ ≤ ‖f y‖ * ‖Hess t (x - y)‖ := norm_smul_le _ _
+      _ ≤ M * ‖Hess t (x - y)‖ :=
+        mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:31:59: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

exit=1
```

### Proof probe 03

```diff
--- previous-probe
+++ 03.lean
@@ -28,7 +28,8 @@
     (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
   exact Filter.Eventually.of_forall fun y => by
     calc
-      ‖f y • Hess t (x - y)‖ ≤ ‖f y‖ * ‖Hess t (x - y)‖ := norm_smul_le _ _
+      ‖f y • Hess t (x - y)‖ ≤ ‖f y‖ * ‖Hess t (x - y)‖ :=
+        norm_real_smul_continuousLinearMap_two_le _ _
       _ ≤ M * ‖Hess t (x - y)‖ :=
         mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 04

```diff
--- previous-probe
+++ 04.lean
@@ -33,4 +33,27 @@
       _ ≤ M * ‖Hess t (x - y)‖ :=
         mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

+/-- The spatial Hessian of the heat convolution is the convolution with the full kernel Hessian. -/
+theorem hessian_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, f y • Hess t (x - y) := by
+  have htwo := contDiff_two_heatSolution_of_bounded_measurable ht hf hM
+  have hD := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
+    (by norm_num) x).hasFDerivAt
+  have hi := integrable_data_smul_hessian_sub ht hf hM x
+  ext v w
+  have hc := hD.clm_apply (hasFDerivAt_const w x)
+  have hg := heatSolution_fderiv_apply_hasFDerivAt ht hf hM x w
+  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hc.unique hg)
+  have hiv := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
+  rw [ContinuousLinearMap.integral_apply hi,
+    ContinuousLinearMap.integral_apply hiv]
+  rw [ContinuousLinearMap.integral_apply
+    (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
+  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
+    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, add_zero,
+    ContinuousLinearMap.smul_apply, smul_eq_mul] using he
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:52:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (∫ (x_1 : E),
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v)
        (f x_1 • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - x_1)))
    ?v
in the target expression
  ((fderiv ℝ (fderiv ℝ (heatSolution t f)) x) v) w =
    (∫ (x_1 : E), (f x_1 • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - x_1)) v) w

case h.h
t M : ℝ
ht : 0 < t
f : E → ℝ
hf : AEStronglyMeasurable f volume
hM : ∀ (y : E), ‖f y‖ ≤ M
x : E
htwo : ContDiff ℝ 2 (heatSolution t f)
hD : HasFDerivAt (fderiv ℝ (heatSolution t f)) (fderiv ℝ (fderiv ℝ (heatSolution t f)) x) x
hi : Integrable (fun y => f y • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - y)) volume
v w : E
hc :
  HasFDerivAt (fun y => (fderiv ℝ (heatSolution t f) y) w)
    ((fderiv ℝ (heatSolution t f) x).comp 0 + (fderiv ℝ (fderiv ℝ (heatSolution t f)) x).flip w) x
hg :
  HasFDerivAt (fun z => (fderiv ℝ (heatSolution t f) z) w)
    (∫ (y : E), (f y • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (x - y)).flip w) x
he :
  (fun L => L v) ((fderiv ℝ (heatSolution t f) x).comp 0 + (fderiv ℝ (fderiv ℝ (heatSolution t f)) x).flip w) =
    (fun L => L v) (∫ (y : E), (f y • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (x - y)).flip w)
hiv :
  Integrable
    (fun a =>
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v)
        (f a • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - a)))
    volume
⊢ ((fderiv ℝ (fderiv ℝ (heatSolution t f)) x) v) w =
    (∫ (x_1 : E), (f x_1 • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t (x - x_1)) v) w

exit=1
```

### Proof probe 05

```diff
--- previous-probe
+++ 05.lean
@@ -47,9 +47,11 @@
   have hc := hD.clm_apply (hasFDerivAt_const w x)
   have hg := heatSolution_fderiv_apply_hasFDerivAt ht hf hM x w
   have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hc.unique hg)
-  have hiv := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
+  have hiv : Integrable (fun y : E => (f y • Hess t (x - y)) v) :=
+    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
   rw [ContinuousLinearMap.integral_apply hi,
     ContinuousLinearMap.integral_apply hiv]
+  dsimp only at he
   rw [ContinuousLinearMap.integral_apply
     (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
   simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:57:2: error: Type mismatch: After simplification, term
  he
 has type
  (fderiv ℝ (heatSolution t f) x) 0 + ((fderiv ℝ (fderiv ℝ (heatSolution t f)) x) v) w =
    ∫ (x_1 : E), f x_1 * ((fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (x - x_1)) v) w
but is expected to have type
  ((fderiv ℝ (fderiv ℝ (heatSolution t f)) x) v) w =
    ∫ (x_1 : E), f x_1 * ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) (x - x_1)) v) w

exit=1
```

### Proof probe 06

```diff
--- previous-probe
+++ 06.lean
@@ -56,6 +56,6 @@
     (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
   simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
     ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, add_zero,
-    ContinuousLinearMap.smul_apply, smul_eq_mul] using he
+    ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_add] using he

 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 07

```diff
--- previous-probe
+++ 07.lean
@@ -58,4 +58,15 @@
     ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, add_zero,
     ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_add] using he

+/-- Changing variables puts the kernel Hessian at the integration variable. -/
+theorem hessian_heatSolution_eq_integral_sub {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, f (x - y) • Hess t y := by
+  rw [hessian_heatSolution_eq_integral ht hf hM]
+  have hc := integral_sub_left_eq_self
+    (fun y : E => f y • Hess t (x - y)) volume x
+  simpa only [sub_sub_cancel] using hc.symm
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 08

```diff
--- previous-probe
+++ 08.lean
@@ -69,4 +69,12 @@
     (fun y : E => f y • Hess t (x - y)) volume x
   simpa only [sub_sub_cancel] using hc.symm

+/-- Integrability also holds with bounded data translated against the fixed kernel. -/
+theorem integrable_data_sub_smul_hessian {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => f (x - y) • Hess t y) := by
+  simpa only [sub_sub_cancel] using
+    (integrable_data_smul_hessian_sub ht hf hM x).comp_sub_left x
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 09

```diff
--- previous-probe
+++ 09.lean
@@ -77,4 +77,18 @@
   simpa only [sub_sub_cancel] using
     (integrable_data_smul_hessian_sub ht hf hM x).comp_sub_left x

+/-- Tensor cancellation removes the value of the forcing at the observation point. -/
+theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, (f (x - y) - f x) • Hess t y := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  rw [hessian_heatSolution_eq_integral_sub ht hf hM]
+  simp_rw [sub_smul]
+  rw [integral_sub (integrable_data_sub_smul_hessian ht hf hM x)
+    ((integrable_hessian ht).smul (f x)), integral_smul,
+    integral_hessian_eq_zero ht, smul_zero, sub_zero]
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:90:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : E),
    f (x - a) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t a -
      (f x • fun x => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) a
in the target expression
  ∫ (y : E), f (x - y) • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y =
    ∫ (y : E),
      f (x - y) • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y - f x • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y

t M : ℝ
ht : 0 < t
f : E → ℝ
hf : AEStronglyMeasurable f volume
hM : ∀ (y : E), ‖f y‖ ≤ M
x : E
this : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := { toModule := ContinuousLinearMap.module, norm_smul_le := ⋯ }
⊢ ∫ (y : E), f (x - y) • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y =
    ∫ (y : E),
      f (x - y) • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y - f x • fderiv ℝ (fderiv ℝ fun z => heatKernel t z) y

exit=1
```

### Proof probe 10

```diff
--- previous-probe
+++ 10.lean
@@ -85,10 +85,12 @@
       ∫ y : E, (f (x - y) - f x) • Hess t y := by
   letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
     { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hc : Integrable (fun y : E => f x • Hess t y) :=
+    (integrable_hessian ht).smul (f x)
   rw [hessian_heatSolution_eq_integral_sub ht hf hM]
   simp_rw [sub_smul]
   rw [integral_sub (integrable_data_sub_smul_hessian ht hf hM x)
-    ((integrable_hessian ht).smul (f x)), integral_smul,
+    hc, integral_smul,
     integral_hessian_eq_zero ht, smul_zero, sub_zero]

 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 11

```diff
--- previous-probe
+++ 11.lean
@@ -93,4 +93,15 @@
     hc, integral_smul,
     integral_hessian_eq_zero ht, smul_zero, sub_zero]

+/-- The cancelled Hessian integral remains a genuine Bochner integral. -/
+theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => (f (x - y) - f x) • Hess t y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hc : Integrable (fun y : E => f x • Hess t y) :=
+    (integrable_hessian ht).smul (f x)
+  simpa only [sub_smul] using (integrable_data_sub_smul_hessian ht hf hM x).sub hc
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 12

```diff
--- previous-probe
+++ 12.lean
@@ -104,4 +104,20 @@
     (integrable_hessian ht).smul (f x)
   simpa only [sub_smul] using (integrable_data_sub_smul_hessian ht hf hM x).sub hc

+/-- Spatial Hölder increments supply the weighted Hessian majorant. -/
+theorem norm_cancelled_hessian_integrand_le {α K : ℝ} {f : E → ℝ}
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
+    (t : ℝ) (x y : E) :
+    ‖(f (x - y) - f x) • Hess t y‖ ≤ K * (‖Hess t y‖ * ‖y‖ ^ α) := by
+  have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
+    have h := hK (x - y) x
+    have he : x - y - x = -y := by abel
+    simpa only [he, norm_neg, Real.norm_eq_abs] using h
+  calc
+    ‖(f (x - y) - f x) • Hess t y‖ ≤ ‖f (x - y) - f x‖ * ‖Hess t y‖ :=
+      norm_real_smul_continuousLinearMap_two_le _ _
+    _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y‖ :=
+      mul_le_mul_of_nonneg_right hd (norm_nonneg _)
+    _ = K * (‖Hess t y‖ * ‖y‖ ^ α) := by ring
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 13

```diff
--- previous-probe
+++ 13.lean
@@ -120,4 +120,19 @@
       mul_le_mul_of_nonneg_right hd (norm_nonneg _)
     _ = K * (‖Hess t y‖ * ‖y‖ ^ α) := by ring

+/-- Integrating the spatial Hölder majorant gives the sharp time power. -/
+theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ht : 0 < t) {f : E → ℝ}
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+      K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
+  calc
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+        ∫ y : E, K * (‖Hess t y‖ * ‖y‖ ^ α) :=
+      norm_integral_le_of_norm_le ((integrable_weighted_hessian hα hα2 ht).const_mul K)
+        (Filter.Eventually.of_forall fun y => norm_cancelled_hessian_integrand_le hK t x y)
+    _ = K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
+      rw [integral_const_mul, weighted_hessian_integral ht]
+      ring
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 14

```diff
--- previous-probe
+++ 14.lean
@@ -135,4 +135,23 @@
       rw [integral_const_mul, weighted_hessian_integral ht]
       ring

+/-- A positive constant depending only on the exponent bounds the actual heat Hessian. -/
+theorem exists_heat_hessian_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : ℝ, 0 < C ∧ ∀ {t M K : ℝ}, 0 < t → 0 ≤ K →
+      ∀ {f : E → ℝ}, AEStronglyMeasurable f volume → (∀ y, ‖f y‖ ≤ M) →
+      (∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) → ∀ x : E,
+      ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x‖ ≤ C * K * t ^ (α / 2 - 1) := by
+  refine ⟨max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t M K ht hK0 f hf hM hK x
+  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM]
+  calc
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+        K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) :=
+      norm_cancelled_hessian_integral_le hα.le (by linarith) ht hK x
+    _ ≤ max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * K * t ^ (α / 2 - 1) := by
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
+      rw [mul_comm K]
+      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hK0
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 15

```diff
--- previous-probe
+++ 15.lean
@@ -154,4 +154,13 @@
       rw [mul_comm K]
       exact mul_le_mul_of_nonneg_right (le_max_right _ _) hK0

+/-- The sharp Hessian time majorant is integrable, including its singular endpoint. -/
+theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
+    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) volume 0 t := by
+  have hi := (intervalIntegral.intervalIntegrable_rpow'
+    (a := (0 : ℝ)) (b := t) (r := α / 2 - 1) (by linarith)).comp_sub_left t
+  have hj : IntervalIntegrable (fun s : ℝ => (t - s) ^ (α / 2 - 1)) volume 0 t := by
+    simpa only [sub_zero, sub_self] using hi.symm
+  exact hj.const_mul A
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 16

```diff
--- previous-probe
+++ 16.lean
@@ -163,4 +163,15 @@
     simpa only [sub_zero, sub_self] using hi.symm
   exact hj.const_mul A

+/-- Exact integration of the time majorant supplies the factor two over the exponent. -/
+theorem integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
+    (∫ s in (0 : ℝ)..t, A * (t - s) ^ (α / 2 - 1)) =
+      A * (2 / α) * t ^ (α / 2) := by
+  rw [intervalIntegral.integral_const_mul]
+  have he : α / 2 - 1 = -(1 - α / 2) := by ring
+  simp_rw [he]
+  rw [integral_sub_rpow_neg (by linarith : 1 - α / 2 < 1)]
+  rw [show 1 - (1 - α / 2) = α / 2 by ring]
+  field_simp
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 17

```diff
--- previous-probe
+++ 17.lean
@@ -174,4 +174,28 @@
   rw [show 1 - (1 - α / 2) = α / 2 by ring]
   field_simp

+/-- Dilation gives joint continuity of the full Hessian at positive times. -/
+theorem continuous_hessian_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => Hess p.1 p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hunit : ContDiff ℝ 0 (Hess 1) :=
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
+    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
+  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
+    Real.sqrt_pos.2 p.1.property
+  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
+      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 2)⁻¹) •
+        Hess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
+    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
+      ((ha.pow 2).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
+      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
+  apply hc.congr
+  intro p
+  have h := hessian_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
+    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
+  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 18

```diff
--- previous-probe
+++ 18.lean
@@ -198,4 +198,38 @@
     ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
   simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm

+/-- The cancelled spatial integral is integrable over the Duhamel time interval. -/
+theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) {f : ℝ × E → ℝ}
+    (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    IntegrableOn (fun s : ℝ => ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y) (Ioo 0 t) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have hf1 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x - p.2)) :=
+    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hf2 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x)) :=
+    hf.comp_continuous (hs.prodMk continuous_const)
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hH : Continuous (fun p : Ioo (0 : ℝ) t × E => Hess (t - (p.1 : ℝ)) p.2) :=
+    continuous_hessian_pos.comp
+      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
+        continuous_snd)
+  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right'
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
+  refine hi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
+  exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+    (sub_pos.mpr s.property.2) (hK s (hmem s)) x
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:225:16: error: typeclass instance problem is stuck
  SFinite ?m.491

Note: Lean will not try to resolve this typeclass instance problem because the third type argument to `SFinite` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.

exit=1
```

### Proof probe 19

```diff
--- previous-probe
+++ 19.lean
@@ -222,7 +222,7 @@
     continuous_hessian_pos.comp
       (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
         continuous_snd)
-  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right'
+  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
   let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
   have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
     (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### Proof probe 20

```diff
--- previous-probe
+++ 20.lean
@@ -232,4 +232,26 @@
   exact norm_cancelled_hessian_integral_le hα.le (by linarith)
     (sub_pos.mpr s.property.2) (hK s (hmem s)) x

+/-- The cancelled Duhamel integral has the required spatial Hessian size. -/
+theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : 0 ≤ t) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo 0 t, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * t ^ (α / 2) := by
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  have hb : ‖∫ s in Ioo (0 : ℝ) t, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      ∫ s in Ioo (0 : ℝ) t, A * (t - s) ^ (α / 2 - 1) := by
+    apply norm_integral_le_of_norm_le hi
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s hs) x
+  rw [Measure.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
+    ← intervalIntegral.integral_of_le ht] at hb
+  simpa only [integral_hessian_majorant hα, A] using hb
+
 end Poincare.HeatDuhamelSpatialHolderHessian
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:253:6: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.restrict_Ioo_eq_restrict_Ioc`
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:241:71: error: unsolved goals
α K t : ℝ
hα : 0 < α
hα1 : α < 1
ht : 0 ≤ t
f : ℝ × E → ℝ
hK : ∀ s ∈ Ioo 0 t, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
A : ℝ := K * ∫ (y : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 y‖ * ‖y‖ ^ α
hi : IntegrableOn (fun s => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) volume
hb :
  ‖∫ (s : ℝ) in Ioo 0 t,
        ∫ (y : E), (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (t - s) y‖ ≤
    ∫ (s : ℝ) in Ioo 0 t, A * (t - s) ^ (α / 2 - 1)
⊢ ‖∫ (s : ℝ) in 0..t,
        ∫ (y : E), (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (t - s) y‖ ≤
    (K * ∫ (y : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) * (2 / α) * t ^ (α / 2)

exit=1
```

### Proof probe 21

```diff
--- previous-probe
+++ 21.lean
@@ -250,7 +250,7 @@
     filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
     exact norm_cancelled_hessian_integral_le hα.le (by linarith)
       (sub_pos.mpr hs.2) (hK s hs) x
-  rw [Measure.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
+  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
     ← intervalIntegral.integral_of_le ht] at hb
   simpa only [integral_hessian_majorant hα, A] using hb

```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0
```

### 22-step3

This first time-differentiation probe additionally needed `uIoc_of_le ht.1` to align the derivative-candidate measure. Probe 23 above fixes that and leaves exactly the two first-derivative time obligations.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/22-step3.lean
/tmp/heat-duhamel-spatial-holder-hessian/22-step3.lean:286:2: error: unsolved goals
case hF_meas
α T t M K : ℝ
hα : 0 < α
hα1 : α < 1
hT : 0 < T
hT1 : T ≤ 1
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
hK : ∀ s ∈ Icc 0 T, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
this : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ⋯
A : ℝ := ⋯
hmem : ∀ s ∈ Ioo 0 t, s ∈ Icc 0 T
hfc : ∀ s ∈ Ioo 0 t, Continuous fun y => f (s, y)
⊢ ∀ᶠ (x : E) in 𝓝 x,
    AEStronglyMeasurable (fun t_1 => fderiv ℝ (heatSolution (t - t_1) fun y => f (t_1, y)) x) (volume.restrict (Ι 0 t))
/tmp/heat-duhamel-spatial-holder-hessian/22-step3.lean:287:2: error: unsolved goals
case hF_int
α T t M K : ℝ
hα : 0 < α
hα1 : α < 1
hT : 0 < T
hT1 : T ≤ 1
ht : t ∈ Icc 0 T
f : ℝ × E → ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ s ∈ Icc 0 T, ∀ (y : E), |f (s, y)| ≤ M
hK : ∀ s ∈ Icc 0 T, ∀ (x y : E), |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α
x : E
this : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ⋯
A : ℝ := ⋯
hmem : ∀ s ∈ Ioo 0 t, s ∈ Icc 0 T
hfc : ∀ s ∈ Ioo 0 t, Continuous fun y => f (s, y)
⊢ IntervalIntegrable (fun t_1 => fderiv ℝ (heatSolution (t - t_1) fun y => f (t_1, y)) x) volume 0 t
/tmp/heat-duhamel-spatial-holder-hessian/22-step3.lean:290:4: error: Type mismatch
  IntervalIntegrable.aestronglyMeasurable hi
has type
  AEStronglyMeasurable
    (fun s =>
      ∫ (y : E), (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (t - s) y)
    (volume.restrict (Ioc 0 t))
but is expected to have type
  AEStronglyMeasurable
    (fun s =>
      ∫ (y : E), (f (s, x - y) - f (s, x)) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (t - s) y)
    (volume.restrict (Ι 0 t))

exit=1
```

## Checks run before each proof commit

### 03-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/03-dependencies.lean
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 06-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/06-dependencies.lean
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 07-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/07-dependencies.lean
'Poincare.HeatDuhamelSpatialHolderHessian.integrable_data_smul_hessian_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelSpatialHolderHessian.hessian_heatSolution_eq_integral_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 08-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/08-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 10-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/10-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 11-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/11-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 12-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/12-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 13-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/13-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 14-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/14-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 15-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/15-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 16-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/16-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 17-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/17-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

### 19-gate

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-duhamel-spatial-holder-hessian/19-dependencies.lean
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
exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0
```

## Source-name verification

The additive translation names are generated by Mathlib `to_additive`; their multiplicative source declarations are in `MeasureTheory/Group/Integral.lean`. The initial combined name search used word boundaries, so its one apparent missing name, which ends in apostrophes, was rechecked literally.

```text
Source-name search: rg -n --glob *.lean <combined exact-name pattern> Poincare .lake/packages/mathlib/Mathlib
exit=0
First matching source line per searched name:
AEStronglyMeasurable
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyMaximumDifferentialDecay.lean:80:    (hMeasurable : AEStronglyMeasurable
ContDiff
Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:20:open scoped Manifold ContDiff
Continuous
Poincare/Global/CartanRootedOverlapReparameterizedBoundary.lean:110:    Continuous (boundaryReparameterization endpoint x N) :=
ContinuousOn
Poincare/Global/DeTurckFlowVariationalIdentification.lean:156:  have hbaseContOn : ContinuousOn (alpha z₀) (Icc (-ε) ε) :=
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
_
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:116:  | .ofScalar c => algebraMap _ _ c
add_apply
.lake/packages/mathlib/Mathlib/Algebra/Exact.lean:392:      simp only [add_apply, coe_comp, comp_apply, fst_apply, snd_apply] at e
add_zero
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:233:  add_zero := by
ae_restrict_mem
Poincare/Global/NormalizedFlowAbsoluteDissipationDecay.lean:49:  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
clm_apply
Poincare/Global/DeTurckFlowVariationalIdentification.lean:306:          simpa using (hDvar tau htau).clm_apply hc
comp_apply
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:376:      simp only [Function.comp_apply, ι_def]
comp_continuous
Poincare/Global/DeTurckFlowVariationalIdentification.lean:165:      hbaseContOn.comp_continuous hclamp
comp_sub_left
Poincare/Global/HeatEnvelopes.lean:106:  exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) ha).comp_sub_left x
const_mul
Poincare/CurvatureConditions.lean:328:        ((hasDerivAt_id t₀).const_mul (2 * lam * (g₀ x (Z x) w)))
contDiff_heatKernel_spatial
Poincare/Global/HeatEnvelopes.lean:164:      (contDiff_heatKernel_spatial (E := E) s).continuous.comp hsub
contDiff_two_heatSolution_of_bounded_measurable
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:42:  have htwo := contDiff_two_heatSolution_of_bounded_measurable ht hf hM
continuous_const
Poincare/CurvatureConditions.lean:612:        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
continuous_fst
Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:161:        continuous_fst).rexp)).comp continuous_id)
continuous_hessian_pos
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:178:theorem continuous_hessian_pos :
continuous_snd
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:220:    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
continuous_sqrt
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:186:    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
continuous_subtype_val
Poincare/Global/DeTurckFlowVariationalIdentification.lean:162:    exact continuous_subtype_val.comp continuous_projIcc
exists_heat_hessian_holder_bound
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:139:theorem exists_heat_hessian_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
fderiv
Poincare/Global/DeTurckFlowVariationalIdentification.lean:50:    fderiv ℝ (inverseGaugePointExtendedField W) (t, x) (0, h) =
fderiv_right
Poincare/Global/LocalUniformTaylorRemainder.lean:37:      (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt).continuousWithinAt
field_simp
Poincare/CurvatureConditions.lean:409:  field_simp
filter_upwards
Poincare/CurvatureConditions.lean:99:    filter_upwards [interior_mem_nhds.mpr hv'] with y hy
flip_apply
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:563:  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
hasFDerivAt_const
Poincare/Global/FixedChartUniformJacobiComparison.lean:229:    ((hasFDerivAt_const (extChartAt I x₀ x) v).prodMk C.timeRescaling.hasFDerivAt)
hasFDerivAt_integral_of_dominated_of_fderiv_le
Poincare/Global/HeatLaplacianZeroTime.lean:111:  have hraw := hasFDerivAt_integral_of_dominated_of_fderiv_le
hasFDerivAt_integral_of_dominated_of_fderiv_le''
NO MATCH
heatKernel
Poincare/Global/HeatCauchyFrechet.lean:9:derivative integrand for `x ↦ heatKernel t (x - y) * c` is dominated, in
heatSolution
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:40:    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
heatSolution_fderiv_apply_hasFDerivAt
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:48:  have hg := heatSolution_fderiv_apply_hasFDerivAt ht hf hM x w
hessian_sq_smul
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:197:  have h := hessian_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
integrableOn_cancelled_hessian_time
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:202:theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
integrableOn_iff_comap_subtypeVal
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:230:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
integrable_cancelled_hessian
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:97:theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
integrable_comp
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:51:    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
integrable_data_smul_hessian_sub
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:22:theorem integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
integrable_data_sub_smul_hessian
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:73:theorem integrable_data_sub_smul_hessian {t M : ℝ} (ht : 0 < t)
integrable_hessian
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:26:  have hi := (integrable_hessian ht).norm.comp_sub_left x
integrable_smul_fderiv_fderiv_heatKernel_sub_flip
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:56:    (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
integrable_weighted_hessian
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:132:      norm_integral_le_of_norm_le ((integrable_weighted_hessian hα hα2 ht).const_mul K)
integral_apply
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:52:  rw [ContinuousLinearMap.integral_apply hi,
integral_const_mul
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:336:    rw [integral_const_mul]
integral_hessian_eq_zero
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:94:    integral_hessian_eq_zero ht, smul_zero, sub_zero]
integral_hessian_majorant
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:167:theorem integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
integral_of_le
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:201:          intervalIntegral.integral_of_le hn
integral_prod_right
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:225:  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
integral_smul
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:93:    hc, integral_smul,
integral_sub
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:92:  rw [integral_sub (integrable_data_sub_smul_hessian ht hf hM x)
integral_sub_left_eq_self
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:68:  have hc := integral_sub_left_eq_self
integral_sub_rpow_neg
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:173:  rw [integral_sub_rpow_neg (by linarith : 1 - α / 2 < 1)]
intervalIntegrable_hessian_majorant
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:158:theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
intervalIntegrable_iff_integrableOn_Ioo_of_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:228:    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
intervalIntegrable_rpow
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:160:  have hi := (intervalIntegral.intervalIntegrable_rpow'
le_max_left
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:111:      (N' : K) ≤ (N : K) := by exact_mod_cast le_max_left _ _
le_max_right
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:113:      _ ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
lt_of_lt_of_le
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:189:  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)
map_zero
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:244:    rw [map_zero]
measurableSet_Ioo
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:230:  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
mem_univ
Poincare/ProofProgress/OnePointTwoPointComplementTopology.lean:67:    exact Set.mem_univ z
mono
Poincare/CurvatureConditions.lean:100:    exact (((hZv.mono interior_subset) y hy).contMDiffAt
mul_comm
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Associated.lean:116:  rw [mul_comm]
mul_le_mul_of_nonneg_right
Poincare/Global/HeatCauchyFrechet.lean:72:    exact mul_le_mul_of_nonneg_right
norm
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Single.lean:105:  aesop (add norm [update, Finsupp.support_update_ne_zero])
norm_cancelled_hessian_integral_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:124:theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
norm_cancelled_hessian_integrand_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:108:theorem norm_cancelled_hessian_integrand_le {α K : ℝ} {f : E → ℝ}
norm_eq_abs
Poincare/Global/HeatCauchyFrechet.lean:75:    simpa only [innerSL_apply_apply, Real.norm_eq_abs] using abs_real_inner_le_norm (x - y) v
norm_integral_cancelled_hessian_time_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:236:theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
norm_integral_le_of_norm_le
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:274:    MeasureTheory.norm_integral_le_of_norm_le hbound
norm_neg
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_nonneg
Poincare/Global/HeatCauchyFrechet.lean:56:  have hC_nonneg : 0 ≤ C := (norm_nonneg c).trans hc
norm_num
Poincare/CurvatureConditions.lean:98:      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
norm_real_smul_continuousLinearMap_two_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:32:        norm_real_smul_continuousLinearMap_two_le _ _
norm_smul_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:87:    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
of_forall
Poincare/Global/DeTurckFlowVariationalIdentification.lean:295:      apply Filter.Eventually.of_forall
pow_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Divisibility.lean:172:    apply pow_ne_zero m ha₀
restrict_Ioo_eq_restrict_Ioc
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:253:  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
rpow_nonneg
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:585:        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)
set_option
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:315:set_option backward.privateInPublic true in
simp_rw
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Lift.lean:47:    simp_rw [show ∀ (g : G) (r : k), g • r = r by
smul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:179:  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ ↦ Rel.mul_compat_right
smul_apply
Poincare/CurvatureConditions.lean:61:        LinearMap.smul_apply, smul_eq_mul]
smul_eq_mul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:289:    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:28:    (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
smul_inv_smul
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Basic.lean:85:  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
smul_zero
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:79:  smul_zero a := by exact congr_arg ofFinsupp (smul_zero a)
sq_sqrt
Poincare/Global/SpeedPackage.lean:60:  exact Real.sq_sqrt
sqrt_pos
Poincare/Global/HausdorffInverseChartLocalFrozenBilipschitz.lean:93:    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
sub_pos
Poincare/Global/HausdorffInverseChartLocalFrozenBilipschitz.lean:93:    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
sub_self
.lake/packages/mathlib/Mathlib/Algebra/Exact.lean:433:      rw [← sub_eq_zero, ← hz, ← h₁ z, hz, map_sub, e.1, sub_self, map_zero]
sub_smul
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basis.lean:84:    rw [sub_smul, ofNat_smul_eq_nsmul, ← (b.sl2 i).lie_h_e_nsmul, b.lie_h_e i i]; abel
sub_sub_cancel
.lake/packages/mathlib/Mathlib/Algebra/Star/StarProjection.lean:77:  ⟨fun h ↦ sub_sub_cancel 1 p ▸ h.one_sub, .one_sub⟩
sub_zero
.lake/packages/mathlib/Mathlib/Algebra/Quaternion.lean:261:  QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl
subtype_mk
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:874:theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
weighted_hessian_integral
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:135:      rw [integral_const_mul, weighted_hessian_integral ht]
zero_add
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:129:  | zero_add {a : Pre R X} : Rel (0 + a) a
zero_apply
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:284:theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 :=
zero_lt_one
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:386:  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a

$ rg -n -F "hasFDerivAt_integral_of_dominated_of_fderiv_le''" .lake/packages/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean
238:theorem hasFDerivAt_integral_of_dominated_of_fderiv_le'' [NormedSpace ℝ H] {μ : Measure ℝ}
exit=0
```

## Final proof diff

```diff
diff --git a/Poincare/Global/HeatDuhamelSpatialHolderHessian.lean b/Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
new file mode 100644
index 00000000..cde0bbc1
--- /dev/null
+++ b/Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
@@ -0,0 +1,257 @@
+import Poincare.Global.HeatKernelHessianMoments
+import Poincare.Global.HeatCauchyNext2
+import Poincare.Global.HeatMildBUCPositiveHolder
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Topology
+
+namespace Poincare.HeatDuhamelSpatialHolderHessian
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+open HeatKernelHessianMoments
+
+/-- The full translated Hessian integrand is integrable for bounded measurable data. -/
+theorem integrable_data_smul_hessian_sub {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => f y • Hess t (x - y)) := by
+  have hi := (integrable_hessian ht).norm.comp_sub_left x
+  refine (hi.const_mul M).mono'
+    (smul_fderiv_fderiv_heatKernel_sub_aestronglyMeasurable t hf x) ?_
+  exact Filter.Eventually.of_forall fun y => by
+    calc
+      ‖f y • Hess t (x - y)‖ ≤ ‖f y‖ * ‖Hess t (x - y)‖ :=
+        norm_real_smul_continuousLinearMap_two_le _ _
+      _ ≤ M * ‖Hess t (x - y)‖ :=
+        mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
+
+/-- The spatial Hessian of the heat convolution is the convolution with the full kernel Hessian. -/
+theorem hessian_heatSolution_eq_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, f y • Hess t (x - y) := by
+  have htwo := contDiff_two_heatSolution_of_bounded_measurable ht hf hM
+  have hD := ((htwo.fderiv_right (m := 1) (by norm_num)).differentiable
+    (by norm_num) x).hasFDerivAt
+  have hi := integrable_data_smul_hessian_sub ht hf hM x
+  ext v w
+  have hc := hD.clm_apply (hasFDerivAt_const w x)
+  have hg := heatSolution_fderiv_apply_hasFDerivAt ht hf hM x w
+  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hc.unique hg)
+  have hiv : Integrable (fun y : E => (f y • Hess t (x - y)) v) :=
+    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hi
+  rw [ContinuousLinearMap.integral_apply hi,
+    ContinuousLinearMap.integral_apply hiv]
+  dsimp only at he
+  rw [ContinuousLinearMap.integral_apply
+    (integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht hf hM x w)] at he
+  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
+    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, add_zero,
+    ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_add] using he
+
+/-- Changing variables puts the kernel Hessian at the integration variable. -/
+theorem hessian_heatSolution_eq_integral_sub {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, f (x - y) • Hess t y := by
+  rw [hessian_heatSolution_eq_integral ht hf hM]
+  have hc := integral_sub_left_eq_self
+    (fun y : E => f y • Hess t (x - y)) volume x
+  simpa only [sub_sub_cancel] using hc.symm
+
+/-- Integrability also holds with bounded data translated against the fixed kernel. -/
+theorem integrable_data_sub_smul_hessian {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => f (x - y) • Hess t y) := by
+  simpa only [sub_sub_cancel] using
+    (integrable_data_smul_hessian_sub ht hf hM x).comp_sub_left x
+
+/-- Tensor cancellation removes the value of the forcing at the observation point. -/
+theorem hessian_heatSolution_eq_cancelled_integral {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    fderiv ℝ (fderiv ℝ (heatSolution t f)) x =
+      ∫ y : E, (f (x - y) - f x) • Hess t y := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hc : Integrable (fun y : E => f x • Hess t y) :=
+    (integrable_hessian ht).smul (f x)
+  rw [hessian_heatSolution_eq_integral_sub ht hf hM]
+  simp_rw [sub_smul]
+  rw [integral_sub (integrable_data_sub_smul_hessian ht hf hM x)
+    hc, integral_smul,
+    integral_hessian_eq_zero ht, smul_zero, sub_zero]
+
+/-- The cancelled Hessian integral remains a genuine Bochner integral. -/
+theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume)
+    (hM : ∀ y, ‖f y‖ ≤ M) (x : E) :
+    Integrable (fun y : E => (f (x - y) - f x) • Hess t y) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hc : Integrable (fun y : E => f x • Hess t y) :=
+    (integrable_hessian ht).smul (f x)
+  simpa only [sub_smul] using (integrable_data_sub_smul_hessian ht hf hM x).sub hc
+
+/-- Spatial Hölder increments supply the weighted Hessian majorant. -/
+theorem norm_cancelled_hessian_integrand_le {α K : ℝ} {f : E → ℝ}
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α)
+    (t : ℝ) (x y : E) :
+    ‖(f (x - y) - f x) • Hess t y‖ ≤ K * (‖Hess t y‖ * ‖y‖ ^ α) := by
+  have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
+    have h := hK (x - y) x
+    have he : x - y - x = -y := by abel
+    simpa only [he, norm_neg, Real.norm_eq_abs] using h
+  calc
+    ‖(f (x - y) - f x) • Hess t y‖ ≤ ‖f (x - y) - f x‖ * ‖Hess t y‖ :=
+      norm_real_smul_continuousLinearMap_two_le _ _
+    _ ≤ (K * ‖y‖ ^ α) * ‖Hess t y‖ :=
+      mul_le_mul_of_nonneg_right hd (norm_nonneg _)
+    _ = K * (‖Hess t y‖ * ‖y‖ ^ α) := by ring
+
+/-- Integrating the spatial Hölder majorant gives the sharp time power. -/
+theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ht : 0 < t) {f : E → ℝ}
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+      K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
+  calc
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+        ∫ y : E, K * (‖Hess t y‖ * ‖y‖ ^ α) :=
+      norm_integral_le_of_norm_le ((integrable_weighted_hessian hα hα2 ht).const_mul K)
+        (Filter.Eventually.of_forall fun y => norm_cancelled_hessian_integrand_le hK t x y)
+    _ = K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) := by
+      rw [integral_const_mul, weighted_hessian_integral ht]
+      ring
+
+/-- A positive constant depending only on the exponent bounds the actual heat Hessian. -/
+theorem exists_heat_hessian_holder_bound {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : ℝ, 0 < C ∧ ∀ {t M K : ℝ}, 0 < t → 0 ≤ K →
+      ∀ {f : E → ℝ}, AEStronglyMeasurable f volume → (∀ y, ‖f y‖ ≤ M) →
+      (∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) → ∀ x : E,
+      ‖fderiv ℝ (fderiv ℝ (heatSolution t f)) x‖ ≤ C * K * t ^ (α / 2 - 1) := by
+  refine ⟨max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t M K ht hK0 f hf hM hK x
+  rw [hessian_heatSolution_eq_cancelled_integral ht hf hM]
+  calc
+    ‖∫ y : E, (f (x - y) - f x) • Hess t y‖ ≤
+        K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * t ^ (α / 2 - 1) :=
+      norm_cancelled_hessian_integral_le hα.le (by linarith) ht hK x
+    _ ≤ max 1 (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * K * t ^ (α / 2 - 1) := by
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
+      rw [mul_comm K]
+      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hK0
+
+/-- The sharp Hessian time majorant is integrable, including its singular endpoint. -/
+theorem intervalIntegrable_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
+    IntervalIntegrable (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) volume 0 t := by
+  have hi := (intervalIntegral.intervalIntegrable_rpow'
+    (a := (0 : ℝ)) (b := t) (r := α / 2 - 1) (by linarith)).comp_sub_left t
+  have hj : IntervalIntegrable (fun s : ℝ => (t - s) ^ (α / 2 - 1)) volume 0 t := by
+    simpa only [sub_zero, sub_self] using hi.symm
+  exact hj.const_mul A
+
+/-- Exact integration of the time majorant supplies the factor two over the exponent. -/
+theorem integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
+    (∫ s in (0 : ℝ)..t, A * (t - s) ^ (α / 2 - 1)) =
+      A * (2 / α) * t ^ (α / 2) := by
+  rw [intervalIntegral.integral_const_mul]
+  have he : α / 2 - 1 = -(1 - α / 2) := by ring
+  simp_rw [he]
+  rw [integral_sub_rpow_neg (by linarith : 1 - α / 2 < 1)]
+  rw [show 1 - (1 - α / 2) = α / 2 by ring]
+  field_simp
+
+/-- Dilation gives joint continuity of the full Hessian at positive times. -/
+theorem continuous_hessian_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => Hess p.1 p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hunit : ContDiff ℝ 0 (Hess 1) :=
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
+    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
+  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
+    Real.sqrt_pos.2 p.1.property
+  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
+      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 2)⁻¹) •
+        Hess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
+    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
+      ((ha.pow 2).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
+      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
+  apply hc.congr
+  intro p
+  have h := hessian_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
+    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
+  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
+
+/-- The cancelled spatial integral is integrable over the Duhamel time interval. -/
+theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : t ∈ Icc 0 T) {f : ℝ × E → ℝ}
+    (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    IntegrableOn (fun s : ℝ => ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y) (Ioo 0 t) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hmem (s : Ioo (0 : ℝ) t) : (s : ℝ) ∈ Icc 0 T :=
+    ⟨s.property.1.le, s.property.2.le.trans ht.2⟩
+  have hs : Continuous (fun p : Ioo (0 : ℝ) t × E => (p.1 : ℝ)) :=
+    continuous_subtype_val.comp continuous_fst
+  have hf1 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x - p.2)) :=
+    hf.comp_continuous (hs.prodMk (continuous_const.sub continuous_snd))
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hf2 : Continuous (fun p : Ioo (0 : ℝ) t × E => f ((p.1 : ℝ), x)) :=
+    hf.comp_continuous (hs.prodMk continuous_const)
+      (fun p => ⟨hmem p.1, mem_univ _⟩)
+  have hH : Continuous (fun p : Ioo (0 : ℝ) t × E => Hess (t - (p.1 : ℝ)) p.2) :=
+    continuous_hessian_pos.comp
+      (((continuous_const.sub hs).subtype_mk (fun p => sub_pos.mpr p.1.property.2)).prodMk
+        continuous_snd)
+  have hmeas := ((hf1.sub hf2).smul hH).stronglyMeasurable.integral_prod_right' (ν := volume)
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioo] at hi ⊢
+  refine hi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
+  exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+    (sub_pos.mpr s.property.2) (hK s (hmem s)) x
+
+/-- The cancelled Duhamel integral has the required spatial Hessian size. -/
+theorem norm_integral_cancelled_hessian_time_le {α K t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht : 0 ≤ t) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo 0 t, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α)
+    (x : E) :
+    ‖∫ s in (0 : ℝ)..t, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * t ^ (α / 2) := by
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hi : IntegrableOn (fun s : ℝ => A * (t - s) ^ (α / 2 - 1)) (Ioo 0 t) :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp
+      (intervalIntegrable_hessian_majorant hα t A)
+  have hb : ‖∫ s in Ioo (0 : ℝ) t, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      ∫ s in Ioo (0 : ℝ) t, A * (t - s) ^ (α / 2 - 1) := by
+    apply norm_integral_le_of_norm_le hi
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (sub_pos.mpr hs.2) (hK s hs) x
+  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht,
+    ← intervalIntegral.integral_of_le ht] at hb
+  simpa only [integral_hessian_majorant hα, A] using hb
+
+end Poincare.HeatDuhamelSpatialHolderHessian
```

## Final handoff check

The first staged whitespace check detected trailing spaces on blank context lines in the displayed scratch diffs. Those report-only spaces were removed; the Lean source did not change. The final focused compiler check and both staged/unstaged whitespace checks pass.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelSpatialHolderHessian.lean

exit=0

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
(no output)
exit=1

$ git diff --cached --check
(no output)
exit=0

$ git diff --check
(no output)
exit=0
```
