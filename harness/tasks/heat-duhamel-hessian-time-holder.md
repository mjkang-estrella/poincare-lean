# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/heat-duhamel-hessian-time-holder`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/heat-duhamel-hessian-time-holder_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. A blocked report displaying the exact resisting estimate with committed partial lemmas is acceptable; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the `Y_T`/`X_T` norms) and 3.2 (step L3) first. Landed parabolic modules, all in `Poincare/Global/`: `HeatKernelHessianMoments.lean` (K1: `hessian_moments`, weighted Hessian moment scaling, `integral_hessian_eq_zero`), `HeatDuhamelSpatialHolderHessian.lean` (Hessian of the heat convolution as the cancelled kernel integral, majorants, time integrability), `HeatDuhamelHessianDifferentiation.lean` (K2: `duhamel_hessian_bound`, `hessian_duhamel_eq_integral`, `contDiff_two_duhamel`, `hasFDerivAt_duhamel`, gradient kernel lemmas, `continuous_duhamel_hessian`), `HeatDuhamelHessianSpatialHolder.lean` (`duhamel_hessian_spatial_holder`, third-derivative kernel moments `third_moment_bound`, translation and segment lemmas), `ParabolicHolderSpace.lean` (`Y α T F`), `ParabolicSolutionGraph.lean` (`Graph α T`), `ParametrixNeumannCorrection.lean`. Throughout, `u t x := ∫ s in (0:ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x`, `E := ClosedSmoothModel 3`, and the `Hess`/local-instance conventions of K1.

# Task heat-duhamel-hessian-time-holder

Module: `Poincare/Global/HeatDuhamelHessianTimeHolder.lean`. Namespace: `Poincare.HeatDuhamelHessianTimeHolder`. Imports: `Poincare.Global.HeatDuhamelHessianSpatialHolder` (add what you need).

Objective: the time half of the parabolic Hölder estimate for the Duhamel Hessian. Under the same hypotheses as `duhamel_hessian_spatial_holder` (`0 < α < 1`, `0 < T ≤ 1`, `f` cylinder-continuous, `|f| ≤ M`, spatial Hölder constant `K`), prove

```lean
theorem duhamel_hessian_time_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖
      ≤ C * K * |t₁ - t₂| ^ (α / 2)
```

Probe the statement before starting. Route (standard, symmetric in `t₁ < t₂`, write `τ := t₂ − t₁` and `ρ := √τ`): using the landed `hessian_duhamel_eq_integral`, both Hessians are time integrals of the cancelled kernel integral `Φ(t, s, x) := ∫ y, (f(s,x−y) − f(s,x)) • Hess (t−s) y`, whose norm is at most `K Jα (t−s)^{α/2−1}`. Split `D²u(t₂) − D²u(t₁)` as
(i) the tail `∫_{t₁}^{t₂} Φ(t₂, s, x) ds`, bounded by `K Jα (2/α) τ^{α/2}` by the landed majorant integral; plus
(ii) `∫_0^{t₁} [Φ(t₂, s, x) − Φ(t₁, s, x)] ds`. For (ii) split again at `s = t₁ − τ`: on the near part `s ∈ (t₁ − τ, t₁)` bound each term separately by the majorant, giving another `C K τ^{α/2}`; on the far part `s ∈ (0, t₁ − τ)` use the time derivative of the kernel Hessian, `∂ₜ Hess_t(y) = Δ Hess_t(y)` or directly the explicit Gaussian time derivative, with a fourth-order-type moment bound `∫ ‖∂ₜ Hess_τ(y)‖ ‖y‖^α dy ≤ C₄ τ^{α/2−2}` (prove it exactly as K1 and the third-moment lemma did: explicit derivative of the Gaussian, dilation, Gaussian-times-power envelope), then `τ ∫_0^{t₁−τ} (t₁−s)^{α/2−2} ds ≤ C τ^{α/2}`.
Commit the kernel time-derivative moment lemma, the tail bound, the near bound, the far bound, and the assembly separately.

Exact stop condition: the displayed theorem compiles and passes the gate; or a blocked report displaying the exact resisting estimate with the committed partial lemmas (the kernel time-derivative moment bound and the tail bound at least are expected).
