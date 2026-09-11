# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/heat-duhamel-hessian-spatial-holder`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/heat-duhamel-hessian-spatial-holder_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting step and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first.

# Task heat-duhamel-hessian-spatial-holder

Read `harness/reports/parabolic-schauder-decomposition-survey_done.md` sections 3.1-3.2 (L3) and the landed K1/K2 modules: `Poincare/Global/HeatKernelHessianMoments.lean`, `Poincare/Global/HeatDuhamelSpatialHolderHessian.lean`, `Poincare/Global/HeatDuhamelHessianDifferentiation.lean` (`duhamel_hessian_bound`, `hessian_duhamel_eq_integral`, `continuous_duhamel_hessian`, the gradient and Hessian kernel lemmas). Also `Poincare/Global/ParabolicHolderSpace.lean` (`parabolicDist`, `HasHolderBound`, `cylinder`).

Module: `Poincare/Global/HeatDuhamelHessianSpatialHolder.lean`. Namespace: `Poincare.HeatDuhamelHessianSpatialHolder`. Imports: `Poincare.Global.HeatDuhamelHessianDifferentiation` (add what you need).

Objective: the spatial Hölder estimate for the Duhamel Hessian, the first half of L3. Under the K2 hypotheses (`0 < α < 1`, `0 < T ≤ 1`, `f` cylinder-continuous with `|f| ≤ M` and spatial Hölder constant `K`), with `u t x := ∫ s in 0..t, heatSolution (t-s) (f(s,·)) x`, prove

```lean
theorem duhamel_hessian_spatial_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t ∈ Icc 0 T, ∀ x z : E,
    ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α
```

(same `E`, `Hess`, local instance conventions as K1/K2; probe the statement first). Route (the standard near/far split, Ladyzhenskaya–Solonnikov–Uraltseva / Lieberman): with `ρ := ‖x−z‖`, split the time integral at `s = t − ρ²` (if `ρ² < t`; otherwise only the "near" part exists). Near part `s ∈ (t−ρ², t)`: bound each of the two Hessians separately by the landed pointwise bound `K Jα (t−s)^{α/2−1}`, integrate to `2 K Jα (2/α) ρ^{α}`. Far part `s ∈ (0, t−ρ²)`: write the difference of the two cancelled integrals as `∫ y, (f(s,x−y) − f(s,x)) • (Hess_{t−s}(y) − Hess_{t−s}(y + (x−z)))` after the substitution `y ↦ y + (x − z)` in the second integral and use of `∫ Hess = 0` again (the constants `f(s,x)`, `f(s,z)` drop), then the mean value theorem on the third derivative of the kernel: `‖Hess_τ(y) − Hess_τ(y+w)‖ ≤ ‖w‖ sup ‖D³K_τ‖` along the segment, and a third-moment kernel bound `∫ ‖D³K_τ(y)‖ ‖y‖^α dy ≤ C₃ τ^{α/2 − 3/2}` (prove it exactly as K1 proved the Hessian moment: explicit third derivative of the Gaussian, dilation, Gaussian-times-power envelope; handle the shift `‖y + w‖^α ≤ ‖y‖^α + ‖w‖^α` or restrict to `‖y‖ ≥ 2‖w‖` with a separate small-ball term); integrate `ρ ∫₀^{t−ρ²} (t−s)^{α/2−3/2} ds ≤ ρ · (2/(1−α)) ρ^{α−1} = C ρ^{α}`. Commit the third-moment kernel lemma, the near bound, the far bound, and the assembly separately.

Exact stop condition: the displayed theorem compiles and passes the gate; or a blocked report displaying the exact resisting estimate with committed partial lemmas (the third-moment kernel bound and the near part at least are expected).
