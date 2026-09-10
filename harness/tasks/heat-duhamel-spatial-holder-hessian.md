# Worker contract (Lean task, class B, exploratory)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/heat-duhamel-spatial-holder-hessian`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/heat-duhamel-spatial-holder-hessian_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. This is a class-B task: a blocked report displaying the exact resisting step (for example the identification of the Duhamel second derivative with the cancelled kernel integral, or the differentiation under the time integral) with the strongest compiled partial lemmas committed is acceptable; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` (sections 1.2-1.3, 3.2, 4 (K2), Appendix D2) first. K1 is landed: `Poincare/Global/HeatKernelHessianMoments.lean` (namespace `Poincare.HeatKernelHessianMoments`: `hessian_moments`, `integrable_weighted_hessian`, `weighted_hessian_integral`, `integrable_hessian`, `integral_hessian_eq_zero`, and the scaling lemmas). Landed Duhamel/BUC material: `Poincare/Global/HeatCauchyNext2.lean`, `HeatMildBUCPositiveHolder.lean` (interval-integration calculus for mild solutions), `HeatSemigroupBUCPositiveGenerator.lean`; find the exact names by grep.

# Task heat-duhamel-spatial-holder-hessian

Module: `Poincare/Global/HeatDuhamelSpatialHolderHessian.lean`. Namespace: `Poincare.HeatDuhamelSpatialHolderHessian`. Imports: `Poincare.Global.HeatKernelHessianMoments`, `Poincare.Global.HeatCauchyNext2`, `Poincare.Global.HeatMildBUCPositiveHolder` (add what you need).

Objective: prove the K2 target exactly as probed in Appendix D2 of the survey (same `E`, `Hess`, and local instance conventions as K1):

```lean
theorem duhamel_hessian_bound :
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
    ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2))
```

Route, in order (commit each): (1) for fixed `s < t`, the spatial Hessian of `x ↦ heatSolution (t-s) (f(s,·)) x` equals `∫ y, f(s, x-y) • Hess (t-s) y` (differentiate the convolution under the integral using the landed Hessian envelopes in `HeatCauchyNext2`; bounded `f` suffices), and by K1's cancellation `∫ Hess = 0` this equals `∫ y, (f(s,x-y) - f(s,x)) • Hess (t-s) y`; (2) the norm bound `‖·‖ ≤ K ∫ ‖y‖^α ‖Hess (t-s) y‖ dy ≤ K C₁ (t-s)^{α/2 - 1}` by K1's moment bound, which is integrable on `(0,t)` with integral `K C₁ (2/α) t^{α/2}`; (3) differentiation of the time integral `u t = ∫₀ᵗ v_s ds` under the integral sign in `x` (first and second derivatives) using dominated convergence with the majorants from (2) and the first-derivative analogue (a first-moment kernel bound; prove it from the landed gradient envelope or by the same scaling as K1); (4) assemble `ContDiff ℝ 2 (u t)`, the identification, and the bound with `C := 2 C₁ / α` (or larger). The value `u 0 x = 0` is the empty interval integral.

Exact stop condition: `duhamel_hessian_bound` compiles with exactly the displayed statement; or a blocked report with the exact resisting step and committed partial lemmas (at least steps 1 and 2 are expected to be reachable).
