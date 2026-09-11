# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/heat-duhamel-heat-equation`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/heat-duhamel-heat-equation_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. A blocked report displaying the exact resisting estimate with committed partial lemmas is acceptable; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the `Y_T`/`X_T` norms) and 3.2 (step L3) first. Landed parabolic modules, all in `Poincare/Global/`: `HeatKernelHessianMoments.lean` (K1: `hessian_moments`, weighted Hessian moment scaling, `integral_hessian_eq_zero`), `HeatDuhamelSpatialHolderHessian.lean` (Hessian of the heat convolution as the cancelled kernel integral, majorants, time integrability), `HeatDuhamelHessianDifferentiation.lean` (K2: `duhamel_hessian_bound`, `hessian_duhamel_eq_integral`, `contDiff_two_duhamel`, `hasFDerivAt_duhamel`, gradient kernel lemmas, `continuous_duhamel_hessian`), `HeatDuhamelHessianSpatialHolder.lean` (`duhamel_hessian_spatial_holder`, third-derivative kernel moments `third_moment_bound`, translation and segment lemmas), `ParabolicHolderSpace.lean` (`Y α T F`), `ParabolicSolutionGraph.lean` (`Graph α T`), `ParametrixNeumannCorrection.lean`. Throughout, `u t x := ∫ s in (0:ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x`, `E := ClosedSmoothModel 3`, and the `Hess`/local-instance conventions of K1.

# Task heat-duhamel-heat-equation

Module: `Poincare/Global/HeatDuhamelHeatEquation.lean`. Namespace: `Poincare.HeatDuhamelHeatEquation`. Imports: `Poincare.Global.HeatDuhamelHessianDifferentiation` (add what you need).

Objective: the Duhamel integral solves the inhomogeneous heat equation with zero initial value, which is the remaining structural half of step L3 (independent of the time-Hölder estimate). Under the K2 hypotheses (`0 < α < 1`, `0 < T ≤ 1`, `f` cylinder-continuous with `|f| ≤ M` and spatial Hölder constant `K`), prove

```lean
theorem duhamel_solves_heat_equation :
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
      (Icc 0 T) t
```

Probe the exact spelling of the Laplacian sum against the landed conventions first (the repository may already have a coordinate Laplacian abbreviation for `E`; grep `heatSolution_solves_heatEquation`, `vectorHeatSolution_solves_heatEquation_of_bounded_measurable`, and any `laplacian`/`trace` helper on `E` and reuse it rather than spelling the sum by hand — if you change the spelling, say so and justify that it is definitionally the trace of the Hessian).

Route: differentiate `t ↦ ∫₀ᵗ v(t, s, x) ds` where `v(t,s,x) := heatSolution (t−s) (f(s,·)) x`, using the Leibniz rule for an integral whose integrand also depends on the upper limit: the boundary term is `lim_{s→t⁻} v(t,s,x) = f(t,x)` (continuity of the heat semigroup at time zero on the cylinder-continuous bounded data; the landed BUC material should have the approximate-identity statement, grep `heatSolution_tendsto` / `tendsto_heatSolution`), and the interior term is `∫₀ᵗ ∂ₜ v(t,s,x) ds = ∫₀ᵗ Δₓ v(t,s,x) ds`, which equals `Δₓ u(t,x)` by the landed `hessian_duhamel_eq_integral` and the fact that `v` solves the homogeneous heat equation in `(t−s)` for bounded measurable data (`vectorHeatSolution_solves_heatEquation_of_bounded_measurable`). Justify the interchange with the landed majorants. `u 0 x = 0` is `intervalIntegral.integral_same`.

Exact stop condition: the displayed conjunction compiles and passes the gate; or a blocked report displaying the exact resisting step (most likely the boundary term or the Leibniz interchange) with the committed partial lemmas.
