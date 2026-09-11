# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/duhamel-solution-operator-bound`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/duhamel-solution-operator-bound_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep; record every probe with actual output. Partial landing is acceptable: this task has four independent estimate groups, and a report that lands some and displays the exact resisting goal for the rest is a success. Never weaken a target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` sections 3.1 and 3.2 (step L3) first. Landed, all in `Poincare/Global/` with `u t x := ∫ s in (0:ℝ)..t, heatSolution (t−s) (f(s,·)) x` and `E := ClosedSmoothModel 3`:
- `HeatDuhamelHessianDifferentiation.lean`: `duhamel_hessian_bound` (`‖D²u(t)‖ ≤ C·K·t^{α/2}`), `contDiff_two_duhamel`, `hasFDerivAt_duhamel`, `hessian_duhamel_eq_integral`, and the gradient kernel lemmas `gradient_integral` (`∫‖∇K_t‖ = (∫‖∇K_1‖)·t^{−1/2}`), `gradient_heatSolution_eq_integral`, `norm_gradient_heatSolution_le` (`≤ M·C₁·t^{−1/2}`), `continuous_gradient_heatSolution_time`, `intervalIntegrable_gradient_heatSolution_time`.
- `DuhamelParabolicHolderSeminorm.lean`: `duhamel_hessian_parabolic_holder`, `hasHolderBound_duhamel_hessian`.
- `MovingLimitLeibniz.lean`: `duhamel_solves_heat_equation` (zero initial value and `∂ₜu = f + Δu` within `Icc 0 T`).
- `ParabolicHolderSpace.lean`: `Y α T F`, `parabolicDist`, `cylinder`, `HasHolderBound`, `ofFunction`, `norm_le_of_bounds`, `norm_eq`.
- `ParabolicSolutionGraph.lean`: `Graph α T`, `ofDerivatives`, `norm_eq`, the component bounds and the time bound `‖u(t,x)‖ ≤ t‖uₜ‖`.
Print all of these before starting.

# Task duhamel-solution-operator-bound

Module: `Poincare/Global/DuhamelSolutionOperatorBound.lean`. Namespace: `Poincare.DuhamelSolutionOperatorBound`. Imports: `Poincare.Global.MovingLimitLeibniz`, `Poincare.Global.DuhamelParabolicHolderSeminorm`, `Poincare.Global.ParabolicSolutionGraph` (add what you need).

Objective: step L3's conclusion, the constant-coefficient solution operator is bounded from the Hölder carrier into the solution-graph space. Work in four independent groups; commit each lemma.

**Group 1: the time derivative.** From `duhamel_solves_heat_equation` and the landed Hessian bounds, prove the sup bound `|∂ₜu(t,x)| ≤ M + 3·C·K·t^{α/2}` and the parabolic Hölder bound `|∂ₜu(p) − ∂ₜu(q)| ≤ (K + 3·C·K)·parabolicDist p q ^ α`, where the Laplacian is the three-term coordinate trace of `D²u` so its bounds follow from the landed Hessian sup and parabolic Hölder bounds by the triangle inequality over the three basis directions (the landed `laplacian_eq_hessian_trace` in `HeatDuhamelHeatEquation.lean` gives the spelling).

**Group 2: the gradient.** Prove `‖Du(t,x)‖ ≤ 2·M·C₁·√t` for `t ∈ Icc 0 T` (integrate the landed `norm_gradient_heatSolution_le` majorant `M C₁ (t−s)^{−1/2}`), and a parabolic Hölder bound `‖Du(p) − Du(q)‖ ≤ C'·(M + K)·parabolicDist p q ^ α`. For the Hölder part, the cheapest correct route is interpolation from the landed Hessian sup bound and the gradient sup bound: in space, `‖Du(t,x) − Du(t,z)‖ ≤ min(2·sup‖Du‖, sup‖D²u‖·‖x−z‖)`, and `min(2A, B r) ≤ (2A)^{1−α} (B r)^{α} ≤ … ≤ C r^α` when `A` and `B` carry the right powers of `T ≤ 1`; in time, use the equation and the fundamental theorem of calculus on `s ↦ Du(s,x)` if a derivative bound is available, otherwise bound the time increment by the same interpolation applied to `u`. If the time-Hölder part of the gradient resists, land the spatial part and the sup bound and say so.

**Group 3: the value.** Prove `|u(t,x)| ≤ t·(M + 3·C·K·T^{α/2})` from group 1 and the landed graph time bound (or directly from the mean value inequality with the time derivative), and the parabolic Hölder bound for `u` by the same interpolation as group 2, using the gradient sup bound in space and the time-derivative sup bound in time.

**Group 4: assembly.** With `0 < α < 1` and `0 < T ≤ 1` fixed, and `f` given as an element of `Y α T ℝ` (so `M := ‖f‖` and `K := ‖f‖` both work as bounds through the landed `norm_le` and `holder_le`), build the four components with `ParabolicHolder.ofFunction` (multiply by the cylinder indicator so they vanish off the cylinder, as the carrier requires; the landed `ofFunction` takes the support condition and the two witnesses), assemble a `ParabolicSolutionGraph.Graph α T` with `ofDerivatives` using `duhamel_solves_heat_equation`, `contDiff_two_duhamel` and `hasFDerivAt_duhamel` for the relation fields, and prove the operator bound

```lean
theorem exists_solution_graph_bound :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y (E := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph (E := E) α T,
      (∀ p ∈ ParabolicHolder.cylinder (E := E) T,
        G.u p = ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2) ∧
      ‖G‖ ≤ C * ‖f‖
```

Probe this statement before proving it and adjust only the spelling, not the content.

Exact stop condition: as many of groups 1 to 4 as compile, with the gate passing on the module, and the report stating exactly which group resisted and at which goal. Group 1 and the sup bounds of groups 2 and 3 are expected to be reachable.
