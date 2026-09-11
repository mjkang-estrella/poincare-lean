# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/moving-limit-leibniz-rule`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/moving-limit-leibniz-rule_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every Mathlib name by grep in `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/heat-duhamel-heat-equation_blocked.md` in full (its verified-progress table, the exact remaining goal, and the "routes examined" section) first. Landed: `Poincare/Global/HeatDuhamelHeatEquation.lean` (namespace `Poincare.HeatDuhamelHeatEquation`, 11 theorems: `laplacian_eq_hessian_trace`, `intervalIntegrable_heat_hessian`, `intervalIntegrable_heat_laplacian`, `laplacian_duhamel_eq_integral`, `hasDerivAt_heat_integrand`, `heatSolution_sq`, `continuousOn_rescaled_heat_integral`, `continuousOn_heat_integrand_extension`, `tendsto_heat_integrand_diagonal`, `duhamel_time_derivative_integral`, `duhamel_zero`). Everything the final assembly needs is proved except one general calculus lemma.

# Task moving-limit-leibniz-rule

Module: `Poincare/Global/MovingLimitLeibniz.lean`. Namespace: `Poincare.MovingLimitLeibniz`. Imports: `Poincare.Global.HeatDuhamelHeatEquation` (add Mathlib imports as needed).

This task has two parts; part A is a self-contained real-analysis lemma with no geometry in it, part B applies it.

**Part A: the Leibniz rule for a moving upper limit with a parameter-dependent integrand.** State and prove a general lemma of the following shape (adjust the hypothesis spelling to what the proof actually needs, but keep the conclusion and do not add hypotheses the application cannot supply; probe your statement first):

```lean
theorem hasDerivWithinAt_integral_moving_limit
    {F : ℝ → ℝ → ℝ} {∂F : ℝ → ℝ → ℝ} {b T t : ℝ} (ht : t ∈ Icc 0 T)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
    (hdiag : Tendsto (fun s => F t s) (nhdsWithin t (Ico 0 t)) (nhds b))
    (hderiv : ∀ s ∈ Ioo 0 t, ∀ r ∈ Icc 0 T, s < r → HasDerivAt (fun ρ => F ρ s) (∂F r s) r)
    (hint : ∀ r ∈ Icc 0 T, IntervalIntegrable (fun s => ∂F r s) volume 0 r)
    <a local uniform domination hypothesis for ∂F near t, stated so the landed heat bounds supply it> :
    HasDerivWithinAt (fun r : ℝ => ∫ s in (0:ℝ)..r, F r s)
      (b + ∫ s in (0:ℝ)..t, ∂F t s) (Icc 0 T) t
```

Route: write the difference quotient at `t` with increment `h` as the sum of the boundary piece `(1/h) ∫_t^{t+h} F(t+h, s) ds`, which tends to `b` by `hdiag` and continuity, and the interior piece `(1/h) ∫_0^t [F(t+h,s) − F(t,s)] ds`, which tends to `∫_0^t ∂F(t,s) ds` by the mean value theorem in `r` plus dominated convergence with the local domination hypothesis. Handle `h < 0` and `h > 0` symmetrically, and the endpoints `t = 0`, `t = T` through the `Icc` neighbourhood filter. Look first for an existing Mathlib lemma in this family (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `intervalIntegral.integral_hasDerivAt_right`, `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) and compose them rather than reproving from scratch: the standard trick is to write `∫_0^r F(r,s) ds = G(r, r)` for `G(ρ, r) := ∫_0^r F(ρ, s) ds` and differentiate the composition, using `HasDerivAt.comp`-style chain rules with the partial derivatives in each slot (`integral_hasDerivAt_right` for the second slot, the dominated theorem for the first). Record which route compiled.

**Part B: finish the frozen K2 companion.** Apply part A with `F r s := heatSolution (r − s) (f(s,·)) x`, `∂F r s := deriv (fun ρ => heatSolution (ρ − s) (f(s,·)) x) r`, `b := f(t,x)`, using the landed `continuousOn_heat_integrand_extension`, `tendsto_heat_integrand_diagonal`, `hasDerivAt_heat_integrand`, `duhamel_time_derivative_integral` and the K1/K2 majorants for the domination, and prove the frozen statement

```lean
theorem duhamel_solves_heat_equation : <the exact statement of harness/tasks/heat-duhamel-heat-equation.md>
```

copying that statement verbatim from the task file.

Exact stop condition: part A compiles and passes the gate, and part B is landed if reachable. Landing part A alone, with the exact resisting application step displayed, is a success; neither is blocked.
