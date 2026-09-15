# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/duhamel-solution-operator-clm`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file, `Poincare/Global/DuhamelSolutionOperatorCLM.lean`; commit each verified item on the branch; report actual command output to `harness/reports/duhamel-solution-operator-clm_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first. The parabolic route's landed modules, all in `Poincare/Global/`: `ParabolicHolderSpace.lean` (namespace `Poincare.ParabolicHolder`: `Y α T F` complete normed space, `parabolicDist`, `cylinder`, `HasHolderBound`, `ofFunction`, `norm_eq`, `norm_le`, `holder_le`, `norm_le_of_bounds`, `norm_mul_le`, `restrict`), `ParabolicSolutionGraph.lean` (namespace `Poincare.ParabolicSolutionGraph`: `Graph α T` with fields `u ut du ddu zero_trace hasFDeriv hasFDeriv_du hasDeriv_time`, complete normed space, `ofDerivatives`, `norm_eq`, component bounds, `time_bound`), `DuhamelSolutionOperatorBound.lean` (namespace `Poincare.DuhamelSolutionOperatorBound`: `exists_solution_graph_bound` and the component estimates), `MovingLimitLeibniz.lean` (`duhamel_solves_heat_equation`), `HeatDuhamelHessianDifferentiation.lean` (`contDiff_two_duhamel`, `hasFDerivAt_duhamel`, `hessian_duhamel_eq_integral`), `ParametrixNeumannCorrection.lean` (`correctedInverse`, `comp_correctedInverse`, `exists_right_inverse` for `L : X →L Y`, `P : Y →L X`, `R : Y →L Y`, `‖R‖ < 1`). `E := ClosedSmoothModel 3`. Print every landed statement you rely on before using it.

# Task duhamel-solution-operator-clm

Namespace: `Poincare.DuhamelSolutionOperatorCLM`. Imports: `Poincare.Global.DuhamelSolutionOperatorBound` (add what you need).

Objective: package the constant-coefficient inverse as a continuous linear map, the form `ParametrixNeumannCorrection` consumes. For fixed `0 < α < 1` and `0 < T ≤ 1`:

```lean
def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ParabolicHolder.Y (E := E) α T ℝ →L[ℝ] ParabolicSolutionGraph.Graph (E := E) α T

theorem duhamelOperator_u (…) (f) : ∀ p ∈ ParabolicHolder.cylinder (E := E) T,
    (duhamelOperator α T hα hα1 hT hT1 f).u p =
      ∫ s in (0:ℝ)..p.1, Poincare.heatSolution (p.1 - s) (fun y => f (s, y)) p.2

theorem duhamelOperator_norm_le : ∀ α, 0 < α → α < 1 → ∃ C, 0 < C ∧ ∀ T, 0 < T → T ≤ 1 →
    ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ C

theorem duhamelOperator_solves (…) (f) : ∀ t ∈ Icc 0 T, ∀ x,
    (duhamelOperator … f).ut (t, x) = f (t, x) + <the three-term coordinate trace of (duhamelOperator … f).ddu (t, x)>
```

(adjust spelling after probing; the trace spelling must match `duhamel_solves_heat_equation` / `laplacian_eq_hessian_trace`).

Route. First a uniqueness lemma for graphs: `Graph.ext_of_u : G.u = H.u → G = H`. Reason: `du` is determined on the cylinder by `hasFDeriv` (uniqueness of the Fréchet derivative, `HasFDerivAt.unique`), `ddu` by `hasFDeriv_du`, `ut` by `hasDeriv_time` on `Icc 0 T` (`HasDerivWithinAt.unique` with `uniqueDiffWithinAt_Icc` for `T > 0`), and all components vanish off the cylinder by the carrier's support condition; conclude with the carrier's `ext`. Then define the underlying map `f ↦ Classical.choose (exists_solution_graph_bound … f)` (or better, factor the explicit assembly out of the landed proof as a `def duhamelGraph`), prove additivity and homogeneity through `Graph.ext_of_u` from linearity of the Duhamel integral in `f` (`intervalIntegral.integral_add`, `integral_smul`, and linearity of `heatSolution` in its data, which the landed convolution lemmas should give or which follows from `integral_add`), and build the CLM with `LinearMap.mkContinuous` and the landed bound. The norm bound is `LinearMap.mkContinuous_norm_le`.

Exact stop condition: the definition and the three theorems pass the gate. If `Graph.ext_of_u` resists at the time-derivative endpoint, display the exact goal and land the rest with the extensionality as an explicit hypothesis, clearly marked as partial.
