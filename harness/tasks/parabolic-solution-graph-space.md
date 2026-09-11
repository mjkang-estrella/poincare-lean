# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/parabolic-solution-graph-space`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/parabolic-solution-graph-space_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting step and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the `Y_T` / `X_T` norm choice) and 3.2 (step L0) first. Landed: `Poincare/Global/ParabolicHolderSpace.lean` (namespace `Poincare.ParabolicHolder`: `parabolicDist`, `cylinder`, `HasHolderBound`, `holderSeminorm`, `supNorm`, the carrier `Y α T F` as a closed submodule of an lp product with `NormedAddCommGroup`, `NormedSpace ℝ`, `CompleteSpace`, the constructor `ofFunction`, `norm_eq`, `norm_le`, `holder_le`, `norm_le_of_bounds`, `exists_rep_iff`, `norm_mul_le`, `restrict`, `restrict_le`). Study that module's representation before designing yours; reuse `ofFunction` and `norm_le_of_bounds` rather than re-deriving bounds.

# Task parabolic-solution-graph-space

Module: `Poincare/Global/ParabolicSolutionGraph.lean`. Namespace: `Poincare.ParabolicSolutionGraph`. Imports: `Poincare.Global.ParabolicHolderSpace` (add what you need).

Objective: the solution-graph space `X α T` of step L0, the domain carrier for the constant-coefficient inverse and the nonlinear fixed point. Its elements are genuine derivative graphs with zero initial trace whose four components lie in the landed Hölder carrier.

With `E := ClosedSmoothModel 3` (or general `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]` if that costs nothing) and real values:

1. `structure Graph (α T : ℝ)` with fields `u : Y α T ℝ`, `ut : Y α T ℝ`, `du : Y α T (E →L[ℝ] ℝ)`, `ddu : Y α T (E →L[ℝ] E →L[ℝ] ℝ)` and the relation fields, all stated on the cylinder `Icc 0 T ×ˢ univ`:
   - `zero_trace : ∀ x : E, u (0, x) = 0`
   - `hasFDeriv : ∀ t ∈ Icc 0 T, ∀ x : E, HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x`
   - `hasFDeriv_du : ∀ t ∈ Icc 0 T, ∀ x : E, HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x`
   - `hasDeriv_time : ∀ t ∈ Icc 0 T, ∀ x : E, HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t`
   (use `HasDerivWithinAt` on the closed interval so the endpoints are covered; if a two-sided `HasDerivAt` is cleaner because elements vanish off the cylinder, justify the choice in the report.)
2. Instances: `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ` with `‖G‖ = ‖G.u‖ + ‖G.ut‖ + ‖G.du‖ + ‖G.ddu‖`, and `CompleteSpace`. Build the algebra by transporting from the product `Y × Y × Y × Y` (the relation fields are closed conditions: a limit of graphs is a graph, because uniform convergence of the functions and their derivatives on the cylinder passes to the limit — use Mathlib's `hasFDerivAt_of_tendstoUniformlyOn` / `HasFDerivAt.of_tendsto...` family, or realize `X` as a closed submodule of the product exactly as `ParabolicHolderSpace` realized `Y` inside its lp product, which is the recommended route).
3. Bridging lemmas: `norm_u_le`, `norm_ut_le`, `norm_du_le`, `norm_ddu_le` (each component's norm is at most `‖G‖`); `sup_le` and `holder_le` for each component on the cylinder; and the time bound from the zero trace: `∀ t ∈ Icc 0 T, ∀ x, ‖G.u (t, x)‖ ≤ t * ‖G.ut‖` (mean value inequality on `[0, t]` from the derivative field).
4. A constructor `ofDerivatives` taking the four raw functions with the support condition off the cylinder, the bound and Hölder witnesses, and the relation proofs, returning a `Graph`.

Exact stop condition: the `CompleteSpace` instance, the four bridging norm lemmas, the zero-trace time bound, and the constructor compile and pass the gate. If `CompleteSpace` resists, land the normed space with all bridging lemmas and display the exact resisting limit-passing step for the derivative relations.
