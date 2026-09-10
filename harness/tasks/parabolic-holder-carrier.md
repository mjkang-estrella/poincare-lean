# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/parabolic-holder-carrier`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files, `Poincare.lean`, audit scripts, missions, or ledgers; you may add EXACTLY ONE new Lean module, `Poincare/Global/ParabolicHolderSpace.lean`. Commit each verified item on your branch; report actual command output to `harness/reports/parabolic-holder-carrier_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting statement and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only. Distinguish (a) proved in repo, (b) in Mathlib, (c) absent.

Context: read `HANDOFF.md` top section first.

# Task parabolic-holder-carrier

Read `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the norm choice `Y_T`, `X_T`) and section 3.2 first.

Objective: implement the parabolic Hölder carrier `Y_T` as a genuine complete normed space so that later tasks (K2, the frozen-coefficient correction, the nonlinear fixed point) can use Mathlib's Banach fixed point and bounded-operator theory on it.

Module: `Poincare/Global/ParabolicHolderSpace.lean`. Namespace: `Poincare.ParabolicHolder`. Imports: Mathlib only unless a landed definition is needed (`Poincare.Global.CompactCoefficientEllipticity` for `E`).

Required content, with `E := ClosedSmoothModel 3` (or general `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` and a target `{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]` if the generality costs nothing):

1. `parabolicDist (p q : ℝ × E) : ℝ := ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|` and its basic lemmas (nonneg, symm, zero iff equal on the cylinder is NOT needed).
2. The seminorm `holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ := ⨆ (p ∈ S) (q ∈ S) (_ : p ≠ q), ‖f p - f q‖ / parabolicDist p q ^ α` defined via `⨆` over a bounded family, or as `sSup` of the ratio set, with a predicate `HasHolderBound α S f K` meaning `∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * parabolicDist p q ^ α` (prefer building the space from the predicate: it avoids `⨆` pathologies).
3. The carrier: a structure `Y (α : ℝ) (T : ℝ) (F)` of functions `f : ℝ × E → F` that are bounded on the cylinder `S_T := Icc 0 T ×ˢ univ` and admit some Hölder bound there (store `∃ M, ∀ p ∈ S_T, ‖f p‖ ≤ M` and `∃ K, HasHolderBound α S_T f K`), with values outside `S_T` irrelevant: quotient by agreement on `S_T`, or simply require `f p = 0` for `p ∉ S_T` to make the norm definite (choose and justify; the second is simpler).
4. Instances: `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ` with norm `‖f‖ = sup_{S_T} ‖f‖ + [f]_{α;S_T}` (define both pieces as `sSup` of bounded nonempty sets or via `⨆` with `BddAbove` lemmas; prove the norm axioms), and `CompleteSpace` (a Cauchy sequence converges uniformly on `S_T` since the sup norm is dominated; the limit is bounded and Hölder with the limiting constant by passing to the limit in the pointwise inequality; convergence in the full norm follows from the same argument applied to differences). Use `BoundedContinuousFunction` completeness as a guide, not as a dependency (the elements are not required continuous; boundedness plus Hölder on `S_T` implies continuity on `S_T` anyway).
5. Bridging lemmas: `norm_le` (`‖f p‖ ≤ ‖f‖` on `S_T`), `holder_le` (`‖f p - f q‖ ≤ ‖f‖ * parabolicDist p q ^ α` on `S_T`), `mul_mem` for `F = ℝ` (product of two elements is an element with `‖f*g‖ ≤ 2‖f‖‖g‖` or the sharp constant), and `restrict_le` (the norm on `Y α T'` for `T' ≤ T` is bounded by the norm on `Y α T`).

Exact stop condition: the `CompleteSpace` instance and the five bridging lemmas compile and pass the gate. If `CompleteSpace` resists, land the normed space with the bridging lemmas and display the exact resisting limit-passing step.
