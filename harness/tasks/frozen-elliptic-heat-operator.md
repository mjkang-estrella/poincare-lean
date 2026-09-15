# Worker contract (Lean task, class B)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/frozen-elliptic-heat-operator`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file, `Poincare/Global/FrozenEllipticHeatOperator.lean`; commit each verified item on the branch; report actual command output to `harness/reports/frozen-elliptic-heat-operator_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first. The parabolic route's landed modules, all in `Poincare/Global/`: `ParabolicHolderSpace.lean` (namespace `Poincare.ParabolicHolder`: `Y α T F` complete normed space, `parabolicDist`, `cylinder`, `HasHolderBound`, `ofFunction`, `norm_eq`, `norm_le`, `holder_le`, `norm_le_of_bounds`, `norm_mul_le`, `restrict`), `ParabolicSolutionGraph.lean` (namespace `Poincare.ParabolicSolutionGraph`: `Graph α T` with fields `u ut du ddu zero_trace hasFDeriv hasFDeriv_du hasDeriv_time`, complete normed space, `ofDerivatives`, `norm_eq`, component bounds, `time_bound`), `DuhamelSolutionOperatorBound.lean` (namespace `Poincare.DuhamelSolutionOperatorBound`: `exists_solution_graph_bound` and the component estimates), `MovingLimitLeibniz.lean` (`duhamel_solves_heat_equation`), `HeatDuhamelHessianDifferentiation.lean` (`contDiff_two_duhamel`, `hasFDerivAt_duhamel`, `hessian_duhamel_eq_integral`), `ParametrixNeumannCorrection.lean` (`correctedInverse`, `comp_correctedInverse`, `exists_right_inverse` for `L : X →L Y`, `P : Y →L X`, `R : Y →L Y`, `‖R‖ < 1`). `E := ClosedSmoothModel 3`. Print every landed statement you rely on before using it.

# Task frozen-elliptic-heat-operator

Namespace: `Poincare.FrozenEllipticHeatOperator`. Imports: `Poincare.Global.DuhamelSolutionOperatorBound`, `Poincare.Global.CompactCoefficientEllipticity` (add what you need). Read `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.2, row L4, first.

Objective: step L4, the constant-coefficient inverse for a fixed symmetric positive definite coefficient matrix instead of the identity. With `Bilin := E →L[ℝ] E →L[ℝ] ℝ` and a symmetric `A : Bilin` with `λ‖v‖² ≤ A v v ≤ Λ‖v‖²` (`0 < λ ≤ Λ`), prove

```lean
theorem exists_frozen_solution_graph_bound :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ λ Λ : ℝ, 0 < λ → λ ≤ Λ →
  ∃ C : ℝ, 0 < C ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
    (∀ v, λ * ‖v‖^2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ f : ParabolicHolder.Y (E := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph (E := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i : Fin 3, ∑ j : Fin 3, A (e i) (e j) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖
```

with `e := EuclideanSpace.basisFun (Fin 3) ℝ` (probe and adjust spelling only).

Route: the change of variables. Let `S : E ≃L[ℝ] E` be a symmetric positive square root of `A` viewed as an operator (`A v w = ⟪S v, S w⟫`); obtain it from Mathlib's positive-semidefinite square root on `Matrix (Fin 3) (Fin 3) ℝ` (`Matrix.PosSemidef.sqrt` / `Matrix.PosDef` API in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`, transported by `Matrix.toEuclideanLin`; verify the exact names and that `sqrt` of a positive definite matrix is positive definite and symmetric), or by the spectral theorem for the self-adjoint operator (`LinearMap.IsSymmetric` diagonalization in finite dimension). Its operator norm and its inverse's satisfy `‖S‖ ≤ √Λ`, `‖S⁻¹‖ ≤ 1/√λ`. Set `g(t, y) := f(t, S y)`; then `‖g‖_Y ≤ max(1, ‖S‖^α) ‖f‖_Y` (the cylinder is preserved, the sup is unchanged, the Hölder seminorm scales by `‖S‖^α`). Apply the landed `exists_solution_graph_bound` to `g` to get `H`, and set `u(t, x) := H.u(t, S⁻¹ x)`, with `du(t,x) = H.du(t, S⁻¹x) ∘ S⁻¹`, `ddu(t,x) = H.ddu(t, S⁻¹x) ∘ (S⁻¹ × S⁻¹)`, `ut(t,x) = H.ut(t, S⁻¹x)`. Prove the chain rule identities (`HasFDerivAt.comp` with the continuous linear map `S⁻¹`), that `∑ᵢⱼ A(eᵢ,eⱼ) ddu(eᵢ,eⱼ) = trace of H.ddu` (this is the algebraic identity `∑ᵢⱼ ⟪S eᵢ, S eⱼ⟫ H(S⁻¹eᵢ, S⁻¹eⱼ) = ∑ₖ H(eₖ, eₖ)`, i.e. trace invariance under the orthonormal change; prove it with `LinearMap.trace` or directly by expanding in the basis), and the norm comparison `‖G‖ ≤ max(1, ‖S⁻¹‖²)·max(1, ‖S⁻¹‖^α)·‖H‖` (each component's sup and Hölder seminorm scale by explicit powers of `‖S⁻¹‖`). Assemble `G` with `ofDerivatives`.

Exact stop condition: the displayed theorem passes the gate; or a blocked report displaying exactly which of (square root, transformed forcing bound, chain rule, trace identity, norm comparison) resisted, with the others committed.
