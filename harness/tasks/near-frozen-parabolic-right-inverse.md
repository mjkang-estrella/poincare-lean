# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/near-frozen-parabolic-right-inverse`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file, `Poincare/Global/NearFrozenParabolicRightInverse.lean`; commit each verified item on the branch; report actual command output to `harness/reports/near-frozen-parabolic-right-inverse_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep; record every probe with actual output. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first. Landed, all in `Poincare/Global/`: `FrozenEllipticHeatOperator.lean` (namespace `Poincare.FrozenEllipticHeatOperator`: `mapHolder`, `norm_mapHolder_le`, `mapGraph`, `norm_mapGraph_le`, `trace_pullback`, `exists_symmetric_factor`, `factor_norm_bounds`, `exists_frozen_solution_graph_bound`), `NearIdentityParabolicRightInverse.lean` (namespace `Poincare.NearIdentityParabolicRightInverse`: `multiplier`, `errorOp`, `errorOp_small`, `coeff`, `nearIdentityInverse`, `nearIdentityInverse_solves`, `nearIdentityInverse_norm_le`, `exists_nearIdentity_solution`), `DuhamelSolutionOperatorCLM.lean`, `ParabolicHolderMultiplier.lean`, `ParabolicHolderSpace.lean`, `ParabolicSolutionGraph.lean`. `E := ClosedSmoothModel 3`, `Bilin := E →L[ℝ] E →L[ℝ] ℝ`, `e := EuclideanSpace.basisFun (Fin 3) ℝ`. Print every statement you rely on.

# Task near-frozen-parabolic-right-inverse

Namespace: `Poincare.NearFrozenParabolicRightInverse`. Imports: `Poincare.Global.FrozenEllipticHeatOperator`, `Poincare.Global.NearIdentityParabolicRightInverse` (add what you need).

Objective: the chart-level local solver the finite-atlas parametrix will use: solvability of `∂ₜu = f + Σᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` on a short cylinder when the coefficients `a = A₀ + b` are a small Hölder perturbation of a fixed symmetric positive-definite form `A₀` with `λ‖v‖² ≤ A₀ v v ≤ Λ‖v‖²`.

Target:

```lean
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ λ Λ : ℝ, 0 < λ → λ ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, λ * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y (E := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder (E := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder (E := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y (E := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph (E := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖
```

(probe and adjust spelling only; the quantifier order — `C ε₀ τ₀` before `A₀`, `T`, `b`, `f` — is the content).

Route: change variables with the symmetric factor `S` of `A₀` from `exists_symmetric_factor` (so `A₀ = Sᵀ S` in the sense `A₀ v w = ⟪S v, S w⟫`). Under `x = S⁻¹ y` (as in L4), the operator `∂ₜ − Σ (A₀ + b)ᵢⱼ ∂ᵢ∂ⱼ` becomes `∂ₜ − Σ (δᵢⱼ + b'ᵢⱼ) ∂ᵢ∂ⱼ` with `b'ᵢⱼ(t, y) = Σₖₗ (S⁻¹)ₖᵢ (S⁻¹)ₗⱼ bₖₗ(t, S⁻¹ y)`-type transformed coefficients (derive the exact formula from `trace_pullback`'s algebra; it is the same bilinear pullback applied to the perturbation), whose sup and Hölder bounds are the originals times explicit powers of `‖S⁻¹‖ ≤ 1/√λ` and `‖S‖ ≤ √Λ` (`norm_mapHolder_le`). Choose `ε₀` so that the transformed sup bound satisfies `9 C_S ε' ≤ 1/4` and `τ₀ ≤ 1` so that `9 C_S Λ' T^{α/2} ≤ 1/4`; apply `exists_nearIdentity_solution` to the transformed forcing `mapHolder … f`; pull the graph back with `mapGraph`; verify the equation with `trace_pullback` (the mixed terms `Σ (A₀ + b)ᵢⱼ ∂ᵢ∂ⱼ u` transform to `Σ (δ + b')ᵢⱼ ∂ᵢ∂ⱼ u'` exactly as in L4's proof, now with the perturbation carried along), and the norm bound with `norm_mapGraph_le` and `norm_mapHolder_le`.

Also land the operator form if cheap: `nearFrozenInverse : Y →L Graph` with the same equation and `‖·‖ ≤ C`, built from `nearIdentityInverse` conjugated by the (linear) change-of-variables maps `mapHolder` and `mapGraph` (both are continuous linear maps between the carriers if `mapHolder`/`mapGraph` were defined as such; if they are plain functions, prove linearity or skip the operator form and say so).

Exact stop condition: the existence theorem passes the gate; the operator form is optional. A blocked report must display the exact resisting step (expected friction: the transformed coefficient formula and its Hölder bound).
