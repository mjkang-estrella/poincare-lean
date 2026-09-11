# Worker contract (Lean task, small)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/duhamel-parabolic-holder-seminorm`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; commit each verified lemma on the branch; report actual command output to `harness/reports/duhamel-parabolic-holder-seminorm_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep; record every probe with actual output. Frozen contract files are read-only.

Context: this is a short combination task, not a new estimate. Read `HANDOFF.md` top section. Landed, all in `Poincare/Global/`: `HeatDuhamelHessianSpatialHolder.lean` (`duhamel_hessian_spatial_holder`: the Duhamel Hessian difference at a fixed time is at most `C·K·‖x−z‖^α`), `HeatDuhamelHessianTimeHolder.lean` (`duhamel_hessian_time_holder`: at a fixed point it is at most `C·K·|t₁−t₂|^{α/2}`), `HeatDuhamelHessianDifferentiation.lean` (`duhamel_hessian_bound`: sup bound `C·K·t^{α/2}`), and `ParabolicHolderSpace.lean` (namespace `Poincare.ParabolicHolder`: `parabolicDist p q = ‖p.2 − q.2‖ + Real.sqrt |p.1 − q.1|`, `HasHolderBound`, `cylinder`). Print all four statements before starting.

# Task duhamel-parabolic-holder-seminorm

Module: `Poincare/Global/DuhamelParabolicHolderSeminorm.lean`. Namespace: `Poincare.DuhamelParabolicHolderSeminorm`. Imports: `Poincare.Global.HeatDuhamelHessianTimeHolder`, `Poincare.Global.HeatDuhamelHessianSpatialHolder`, `Poincare.Global.ParabolicHolderSpace` (add what you need).

Objective: combine the two landed one-variable estimates into the genuine parabolic Hölder bound, and express it with the landed predicate.

```lean
theorem duhamel_hessian_parabolic_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder (E := E) T, ∀ q ∈ ParabolicHolder.cylinder (E := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α
```

Proof: take `C₁` from the spatial theorem and `C₂` from the time theorem and set `C := C₁ + C₂`. Insert the intermediate point `(p.1, q.2)`: the spatial theorem at time `p.1` bounds the first difference by `C₁ K ‖p.2 − q.2‖^α`, the time theorem at the point `q.2` bounds the second by `C₂ K |p.1 − q.1|^{α/2}`. Then `‖p.2 − q.2‖ ≤ parabolicDist p q` and `Real.sqrt |p.1 − q.1| ≤ parabolicDist p q`, both nonnegative, so by `Real.rpow_le_rpow` (with `0 ≤ α`) each term is at most `K · Cᵢ · parabolicDist p q ^ α`; use `Real.sqrt_eq_rpow` and `Real.rpow_natCast`/`Real.rpow_mul` to rewrite `|p.1 − p.1|^{α/2}` as `(Real.sqrt |p.1 − q.1|)^α`. Watch that all the exponents are `Real.rpow`, not monoid powers.

Then add the corollary in the landed predicate form:

```lean
theorem hasHolderBound_duhamel_hessian :
  <same binders> →
  ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder (E := E) T)
    (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K)
```

matching the landed `HasHolderBound` definition exactly (print it first).

Exact stop condition: both theorems compile with the displayed statements and pass the gate. If the exponent rewriting resists, land the first theorem and display the exact resisting rewrite.
