# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/near-identity-parabolic-right-inverse`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file, `Poincare/Global/NearIdentityParabolicRightInverse.lean`; commit each verified item on the branch; report actual command output to `harness/reports/near-identity-parabolic-right-inverse_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep; record every probe with actual output. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section first. Landed, all in `Poincare/Global/`: `DuhamelSolutionOperatorCLM.lean` (namespace `Poincare.DuhamelSolutionOperatorCLM`: `duhamelOperator α T hα hα1 hT hT1 : Y α T ℝ →L[ℝ] Graph α T`, `duhamelOperator_u`, `duhamelOperator_norm_le` (a constant `C_S(α)` uniform in `T ≤ 1`), `duhamelOperator_solves` (`ut = f + Σᵢ ddu eᵢ eᵢ` on the cylinder), `Graph.ext_of_u`), `ParabolicHolderMultiplier.lean` (namespace `Poincare.ParabolicHolderMultiplier`: `entry`, `norm_mul_split`, `forcing b G : Y α T ℝ` with `forcing_apply` / `forcing_eq_sum` (`Σᵢⱼ bᵢⱼ(p)·G.ddu p eᵢ eⱼ`), `norm_forcing_le`, `norm_error_le`, `error_small`), `ParametrixNeumannCorrection.lean` (namespace `Poincare.ParametrixNeumannCorrection`: `correctedInverse`, `comp_correctedInverse`, `exists_right_inverse`), `ParabolicSolutionGraph.lean`, `ParabolicHolderSpace.lean`. `E := ClosedSmoothModel 3`, `e := EuclideanSpace.basisFun (Fin 3) ℝ`. Print every statement you rely on.

# Task near-identity-parabolic-right-inverse

Namespace: `Poincare.NearIdentityParabolicRightInverse`. Imports: `Poincare.Global.DuhamelSolutionOperatorCLM`, `Poincare.Global.ParabolicHolderMultiplier`, `Poincare.Global.ParametrixNeumannCorrection` (add what you need).

Objective: solvability of the variable-coefficient parabolic equation `∂ₜu = f + Σᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` on a short cylinder when the coefficients are Hölder and close to the identity, by correcting the constant-coefficient inverse. Fix `0 < α < 1`, `0 < T ≤ 1`, and coefficient perturbations `b : Fin 3 → Fin 3 → Y α T ℝ` (so `aᵢⱼ = δᵢⱼ + bᵢⱼ`).

1. **The multiplier as a continuous linear map.** Define `multiplier b : Graph α T →L[ℝ] Y α T ℝ` with `multiplier b G = forcing b G` (prove `forcing` is additive and homogeneous in `G` — it is a finite sum of products of fixed carrier elements with entries of `G.ddu`, and entries are linear in `G`; use `Graph.ext_of_u`-free reasoning: the carrier's `ext` on cylinder values suffices), and its bound `‖multiplier b‖ ≤ 9(ε + Λ T^{α/2})` under `supNorm (b i j) ≤ ε`, `holderSeminorm (b i j) ≤ Λ` (from the landed `norm_forcing_le`).

2. **The error operator.** `errorOp b := (multiplier b).comp (duhamelOperator …) : Y →L Y`, with `‖errorOp b‖ ≤ 9 C_S (ε + Λ T^{α/2})`, hence `‖errorOp b‖ ≤ 1/2 < 1` under `9C_Sε ≤ 1/4`, `9C_SΛT^{α/2} ≤ 1/4`.

3. **The corrected inverse.** `nearIdentityInverse b … : Y →L Graph := (duhamelOperator …).comp (Units.oneSub (errorOp b) h)⁻¹` (or literally `ParametrixNeumannCorrection.correctedInverse` with `P := duhamelOperator`, `R := errorOp b`), and the theorem that it solves the variable-coefficient equation:

```lean
theorem nearIdentityInverse_solves (…) (f : Y α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearIdentityInverse b … f).ut (t, x) =
        f (t, x) + ∑ i, ∑ j, (if i = j then 1 else 0 + b i j (t, x)) *
          (nearIdentityInverse b … f).ddu (t, x) (e i) (e j)
```

(spell the identity-plus-perturbation coefficient however is cleanest, e.g. as `(1 + b i i)` on the diagonal and `b i j` off it, and state it once as a definition `coeff b i j`), proved from `duhamelOperator_solves` applied to `g := (Units.oneSub R h)⁻¹ f` together with the identity `g = f + errorOp b g` (that is `(Id − R) g = f`), and `forcing_apply`. Also `nearIdentityInverse_norm_le : ‖nearIdentityInverse b …‖ ≤ 2 C_S` from `‖(1 − R)⁻¹‖ ≤ 1/(1 − ‖R‖) ≤ 2` (Mathlib: `Units.oneSub` / `NormedRing.inverse_one_sub_norm` / `norm_inverse_one_sub_le`-type lemmas; grep). Note the operator `L u := uₜ − Σ aᵢⱼ ∂ᵢ∂ⱼu` need not be defined as a CLM on `Graph`; the pointwise equation is the deliverable.

4. **Existence form.** `exists_nearIdentity_solution`: for such `b`, every `f ∈ Y α T ℝ` has a `G : Graph α T` with the equation of item 3 and `‖G‖ ≤ 2 C_S ‖f‖`.

Exact stop condition: items 1 to 4 pass the gate; or a blocked report naming which item resisted at which goal, with the others committed. Item 1 (linearity of the forcing) is the only expected friction.
