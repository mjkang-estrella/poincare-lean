# Near-frozen parabolic right inverse proved

Date: 2026-09-15. Worker result awaiting independent orchestrator review.

- Branch: `worker/near-frozen-parabolic-right-inverse`.
- Base: `571442448b8afd8484cd770e22944f54daec05e5`.
- Verified proof head: `5c1f77a4c417fd194622b3a7b5b989609c045da9`.
- Single new Lean file: `Poincare/Global/NearFrozenParabolicRightInverse.lean`.
- Existing Lean files, root imports, task contract, and frozen contracts are unchanged.
- Required first reads completed: handoff top, README, project map, task, and all six named context modules with their direct imports. Initial worktree was clean at the recorded base.

## Result

The exact `Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_solution`
passes the literal task-type assignment. The only lexical adjustments in that
probe escape the reserved `λ` token and the named `E` argument under local notation.
Its constants precede `A₀`, `T`, `b`, and `f` exactly as requested. The equation
holds on `Icc 0 T`; the graph carries the genuine derivatives and zero initial trace.

The optional operator result is also proved:
`exists_nearFrozen_operator` chooses a bounded linear solution operator before the
forcing, with the same uniform constants and equation. `nearFrozenInverse` is the
explicit Neumann correction of a supplied frozen linear inverse; its equation and
norm bound are `nearFrozenInverse_solves` and `nearFrozenInverse_norm_le`.
The unconditional operator theorem supplies the frozen inverse from ellipticity.

## Proof route and constants

This proof makes an explicit route adjustment without changing the target.
It uses the symmetric factor and the landed change-of-variables maps to construct
the frozen linear inverse. It then applies the original-coefficient multiplier
estimate to that inverse. It does not introduce transformed coefficients or invoke
`exists_nearIdentity_solution`. Thus the optional operator is built using the
landed Neumann correction, not by conjugating `nearIdentityInverse`.

Write `C_S = boundConstant α hα hα1`, `q = 1 / sqrt λ`, and

```text
D = max(1, q²) * max(1, q^α) * C_S * max(1, (sqrt Λ)^α).
C = 2 D,     ε₀ = 1 / (36 D),     τ₀ = 1.
```

For the symmetric factor `S`, the frozen inverse is
`graphPullback S.symm ∘ duhamelOperator ∘ holderPullback S`.
In coordinates the transformed forcing is `f(t, S y)` and the solution pulls
back by `y = S.symm x`. The landed `trace_pullback` proves the frozen equation;
`factor_norm_bounds` supplies the uniform distortion bound `D`.

For `R = multiplier b ∘ P`, the landed split estimate gives
`‖R‖ ≤ 9 D (ε₀ + Λb T^(α/2)) ≤ 1/2`.
The corrected operator is `P ∘ (Id - R)⁻¹` and has norm at most `2 D`.
The correction identity adds the original `b` sum to the original frozen `A₀`
sum directly, retaining the exact coefficient equation and all hypotheses.

## Verification

All final Lean commands use the pinned toolchain and Mathlib revision
`7175569c842f9164564bd76ff8b207e7b4705522`.
The process environment exports
`DEVELOPER_DIR=/Library/Developer/CommandLineTools` and `LEAN_NUM_THREADS=1`.
This is necessary on this machine because the default Xcode Git launcher refuses
to run pending its license prompt. No license was accepted or system setting changed.

| Check | Actual result |
| --- | --- |
| `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean` | Exit 0, empty output; transcript 026 |
| Forbidden-token scan including `opaque` | Exit 1, empty output, hence no matches; transcript 027 |
| Imported literal target assignment | Exit 0, empty output; transcript 025 |
| Entire emitted module, including generated declarations outside the task namespace | Exit 0; all 26 declarations have exactly `[propext, Classical.choice, Quot.sound]`; transcript 023 |
| `git diff --check` and `git diff --check 571442448b8afd8484cd770e22944f54daec05e5` | Exit 0, empty output; transcripts 028 and 029 |
| Lean file scope | Exactly one added Lean file; transcript 030 |
| Root and frozen-contract diff | Exit 0, empty output; transcript 031 |

The module-wide check also finds the generated
`Poincare.DuhamelSolutionOperatorCLM.duhamelOperator.congr_simp` declaration.
It is included among the 26 checked declarations. The earlier namespace-only
checks count 25 and are not the final acceptance evidence.

## Commits

```text
5c1f77a4 fix: remove notation metadata for exact module dependency gate
e5aeb288 feat: prove uniform near-frozen parabolic solvability and operator bound
4e4226c8 feat: correct frozen inverse for small Holder coefficient perturbations
c298c25b feat: bound frozen elliptic inverse uniformly by ellipticity
d019de04 feat: construct frozen elliptic continuous linear solution operator
```

## Failed probes and recovery

All compiler probes, including failures and the removed warning, are preserved
below with actual output and source snapshots.

- Probes 001 and 002 failed before elaboration. Lake reported a URL change,
  removed this worktree's Mathlib copy, and failed to clone because its Git
  subprocess hit the Xcode license check. A private copy was restored using
  `cp -cR /private/tmp/poincare-workers/hamilton-eta-core-reduction/.lake/packages/mathlib .lake/packages/mathlib`.
  The source copy was read only. Its exact revision and origin were checked;
  transcript 033 rechecks the restored copy. Subsequent subprocesses select the
  existing Command Line Tools through `DEVELOPER_DIR`.
- Probe 004 exposed the parser collision between local notation `E` and named
  arguments. Escaping the binder names fixed it.
- Probe 006 failed because the quoted Lean name needed parentheses before
  `.isPrefixOf`. The audit script was corrected.
- Probe 013 passed with an unnecessary-sequence-focus warning; probe 014 is clean.
- Probe 019 used the stronger module-wide audit and caught local-notation
  metaprogram declarations with empty foundational dependencies. All three local
  notations were removed. Probe 023 checks every declaration of the resulting
  module, with no namespace filter or exception.
- Transcript 018 records basename grep candidates. Some generic Mathlib names
  occur in several namespaces; these first matches alone are not namespace
  provenance. Fully qualified `#print` statements resolve the actual names, and
  transcripts 021 and 022 record focused source matches for the ambiguous APIs.
- An initial `git add` and `git commit` attempt without `DEVELOPER_DIR` each
  emitted the following diagnostic and the combined command exited 69:

```text
You have not agreed to the Xcode license agreements. Please run 'sudo xcodebuild -license' from within a Terminal window to review and agree to the Xcode and Apple SDKs license.
You have not agreed to the Xcode license agreements. Please run 'sudo xcodebuild -license' from within a Terminal window to review and agree to the Xcode and Apple SDKs license.
```

The commits listed above succeeded after selecting the installed Command Line Tools.

## Handoff

The task's existence stop condition is met. This worker does not merge or accept
its own result. Root integration and full-project audits remain the orchestrator's
responsibility; no full build or root audit was launched by this worker.

First action in this worktree:

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Then independently reproduce the imported-target and module-audit probes below
against the recorded base and proof diff before deciding acceptance.

## Command transcript

The runner records stdout and stderr together and the actual exit code. Empty
output is represented by an empty fenced block. Probe snapshots are deduplicated
by SHA-256 in the source appendix. The first two probes predate the
`DEVELOPER_DIR` environment fix; all later runner calls use it.

<details>
<summary>001-dependencies</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/dependencies.lean
```

Source snapshot: `001-dependencies_dependencies.lean`, SHA-256 `8c22754bb27333e58a449a0b29b90171c2b2505af72658c9ae1c2c285d87abf7`.

```text
info: mathlib: URL has changed; deleting '/private/tmp/poincare-workers/near-frozen-parabolic-right-inverse/.lake/packages/mathlib' and cloning again
info: mathlib: cloning https://github.com/leanprover-community/mathlib4.git
info: stderr:
You have not agreed to the Xcode license agreements. Please run 'sudo xcodebuild -license' from within a Terminal window to review and agree to the Xcode and Apple SDKs license.
error: external command 'git' exited with code 69
```

Exit code: `1`.

</details>

<details>
<summary>002-pullbacks</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `002-pullbacks_NearFrozenParabolicRightInverse.lean`, SHA-256 `9c6f9590d306bf2753bf02b976209960ce3948c038ddb312ac5f25882fc3a45d`.

```text
info: mathlib: cloning https://github.com/leanprover-community/mathlib4.git
info: stderr:
You have not agreed to the Xcode license agreements. Please run 'sudo xcodebuild -license' from within a Terminal window to review and agree to the Xcode and Apple SDKs license.
error: external command 'git' exited with code 69
```

Exit code: `1`.

</details>

<details>
<summary>003-dependencies</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/dependencies.lean
```

Source snapshot: `003-dependencies_dependencies.lean`, SHA-256 `8c22754bb27333e58a449a0b29b90171c2b2505af72658c9ae1c2c285d87abf7`.

```text
def Poincare.FrozenEllipticHeatOperator.mapHolder.{u_1, u_2} : {F : Type u_1} →
  {F' : Type u_2} →
    [inst : NormedAddCommGroup F] →
      [inst_1 : NormedSpace ℝ F] →
        [inst_2 : NormedAddCommGroup F'] →
          [inst_3 : NormedSpace ℝ F'] →
            {α T : ℝ} →
              0 ≤ α →
                (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) →
                  (F →L[ℝ] F') → Poincare.ParabolicHolder.Y α T F → Poincare.ParabolicHolder.Y α T F' :=
fun {F} {F'} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] {α T} hα S Q f =>
  Poincare.ParabolicHolder.ofFunction (fun p => Q (↑(WithLp.fst ↑f) (p.1, S p.2))) ⋯ ⋯ ⋯
theorem Poincare.FrozenEllipticHeatOperator.norm_mapHolder_le.{u_1, u_2} : ∀ {F : Type u_1} {F' : Type u_2}
  [inst : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] [inst_2 : NormedAddCommGroup F'] [inst_3 : NormedSpace ℝ F']
  {α T : ℝ} (hα : 0 ≤ α) (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (Q : F →L[ℝ] F')
  (f : Poincare.ParabolicHolder.Y α T F),
  ‖Poincare.FrozenEllipticHeatOperator.mapHolder hα S Q f‖ ≤ ‖Q‖ * max 1 (‖S‖ ^ α) * ‖f‖ :=
⋯
theorem Poincare.FrozenEllipticHeatOperator.norm_forcing_pullback_le : ∀ {α T : ℝ} (hα : 0 ≤ α)
  (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (f : Poincare.ParabolicHolder.Y α T ℝ),
  ‖Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) f‖ ≤ max 1 (‖S‖ ^ α) * ‖f‖ :=
⋯
def Poincare.FrozenEllipticHeatOperator.mapGraph : {α T : ℝ} →
  0 ≤ α →
    (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) →
      Poincare.ParabolicSolutionGraph.Graph α T → Poincare.ParabolicSolutionGraph.Graph α T :=
fun {α T} hα S H =>
  { u := Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.u,
    ut := Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) H.ut,
    du :=
      Poincare.FrozenEllipticHeatOperator.mapHolder hα S (Poincare.FrozenEllipticHeatOperator.covectorPullback S) H.du,
    ddu :=
      Poincare.FrozenEllipticHeatOperator.mapHolder hα S (Poincare.FrozenEllipticHeatOperator.bilinearPullback S) H.ddu,
    zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }
theorem Poincare.FrozenEllipticHeatOperator.norm_mapGraph_le : ∀ {α T : ℝ} (hα : 0 ≤ α)
  (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (H : Poincare.ParabolicSolutionGraph.Graph α T),
  ‖Poincare.FrozenEllipticHeatOperator.mapGraph hα S H‖ ≤ max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α) * ‖H‖ :=
⋯
theorem Poincare.FrozenEllipticHeatOperator.trace_pullback : ∀
  (S : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3),
  (∀ (v w : Poincare.ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w)) →
    ∀ (H : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ),
      ∑ i,
          ∑ j,
            inner ℝ (S ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) (S ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) *
              (H (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) =
        ∑ k, (H ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) ((EuclideanSpace.basisFun (Fin 3) ℝ) k) :=
⋯
theorem Poincare.FrozenEllipticHeatOperator.exists_symmetric_factor : ∀
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ) {«λ» : ℝ},
  0 < «λ» →
    (∀ (v w : Poincare.ClosedSmoothModel 3), (A v) w = (A w) v) →
      (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A v) v) →
        ∃ S,
          (∀ (v w : Poincare.ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w)) ∧
            ∀ (v w : Poincare.ClosedSmoothModel 3), (A v) w = inner ℝ (S v) (S w) :=
⋯
theorem Poincare.FrozenEllipticHeatOperator.factor_norm_bounds : ∀
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
  (S : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) {«λ» Λ : ℝ},
  0 < «λ» →
    «λ» ≤ Λ →
      (∀ (v : Poincare.ClosedSmoothModel 3), (A v) v = inner ℝ (S v) (S v)) →
        (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A v) v) →
          (∀ (v : Poincare.ClosedSmoothModel 3), (A v) v ≤ Λ * ‖v‖ ^ 2) → ‖↑S‖ ≤ √Λ ∧ ‖↑S.symm‖ ≤ 1 / √«λ» :=
⋯
theorem Poincare.FrozenEllipticHeatOperator.exists_frozen_solution_graph_bound : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∀ («λ» Λ : ℝ),
        0 < «λ» →
          «λ» ≤ Λ →
            ∃ C,
              0 < C ∧
                ∀ (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ),
                  (∀ (v w : Poincare.ClosedSmoothModel 3), (A v) w = (A w) v) →
                    (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A v) v) →
                      (∀ (v : Poincare.ClosedSmoothModel 3), (A v) v ≤ Λ * ‖v‖ ^ 2) →
                        ∀ (T : ℝ),
                          0 < T →
                            T ≤ 1 →
                              ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                                ∃ G,
                                  (∀ t ∈ Set.Icc 0 T,
                                      ∀ (x : Poincare.ClosedSmoothModel 3),
                                        ↑(WithLp.fst ↑G.ut) (t, x) =
                                          ↑(WithLp.fst ↑f) (t, x) +
                                            ∑ i,
                                              ∑ j,
                                                (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                    ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
                                                  ((↑(WithLp.fst ↑G.ddu) (t, x))
                                                      ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                    ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
                                    ‖G‖ ≤ C * ‖f‖ :=
⋯
def Poincare.NearIdentityParabolicRightInverse.multiplier : {α T : ℝ} →
  (Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) →
    Poincare.ParabolicSolutionGraph.Graph α T →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ :=
fun {α T} b =>
  { toFun := Poincare.ParabolicHolderMultiplier.forcing b, map_add' := ⋯, map_smul' := ⋯ }.mkContinuous
    (∑ i, ∑ j, ‖b i j‖) ⋯
@[defeq] theorem Poincare.NearIdentityParabolicRightInverse.multiplier_apply : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T),
  (Poincare.NearIdentityParabolicRightInverse.multiplier b) G = Poincare.ParabolicHolderMultiplier.forcing b G :=
⋯
theorem Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ),
  0 < α →
    0 < T →
      ∀ {ε Λ : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            ‖Poincare.NearIdentityParabolicRightInverse.multiplier b‖ ≤ 9 * (ε + Λ * T ^ (α / 2)) :=
⋯
theorem Poincare.NearIdentityParabolicRightInverse.neumann_data_eq : ∀ {α T : ℝ}
  (R : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ) (hR : ‖R‖ < 1)
  (f : Poincare.ParabolicHolder.Y α T ℝ), ↑(Units.oneSub R hR)⁻¹ f = f + R (↑(Units.oneSub R hR)⁻¹ f) :=
⋯
theorem Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two : ∀ {α T : ℝ}
  (R : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ) (hR : ‖R‖ < 1),
  ‖R‖ ≤ 1 / 2 → ‖↑(Units.oneSub R hR)⁻¹‖ ≤ 2 :=
⋯
theorem Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant : ∀ {α T : ℝ} (hα : 0 < α)
  (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1),
  ‖Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1‖ ≤
    Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 :=
⋯
theorem Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1),
  0 < T →
    T ≤ 1 →
      ∀ {ε Λ : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ε ≤ 1 / 4 →
              9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4 →
                ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                  ∃ G,
                    (∀ t ∈ Set.Icc 0 T,
                        ∀ (x : Poincare.ClosedSmoothModel 3),
                          ↑(WithLp.fst ↑G.ut) (t, x) =
                            ↑(WithLp.fst ↑f) (t, x) +
                              ∑ i,
                                ∑ j,
                                  Poincare.NearIdentityParabolicRightInverse.coeff b i j (t, x) *
                                    ((↑(WithLp.fst ↑G.ddu) (t, x)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                      ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
                      ‖G‖ ≤ 2 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖ :=
⋯
def Poincare.DuhamelSolutionOperatorCLM.duhamelOperator : (α T : ℝ) →
  0 < α → α < 1 → 0 < T → T ≤ 1 → Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T :=
fun α T hα hα1 hT hT1 =>
  (Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap α T hα hα1 hT hT1).mkContinuous
    (Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1) ⋯
theorem Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves : ∀ (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
  (hT1 : T ≤ 1) (f : Poincare.ParabolicHolder.Y α T ℝ),
  ∀ t ∈ Set.Icc 0 T,
    ∀ (x : Poincare.ClosedSmoothModel 3),
      ↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ut) (t, x) =
        ↑(WithLp.fst ↑f) (t, x) +
          ∑ i,
            ((↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ddu) (t, x))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
              ((EuclideanSpace.basisFun (Fin 3) ℝ) i) :=
⋯
def Poincare.DuhamelSolutionOperatorCLM.boundConstant : (α : ℝ) → 0 < α → α < 1 → ℝ :=
fun α hα hα1 => Classical.choose ⋯
theorem Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1),
  0 < Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 ∧
    ∀ (T : ℝ),
      0 < T →
        T ≤ 1 →
          ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
            ∃ G,
              (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                  ↑(WithLp.fst ↑G.u) p =
                    ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                ‖G‖ ≤ Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖ :=
⋯
theorem Poincare.ParabolicSolutionGraph.Graph.ext_of_u.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ},
  0 < T → ∀ {G H : Poincare.ParabolicSolutionGraph.Graph α T}, G.u = H.u → G = H :=
⋯
theorem Poincare.ParabolicHolderMultiplier.norm_error_le : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (S : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T),
  0 < α →
    0 < T →
      ∀ {ε Λ C_S : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            ‖S‖ ≤ C_S →
              ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                ‖Poincare.ParabolicHolderMultiplier.forcing b (S f)‖ ≤ 9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ :=
⋯
@[defeq] theorem Poincare.ParabolicHolderMultiplier.forcing_apply : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T)
  (p : ℝ × Poincare.ClosedSmoothModel 3),
  ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.forcing b G)) p =
    ∑ i,
      ∑ j,
        ↑(WithLp.fst ↑(b i j)) p *
          ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) :=
⋯
theorem Poincare.ParabolicHolder.ext.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} {f g : Poincare.ParabolicHolder.Y α T F},
  (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p) → f = g :=
⋯
@[defeq] theorem Poincare.ParabolicHolder.add_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E),
  ↑(WithLp.fst ↑(f + g)) p = ↑(WithLp.fst ↑f) p + ↑(WithLp.fst ↑g) p :=
⋯
@[defeq] theorem Poincare.ParabolicHolder.smul_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (c : ℝ)
  (f : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E), ↑(WithLp.fst ↑(c • f)) p = c • ↑(WithLp.fst ↑f) p :=
⋯
@[defeq] theorem Poincare.ParabolicHolder.ofFunction_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : ℝ × E → F)
  (hoff : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, f p = 0)
  (hb : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖f p‖ ≤ M)
  (hh : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K) (p : ℝ × E),
  ↑(WithLp.fst ↑(Poincare.ParabolicHolder.ofFunction f hoff hb hh)) p = f p :=
⋯
theorem Poincare.ParabolicHolder.supNorm_nonneg.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  0 ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
⋯
theorem Poincare.ParabolicHolder.holderSeminorm_nonneg.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  0 ≤ Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
⋯
def Poincare.ParametrixNeumannCorrection.correctedInverse.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : NormedAddCommGroup X] →
      [inst_1 : NormedSpace ℝ X] →
        [inst_2 : NormedAddCommGroup Y] →
          [inst_3 : NormedSpace ℝ Y] → [CompleteSpace Y] → (Y →L[ℝ] X) → (R : Y →L[ℝ] Y) → ‖R‖ < 1 → Y →L[ℝ] X :=
fun {X} {Y} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] P R
    hR =>
  P.comp ↑(Units.oneSub R hR)⁻¹
```

Exit code: `0`.

</details>

<details>
<summary>004-pullbacks</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `004-pullbacks_NearFrozenParabolicRightInverse.lean`, SHA-256 `9c6f9590d306bf2753bf02b976209960ce3948c038ddb312ac5f25882fc3a45d`.

```text
Poincare/Global/NearFrozenParabolicRightInverse.lean:24:8: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearFrozenParabolicRightInverse.lean:38:12: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearFrozenParabolicRightInverse.lean:55:8: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearFrozenParabolicRightInverse.lean:65:13: error: unexpected token ':='; expected ')', ',' or ':'
```

Exit code: `1`.

</details>

<details>
<summary>005-pullbacks</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `005-pullbacks_NearFrozenParabolicRightInverse.lean`, SHA-256 `ed416da484a57a01e2cab9b5d045dd99bfa6f52bf5088c830ee20a90eef126cb`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>006-pullbacks-gates-0</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/006-pullbacks-gates-audit.lean
```

Source snapshot: `006-pullbacks-gates-0_006-pullbacks-gates-audit.lean`, SHA-256 `f934ca2463db5f825b8df3b53ac162510e0c2cfd4d5a21fc72725c5d64434e0a`.

```text
/private/tmp/near-frozen-evidence/006-pullbacks-gates-audit.lean:89:7: error: Function expected at
  `Poincare.NearFrozenParabolicRightInverse.isPrefixOf
but this term has type
  Name

Note: Expected a function because this term is being applied to the argument
  n
```

Exit code: `1`.

</details>

<details>
<summary>007-pullbacks-gates-0</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/007-pullbacks-gates-audit.lean
```

Source snapshot: `007-pullbacks-gates-0_007-pullbacks-gates-audit.lean`, SHA-256 `ffd02b613ab6ecd10f55100b54a635706caf60ad6d4a006425d7a7b9a773ed8c`.

```text
'Poincare.NearFrozenParabolicRightInverse.frozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_NAMESPACE_AUDIT declarations=14; every declaration has exactly the required three dependencies
```

Exit code: `0`.

</details>

<details>
<summary>007-pullbacks-gates-1</summary>

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `007-pullbacks-gates-1_NearFrozenParabolicRightInverse.lean`, SHA-256 `ed416da484a57a01e2cab9b5d045dd99bfa6f52bf5088c830ee20a90eef126cb`.

```text
```

Exit code: `1`.

</details>

<details>
<summary>007-pullbacks-gates-2</summary>

```sh
git diff --check
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>008-frozen-bound</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `008-frozen-bound_NearFrozenParabolicRightInverse.lean`, SHA-256 `4363a3285b01c7243add86747c073dea966bde66e9f453345c10b62599454c95`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>009-frozen-bound-gates-0</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/009-frozen-bound-gates-audit.lean
```

Source snapshot: `009-frozen-bound-gates-0_009-frozen-bound-gates-audit.lean`, SHA-256 `ba6d1e61f4acb180e375af5b2b00409472401cfe8a57ec8fcdd0ba3f08238c94`.

```text
'Poincare.NearFrozenParabolicRightInverse.frozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_NAMESPACE_AUDIT declarations=16; every declaration has exactly the required three dependencies
```

Exit code: `0`.

</details>

<details>
<summary>009-frozen-bound-gates-1</summary>

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `009-frozen-bound-gates-1_NearFrozenParabolicRightInverse.lean`, SHA-256 `4363a3285b01c7243add86747c073dea966bde66e9f453345c10b62599454c95`.

```text
```

Exit code: `1`.

</details>

<details>
<summary>009-frozen-bound-gates-2</summary>

```sh
git diff --check
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>010-mathlib-statements</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/mathlib-statements.lean
```

Source snapshot: `010-mathlib-statements_mathlib-statements.lean`, SHA-256 `47c92781db9db5c1571a51139a51414c927cd88d5b9497ab03b4d4c09fa2270b`.

```text
theorem ContinuousLinearMap.opNorm_le_bound.{u_1, u_2, u_4, u_5} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
  {F : Type u_5} [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F]
  [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →SL[σ₁₂] F) {M : ℝ},
  0 ≤ M → (∀ (x : E), ‖f x‖ ≤ M * ‖x‖) → ‖f‖ ≤ M :=
⋯
theorem ContinuousLinearMap.le_opNorm.{u_1, u_2, u_4, u_5} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
  {F : Type u_5} [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F]
  [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) (x : E), ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
⋯
theorem ContinuousLinearMap.opNorm_comp_le.{u_1, u_2, u_3, u_4, u_5, u_7} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2}
  {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_7} [inst : SeminormedAddCommGroup E]
  [inst_1 : SeminormedAddCommGroup F] [inst_2 : SeminormedAddCommGroup G] [inst_3 : NontriviallyNormedField 𝕜]
  [inst_4 : NontriviallyNormedField 𝕜₂] [inst_5 : NontriviallyNormedField 𝕜₃] [inst_6 : NormedSpace 𝕜 E]
  [inst_7 : NormedSpace 𝕜₂ F] [inst_8 : NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [inst_9 : RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (h : F →SL[σ₂₃] G)
  (f : E →SL[σ₁₂] F), ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
⋯
def ContinuousLinearMap.comp.{u_1, u_2, u_3, u_4, u_6, u_7} : {R₁ : Type u_1} →
  {R₂ : Type u_2} →
    {R₃ : Type u_3} →
      [inst : Semiring R₁] →
        [inst_1 : Semiring R₂] →
          [inst_2 : Semiring R₃] →
            {σ₁₂ : R₁ →+* R₂} →
              {σ₂₃ : R₂ →+* R₃} →
                {σ₁₃ : R₁ →+* R₃} →
                  {M₁ : Type u_4} →
                    [inst_3 : TopologicalSpace M₁] →
                      [inst_4 : AddCommMonoid M₁] →
                        {M₂ : Type u_6} →
                          [inst_5 : TopologicalSpace M₂] →
                            [inst_6 : AddCommMonoid M₂] →
                              {M₃ : Type u_7} →
                                [inst_7 : TopologicalSpace M₃] →
                                  [inst_8 : AddCommMonoid M₃] →
                                    [inst_9 : Module R₁ M₁] →
                                      [inst_10 : Module R₂ M₂] →
                                        [inst_11 : Module R₃ M₃] →
                                          [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] →
                                            (M₂ →SL[σ₂₃] M₃) → (M₁ →SL[σ₁₂] M₂) → M₁ →SL[σ₁₃] M₃ :=
fun {R₁} {R₂} {R₃} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂} {σ₂₃} {σ₁₃} {M₁} [TopologicalSpace M₁]
    [AddCommMonoid M₁] {M₂} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃} [TopologicalSpace M₃] [AddCommMonoid M₃]
    [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] g f =>
  { toLinearMap := ↑g ∘ₛₗ ↑f, cont := ⋯ }
def LinearMap.mkContinuous.{u_1, u_2, u_3, u_4} : {𝕜 : Type u_1} →
  {𝕜₂ : Type u_2} →
    {E : Type u_3} →
      {F : Type u_4} →
        [inst : Ring 𝕜] →
          [inst_1 : Ring 𝕜₂] →
            [inst_2 : SeminormedAddCommGroup E] →
              [inst_3 : SeminormedAddCommGroup F] →
                [inst_4 : Module 𝕜 E] →
                  [inst_5 : Module 𝕜₂ F] →
                    {σ : 𝕜 →+* 𝕜₂} → (f : E →ₛₗ[σ] F) → (C : ℝ) → (∀ (x : E), ‖f x‖ ≤ C * ‖x‖) → E →SL[σ] F :=
fun {𝕜} {𝕜₂} {E} {F} [Ring 𝕜] [Ring 𝕜₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F]
    {σ} f C h =>
  { toLinearMap := f, cont := ⋯ }
@[defeq] theorem ContinuousLinearEquiv.coe_coe.{u_1, u_2, u_4, u_5} : ∀ {R₁ : Type u_1} {R₂ : Type u_2}
  [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [inst_2 : RingHomInvPair σ₁₂ σ₂₁]
  [inst_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁] [inst_5 : AddCommMonoid M₁]
  {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_7 : AddCommMonoid M₂] [inst_8 : Module R₁ M₁]
  [inst_9 : Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂), ⇑↑e = ⇑e :=
⋯
theorem ContinuousLinearEquiv.apply_symm_apply.{u_1, u_2, u_4, u_5} : ∀ {R₁ : Type u_1} {R₂ : Type u_2}
  [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [inst_2 : RingHomInvPair σ₁₂ σ₂₁]
  [inst_3 : RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type u_4} [inst_4 : TopologicalSpace M₁] [inst_5 : AddCommMonoid M₁]
  {M₂ : Type u_5} [inst_6 : TopologicalSpace M₂] [inst_7 : AddCommMonoid M₂] [inst_8 : Module R₁ M₁]
  [inst_9 : Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂), e (e.symm c) = c :=
⋯
@[defeq] theorem ContinuousLinearMap.id_apply.{u_1, u_4} : ∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4}
  [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁] [inst_3 : Module R₁ M₁] (x : M₁),
  (ContinuousLinearMap.id R₁ M₁) x = x :=
⋯
theorem mul_le_mul_of_nonneg_right.{u_1} : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α]
  {a b c : α} [MulPosMono α], b ≤ c → 0 ≤ a → b * a ≤ c * a :=
⋯
theorem mul_le_mul_of_nonneg_left.{u_1} : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α]
  {a b c : α} [PosMulMono α], b ≤ c → 0 ≤ a → a * b ≤ a * c :=
⋯
theorem mul_le_mul.{u_1} : ∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : Preorder α] {a b c d : α}
  [PosMulMono α] [MulPosMono α], a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d :=
@mul_le_mul_of_nonneg'
theorem max_le_max.{u} : ∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, a ≤ c → b ≤ d → max a b ≤ max c d :=
⋯
theorem pow_le_pow_left₀.{u_2} : ∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b : M₀}
  [PosMulMono M₀] [MulPosMono M₀], 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n :=
⋯
theorem Real.rpow_le_rpow : ∀ {x y z : ℝ}, 0 ≤ x → x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z :=
⋯
theorem Real.rpow_nonneg : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ), 0 ≤ x ^ y :=
⋯
theorem norm_nonneg.{u_5} : ∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤ ‖a‖ :=
⋯
theorem Finset.sum_add_distrib.{u_1, u_4} : ∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst : AddCommMonoid M]
  {f g : ι → M}, ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x :=
⋯
theorem add_mul.{v} : ∀ {R : Type v} [inst : Mul R] [inst_1 : Add R] [RightDistribClass R] (a b c : R),
  (a + b) * c = a * c + b * c :=
@right_distrib
theorem congrArg.{u, v} : ∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂ :=
⋯
theorem mul_pos.{u_1} : ∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Preorder α] [PosMulStrictMono α],
  0 < a → 0 < b → 0 < a * b :=
@Left.mul_pos
theorem div_pos.{u_3} : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀]
  {a b : G₀}, 0 < a → 0 < b → 0 < a / b :=
⋯
theorem le_of_lt.{u_1} : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b :=
⋯
theorem mul_div_cancel₀.{u_3} : ∀ {G₀ : Type u_3} [inst : CommGroupWithZero G₀] {b : G₀} (a : G₀),
  b ≠ 0 → b * (a / b) = a :=
⋯
```

Exit code: `0`.

</details>

<details>
<summary>011-neumann</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `011-neumann_NearFrozenParabolicRightInverse.lean`, SHA-256 `568b1235681e2ef96cf1b5ba02ef335695231f99f87a6161b1abb7a2f56dc3b1`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>012-neumann-gates-0</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/012-neumann-gates-audit.lean
```

Source snapshot: `012-neumann-gates-0_012-neumann-gates-audit.lean`, SHA-256 `1f7e98a840b5d4eabea87995eda78b8538d3882fe22feef3c30f1f45019a63d1`.

```text
'Poincare.NearFrozenParabolicRightInverse.frozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozen_error_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_NAMESPACE_AUDIT declarations=23; every declaration has exactly the required three dependencies
```

Exit code: `0`.

</details>

<details>
<summary>012-neumann-gates-1</summary>

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `012-neumann-gates-1_NearFrozenParabolicRightInverse.lean`, SHA-256 `568b1235681e2ef96cf1b5ba02ef335695231f99f87a6161b1abb7a2f56dc3b1`.

```text
```

Exit code: `1`.

</details>

<details>
<summary>012-neumann-gates-2</summary>

```sh
git diff --check
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>013-existence</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `013-existence_NearFrozenParabolicRightInverse.lean`, SHA-256 `08312d23e945050437fc19b7b76d3cf9720d06de720c48fe0e6b16f25a38ffba`.

```text
Poincare/Global/NearFrozenParabolicRightInverse.lean:242:4: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

Exit code: `0`.

</details>

<details>
<summary>014-existence-clean</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `014-existence-clean_NearFrozenParabolicRightInverse.lean`, SHA-256 `07ab264829e853c1714c19e207f992970ff703f4b1ddc1143a25172e3317a657`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>015-exact-target</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/exact-target.lean
```

Source snapshot: `015-exact-target_exact-target.lean`, SHA-256 `abc474c0731d15362cc6d7064f7151b1869e43655018462a3574e5135d23c101`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>016-existence-gates-0</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/016-existence-gates-audit.lean
```

Source snapshot: `016-existence-gates-0_016-existence-gates-audit.lean`, SHA-256 `1c49df01a8386b1c03a6bcf333c937fe36751fe6d495c0574fb2e1c0f2e2a2f4`.

```text
'Poincare.NearFrozenParabolicRightInverse.frozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozen_error_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.holderPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_NAMESPACE_AUDIT declarations=25; every declaration has exactly the required three dependencies
```

Exit code: `0`.

</details>

<details>
<summary>016-existence-gates-1</summary>

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `016-existence-gates-1_NearFrozenParabolicRightInverse.lean`, SHA-256 `07ab264829e853c1714c19e207f992970ff703f4b1ddc1143a25172e3317a657`.

```text
```

Exit code: `1`.

</details>

<details>
<summary>016-existence-gates-2</summary>

```sh
git diff --check
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>017-module-build</summary>

```sh
lake env lean -o .lake/build/lib/lean/Poincare/Global/NearFrozenParabolicRightInverse.olean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `017-module-build_NearFrozenParabolicRightInverse.lean`, SHA-256 `07ab264829e853c1714c19e207f992970ff703f4b1ddc1143a25172e3317a657`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>018-name-grep</summary>

```sh
python3 /private/tmp/near-frozen-evidence/name-grep.py
```

```text
rg -n <all printed declaration basenames> <project context, Mathlib, Lean source>
Poincare.FrozenEllipticHeatOperator.mapHolder: Poincare/Global/FrozenEllipticHeatOperator.lean:61:def mapHolder (hα : 0 ≤ α) (S : E →L[ℝ] E) (Q : F →L[ℝ] F')
Poincare.FrozenEllipticHeatOperator.norm_mapHolder_le: Poincare/Global/FrozenEllipticHeatOperator.lean:71:theorem norm_mapHolder_le (hα : 0 ≤ α) (S : E →L[ℝ] E) (Q : F →L[ℝ] F')
Poincare.FrozenEllipticHeatOperator.norm_forcing_pullback_le: Poincare/Global/FrozenEllipticHeatOperator.lean:88:theorem norm_forcing_pullback_le (hα : 0 ≤ α) (S : E →L[ℝ] E)
Poincare.FrozenEllipticHeatOperator.mapGraph: Poincare/Global/FrozenEllipticHeatOperator.lean:131:def mapGraph (hα : 0 ≤ α) (S : E →L[ℝ] E)
Poincare.FrozenEllipticHeatOperator.norm_mapGraph_le: Poincare/Global/FrozenEllipticHeatOperator.lean:148:theorem norm_mapGraph_le (hα : 0 ≤ α) (S : E →L[ℝ] E)
Poincare.FrozenEllipticHeatOperator.trace_pullback: Poincare/Global/FrozenEllipticHeatOperator.lean:180:theorem trace_pullback (S : E ≃L[ℝ] E)
Poincare.FrozenEllipticHeatOperator.exists_symmetric_factor: Poincare/Global/FrozenEllipticHeatOperator.lean:396:theorem exists_symmetric_factor (A : Bilin) {«λ» : ℝ} (hLowerPos : 0 < «λ»)
Poincare.FrozenEllipticHeatOperator.factor_norm_bounds: Poincare/Global/FrozenEllipticHeatOperator.lean:311:theorem factor_norm_bounds (A : Bilin) (S : E ≃L[ℝ] E) {«λ» Λ : ℝ}
Poincare.FrozenEllipticHeatOperator.exists_frozen_solution_graph_bound: Poincare/Global/FrozenEllipticHeatOperator.lean:428:theorem exists_frozen_solution_graph_bound :
Poincare.NearIdentityParabolicRightInverse.multiplier: Poincare/Global/NearIdentityParabolicRightInverse.lean:60:def multiplier (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) :
Poincare.NearIdentityParabolicRightInverse.multiplier_apply: Poincare/Global/NearIdentityParabolicRightInverse.lean:68:@[simp] theorem multiplier_apply (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le: Poincare/Global/NearIdentityParabolicRightInverse.lean:73:theorem multiplier_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
Poincare.NearIdentityParabolicRightInverse.neumann_data_eq: Poincare/Global/NearIdentityParabolicRightInverse.lean:139:theorem neumann_data_eq (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)
Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two: Poincare/Global/NearIdentityParabolicRightInverse.lean:154:theorem neumann_norm_le_two (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant: Poincare/Global/NearIdentityParabolicRightInverse.lean:86:theorem duhamel_norm_le_boundConstant (hα : 0 < α) (hα1 : α < 1)
Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution: Poincare/Global/NearIdentityParabolicRightInverse.lean:217:theorem exists_nearIdentity_solution (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator: Poincare/Global/DuhamelSolutionOperatorCLM.lean:133:def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves: Poincare/Global/DuhamelSolutionOperatorCLM.lean:157:theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
Poincare.DuhamelSolutionOperatorCLM.boundConstant: Poincare/Global/DuhamelSolutionOperatorCLM.lean:49:def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec: Poincare/Global/DuhamelSolutionOperatorCLM.lean:53:theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
Poincare.ParabolicSolutionGraph.Graph.ext_of_u: Poincare/Global/DuhamelSolutionOperatorCLM.lean:11:theorem Graph.ext_of_u {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
Poincare.ParabolicHolderMultiplier.norm_error_le: Poincare/Global/ParabolicHolderMultiplier.lean:224:theorem norm_error_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare.ParabolicHolderMultiplier.forcing_apply: Poincare/Global/ParabolicHolderMultiplier.lean:168:@[simp] theorem forcing_apply (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare.ParabolicHolder.ext: Poincare/Global/ParabolicHolderSpace.lean:217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
Poincare.ParabolicHolder.add_apply: Poincare/Global/ParabolicHolderSpace.lean:208:@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
Poincare.ParabolicHolder.smul_apply: Poincare/Global/ParabolicHolderSpace.lean:214:@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
Poincare.ParabolicHolder.ofFunction_apply: Poincare/Global/ParabolicHolderSpace.lean:189:@[simp] theorem ofFunction_apply (f : ℝ × E → F) (hoff hb hh) (p : ℝ × E) :
Poincare.ParabolicHolder.supNorm_nonneg: Poincare/Global/ParabolicHolderSpace.lean:327:theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
Poincare.ParabolicHolder.holderSeminorm_nonneg: Poincare/Global/ParabolicHolderSpace.lean:331:theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
Poincare.ParametrixNeumannCorrection.correctedInverse: Poincare/Global/ParametrixNeumannCorrection.lean:22:def correctedInverse (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y) (hR : ‖R‖ < 1) : Y →L[ℝ] X :=
ContinuousLinearMap.opNorm_le_bound: .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:201:theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
ContinuousLinearMap.le_opNorm: .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:239:theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
ContinuousLinearMap.opNorm_comp_le: .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:397:theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
ContinuousLinearMap.comp: .lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:296:def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
LinearMap.mkContinuous: .lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:150:def mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [⋀^ι]→L[𝕜] F :=
ContinuousLinearEquiv.coe_coe: .lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:177:protected theorem coe_coe {F : Type*} [FunLike F A B]
ContinuousLinearEquiv.apply_symm_apply: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:311:theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
ContinuousLinearMap.id_apply: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:240:theorem id_apply (p : A) : AlgHom.id R A p = p :=
mul_le_mul_of_nonneg_right: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Grind/Ordered/Ring.lean:272:theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
mul_le_mul_of_nonneg_left: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Grind/Ordered/Ring.lean:261:theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : c * a ≤ c * b := by
mul_le_mul: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Data/Nat/Basic.lean:757:protected theorem mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂ :=
max_le_max: .lake/packages/mathlib/Mathlib/Order/MinMax.lean:54:theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
pow_le_pow_left₀: Poincare/Global/FrozenEllipticHeatOperator.lean:449:    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
Real.rpow_le_rpow: .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean:146:lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
Real.rpow_nonneg: .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:412:lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a
norm_nonneg: .lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:182:protected lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
Finset.sum_add_distrib: .lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean:466:theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
add_mul: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Data/Dyadic/Basic.lean:614:theorem add_mul (x y z : Dyadic) : (x + y) * z = x * z + y * z := by
congrArg: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean:423:theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
mul_pos: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Grind/Ordered/Ring.lean:246:theorem mul_pos [LE R] [LT R] [IsPreorder R] [OrderedRing R] {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
div_pos: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Data/Nat/Div/Lemmas.lean:96:theorem div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b := by
le_of_lt: /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Grind/Ordered/Order.lean:23:theorem le_of_lt {a b : α} (h : a < b) : a ≤ b := (lt_iff_le_and_not_ge.mp h).1
mul_div_cancel₀: .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:117:  · rw [← mul_cpow_ofReal_nonneg ha.le (div_pos hx.1 ha).le, ofReal_div, mul_div_cancel₀ _ ha']
Poincare.NearFrozenParabolicRightInverse.holderPullback: Poincare/Global/NearFrozenParabolicRightInverse.lean:23:def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
Poincare.NearFrozenParabolicRightInverse.graphPullback: Poincare/Global/NearFrozenParabolicRightInverse.lean:37:def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
Poincare.NearFrozenParabolicRightInverse.frozenInverse: Poincare/Global/NearFrozenParabolicRightInverse.lean:53:def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves: Poincare/Global/NearFrozenParabolicRightInverse.lean:61:theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le: Poincare/Global/NearFrozenParabolicRightInverse.lean:83:theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound: Poincare/Global/NearFrozenParabolicRightInverse.lean:111:theorem exists_frozen_operator_bound :
Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse: Poincare/Global/NearFrozenParabolicRightInverse.lean:144:def nearFrozenInverse
Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_solves: Poincare/Global/NearFrozenParabolicRightInverse.lean:153:theorem nearFrozenInverse_solves (A : Bilin)
Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_norm_le: Poincare/Global/NearFrozenParabolicRightInverse.lean:181:theorem nearFrozenInverse_norm_le
Poincare.NearFrozenParabolicRightInverse.frozen_error_small: Poincare/Global/NearFrozenParabolicRightInverse.lean:197:theorem frozen_error_small
Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator: Poincare/Global/NearFrozenParabolicRightInverse.lean:219:theorem exists_nearFrozen_operator :
Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_solution: Poincare/Global/NearFrozenParabolicRightInverse.lean:253:theorem exists_nearFrozen_solution :
VERIFIED_NAMES=65
```

Exit code: `0`.

</details>

<details>
<summary>019-module-audit</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/module-audit.lean
```

Source snapshot: `019-module-audit_module-audit.lean`, SHA-256 `76e91aac87869791424f65921bf156ab0f0416c0e8ac42bbab22381e85c878ed`.

```text
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2 : ∀ {T : ℝ},
  IsScalarTower ℝ ℝ (WithLp 1 (↥(lp (fun x => ℝ) ⊤) × ↥(lp (fun x => ℝ) ⊤))) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1 : ∀ {T : ℝ},
  IsScalarTower ℝ ℝ (WithLp 1 (↥(lp (fun x => ℝ) ⊤) × ↥(lp (fun x => ℝ) ⊤))) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
private meta def Poincare.NearFrozenParabolicRightInverse._aux_Poincare_Global_NearFrozenParabolicRightInverse___macroRules__private_Poincare_Global_NearFrozenParabolicRightInverse_0_Poincare_NearFrozenParabolicRightInverse_termE_1_1 : Macro :=
fun x =>
  have __discr := x;
  if
      __discr.isOfKind
          ((((((((Name.anonymous.mkStr "_private").mkStr "Poincare").mkStr "Global").mkStr
                            "NearFrozenParabolicRightInverse").mkNum
                        0).mkStr
                    "Poincare").mkStr
                "NearFrozenParabolicRightInverse").mkStr
            "termE_1") =
        true then
    have __discr := __discr.getArg 0;
    do
    let info ← MonadRef.mkInfoFromRefPos
    let scp ← getCurrMacroScope
    let quotCtx ← MonadQuotation.getContext
    pure
        {
            raw :=
              Syntax.node2 info `Lean.Parser.Term.app
                (Syntax.ident info "EuclideanSpace.basisFun".toRawSubstring'
                  (addMacroScope quotCtx `EuclideanSpace.basisFun scp)
                  [Syntax.Preresolved.decl `EuclideanSpace.basisFun []])
                (Syntax.node2 info `null
                  (Syntax.node3 info `Lean.Parser.Term.paren
                    (Syntax.node2 info `Lean.Parser.Term.hygienicLParen (Syntax.atom info "(")
                      (Syntax.node1 info `hygieneInfo
                        (Syntax.ident info "".toRawSubstring' (addMacroScope quotCtx Name.anonymous scp)
                          [Syntax.Preresolved.namespace `Poincare.NearFrozenParabolicRightInverse,
                            Syntax.Preresolved.namespace `Poincare.DuhamelSolutionOperatorCLM,
                            Syntax.Preresolved.namespace `Poincare.FrozenEllipticHeatOperator,
                            Syntax.Preresolved.namespace `Poincare.ParabolicSolutionGraph,
                            Syntax.Preresolved.namespace `Poincare.ParabolicHolder,
                            Syntax.Preresolved.namespace `Set])))
                    (Syntax.node2 info `Lean.Parser.Term.app
                      (Syntax.ident info "Fin".toRawSubstring' (addMacroScope quotCtx `Fin scp)
                        [Syntax.Preresolved.decl `Fin [], Syntax.Preresolved.namespace `Fin])
                      (Syntax.node1 info `null (Syntax.node1 info `num (Syntax.atom info "3"))))
                    (Syntax.atom info ")"))
                  (Syntax.node1 info `termℝ (Syntax.atom info "ℝ"))) }.raw
  else
    have __discr := x;
    throw Macro.Exception.unsupportedSyntax
'_private.Poincare.Global.NearFrozenParabolicRightInverse.0.Poincare.NearFrozenParabolicRightInverse._aux_Poincare_Global_NearFrozenParabolicRightInverse___macroRules__private_Poincare_Global_NearFrozenParabolicRightInverse_0_Poincare_NearFrozenParabolicRightInverse_termE_1_1' does not depend on any axioms
/private/tmp/near-frozen-evidence/module-audit.lean:4:0: error: Unexpected foundational dependencies for _private.Poincare.Global.NearFrozenParabolicRightInverse.0.Poincare.NearFrozenParabolicRightInverse._aux_Poincare_Global_NearFrozenParabolicRightInverse___macroRules__private_Poincare_Global_NearFrozenParabolicRightInverse_0_Poincare_NearFrozenParabolicRightInverse_termE_1_1: []
```

Exit code: `1`.

</details>

<details>
<summary>020-without-notation</summary>

```sh
lake env lean -o .lake/build/lib/lean/Poincare/Global/NearFrozenParabolicRightInverse.olean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `020-without-notation_NearFrozenParabolicRightInverse.lean`, SHA-256 `8cf6a3468b88ae4fd75cca35c4fe20c3082b3fca0f7984f3e13ab3d81230a985`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>021-linear-map-grep</summary>

```sh
rg -n 'theorem (coe_coe|apply_symm_apply|id_apply)|^def (comp |LinearMap.mkContinuous )' .lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean
```

Source snapshot: `021-linear-map-grep_ContinuousLinearMap.lean`, SHA-256 `bb26ac2b8a771841cb6dc83fd8d04865da3e1d66eb68249056a51a0d3b283272`.

Source snapshot: `021-linear-map-grep_Equiv.lean`, SHA-256 `aa9303f6dd87e253402b2425cdb68db29aedeab37c1606dc76356f666deb7146`.

Source snapshot: `021-linear-map-grep_LinearMap.lean`, SHA-256 `551705e41b4d87608c74c31e6370f5db4f6d46c309ce6fcde5c5145d64daee6c`.

```text
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean:55:def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:163:theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:357:theorem id_apply (x : M₁) : ContinuousLinearMap.id R₁ M₁ x = x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:453:def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:177:theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:520:theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
```

Exit code: `0`.

</details>

<details>
<summary>022-scalar-grep</summary>

```sh
rg -n '(^theorem (rpow_le_rpow |rpow_nonneg |pow_le_pow_left₀|mul_le_mul_of_nonneg_right|mul_le_mul_of_nonneg_left)|alias mul_le_mul |alias add_mul |lemma le_of_eq |theorem mul_comm)' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean .lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean .lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean .lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean
```

Source snapshot: `022-scalar-grep_Basic.lean`, SHA-256 `f4f33f1236afe8fef845242ee85773d8821a6aa724839908f790b47bd90d760c`.

Source snapshot: `022-scalar-grep_Defs.lean`, SHA-256 `7c106171cb7a79773caa632ff4dd575c6e097c3d840bf0c0af57d3955f88ea66`.

Source snapshot: `022-scalar-grep_PartialOrder.lean`, SHA-256 `6515bdb4a68678b27490ec2b3332f6d7b1e529489ff9d844898ec1eda5637ec5`.

Source snapshot: `022-scalar-grep_Real.lean`, SHA-256 `c95c6cf267c91508f3f839ea8d2c3baf74c86d8649c7833f0132a32081e5a929`.

```text
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:81:@[to_dual ge_of_eq] lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:258:theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm
.lake/packages/mathlib/Mathlib/Algebra/Ring/Defs.lean:99:alias add_mul := right_distrib
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:226:theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:230:theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:352:alias mul_le_mul := mul_le_mul_of_nonneg'
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:459:theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:163:theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:546:theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
```

Exit code: `0`.

</details>

<details>
<summary>023-module-audit</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/module-audit.lean
```

Source snapshot: `023-module-audit_module-audit.lean`, SHA-256 `76e91aac87869791424f65921bf156ab0f0416c0e8ac42bbab22381e85c878ed`.

```text
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2 : ∀ {T : ℝ},
  IsScalarTower ℝ ℝ (WithLp 1 (↥(lp (fun x => ℝ) ⊤) × ↥(lp (fun x => ℝ) ⊤))) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1 : ∀ {T : ℝ},
  IsScalarTower ℝ ℝ (WithLp 1 (↥(lp (fun x => ℝ) ⊤) × ↥(lp (fun x => ℝ) ⊤))) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
def Poincare.NearFrozenParabolicRightInverse.frozenInverse : {α T : ℝ} →
  (Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) →
    0 < α → α < 1 → 0 < T → T ≤ 1 → Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T :=
fun {α T} S hα hα1 hT hT1 =>
  (Poincare.NearFrozenParabolicRightInverse.graphPullback ⋯ hT ↑S.symm).comp
    ((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1).comp
      (Poincare.NearFrozenParabolicRightInverse.holderPullback ⋯ ↑S))
'Poincare.NearFrozenParabolicRightInverse.frozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_3 : ∀ {α T : ℝ},
  CompleteSpace (Poincare.ParabolicHolder.Y α T ℝ) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4 : ∀ {α : ℝ}, 0 < α → 0 ≤ α :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_solves : ∀ {α T : ℝ}
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
  (P : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T),
  (∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
      ∀ t ∈ Set.Icc 0 T,
        ∀ (x : Poincare.ClosedSmoothModel 3),
          ↑(WithLp.fst ↑(P f).ut) (t, x) =
            ↑(WithLp.fst ↑f) (t, x) +
              ∑ i,
                ∑ j,
                  (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
                    ((↑(WithLp.fst ↑(P f).ddu) (t, x)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                      ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) →
    ∀ (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
      (hR : ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
      (f : Poincare.ParabolicHolder.Y α T ℝ),
      ∀ t ∈ Set.Icc 0 T,
        ∀ (x : Poincare.ClosedSmoothModel 3),
          ↑(WithLp.fst ↑((Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse P b hR) f).ut) (t, x) =
            ↑(WithLp.fst ↑f) (t, x) +
              ∑ i,
                ∑ j,
                  ((A ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
                      ↑(WithLp.fst ↑(b i j)) (t, x)) *
                    ((↑(WithLp.fst ↑((Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse P b hR) f).ddu) (t, x))
                        ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                      ((EuclideanSpace.basisFun (Fin 3) ℝ) j) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
def Poincare.NearFrozenParabolicRightInverse.holderPullback : {α T : ℝ} →
  0 ≤ α →
    (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) →
      Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ :=
fun {α T} hα S =>
  { toFun := Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ), map_add' := ⋯,
        map_smul' := ⋯ }.mkContinuous
    (max 1 (‖S‖ ^ α)) ⋯
'Poincare.NearFrozenParabolicRightInverse.holderPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves : ∀ {α T : ℝ}
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ)
  (S : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3),
  (∀ (v w : Poincare.ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w)) →
    (∀ (v w : Poincare.ClosedSmoothModel 3), (A v) w = inner ℝ (S v) (S w)) →
      ∀ (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) (f : Poincare.ParabolicHolder.Y α T ℝ),
        ∀ t ∈ Set.Icc 0 T,
          ∀ (x : Poincare.ClosedSmoothModel 3),
            ↑(WithLp.fst ↑((Poincare.NearFrozenParabolicRightInverse.frozenInverse S hα hα1 hT hT1) f).ut) (t, x) =
              ↑(WithLp.fst ↑f) (t, x) +
                ∑ i,
                  ∑ j,
                    (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
                      ((↑(WithLp.fst ↑((Poincare.NearFrozenParabolicRightInverse.frozenInverse S hα hα1 hT hT1) f).ddu)
                            (t, x))
                          ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                        ((EuclideanSpace.basisFun (Fin 3) ℝ) j) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1 : ∀ {α T : ℝ} (hα : 0 ≤ α),
  0 < T →
    ∀ (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3)
      (G H : Poincare.ParabolicSolutionGraph.Graph α T),
      Poincare.FrozenEllipticHeatOperator.mapGraph hα S (G + H) =
        Poincare.FrozenEllipticHeatOperator.mapGraph hα S G + Poincare.FrozenEllipticHeatOperator.mapGraph hα S H :=
⋯
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1 : ∀ (i : ℝ × Poincare.ClosedSmoothModel 3),
  NormOneClass ℝ :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
def Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse : {α T : ℝ} →
  (P : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T) →
    (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) →
      ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 →
        Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T :=
fun {α T} P b hR =>
  Poincare.ParametrixNeumannCorrection.correctedInverse P
    ((Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P) hR
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem Poincare.DuhamelSolutionOperatorCLM.duhamelOperator.congr_simp : ∀ (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
  (hT : 0 < T) (hT1 : T ≤ 1),
  Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1 =
    Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1 :=
⋯
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator.congr_simp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1 : ∀ (i : ℝ × Poincare.ClosedSmoothModel 3),
  IsBoundedSMul ℝ ℝ :=
⋯
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2 : ∀ {T : ℝ}
  (i : Poincare.ParabolicHolder.Pairs (Poincare.ParabolicHolder.cylinder T)), NormOneClass ℝ :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_norm_le : ∀ {α T : ℝ}
  (P : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T)
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (hR : ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1),
  ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 →
    ∀ {D : ℝ}, ‖P‖ ≤ D → ‖Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse P b hR‖ ≤ 2 * D :=
⋯
'Poincare.NearFrozenParabolicRightInverse.nearFrozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le : ∀ {α T : ℝ}
  (S : Poincare.ClosedSmoothModel 3 ≃L[ℝ] Poincare.ClosedSmoothModel 3) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
  (hT1 : T ≤ 1),
  ‖Poincare.NearFrozenParabolicRightInverse.frozenInverse S hα hα1 hT hT1‖ ≤
    max 1 (‖↑S.symm‖ ^ 2) * max 1 (‖↑S.symm‖ ^ α) * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 *
      max 1 (‖↑S‖ ^ α) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4 : ∀ {α T : ℝ} (hα : 0 ≤ α)
  (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (c : ℝ) (f : Poincare.ParabolicHolder.Y α T ℝ),
  Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) (c • f) =
    (RingHom.id ℝ) c • Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) f :=
⋯
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3 : ∀ {α T : ℝ} (hα : 0 ≤ α)
  (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (f g : Poincare.ParabolicHolder.Y α T ℝ),
  Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) (f + g) =
    Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) f +
      Poincare.FrozenEllipticHeatOperator.mapHolder hα S (ContinuousLinearMap.id ℝ ℝ) g :=
⋯
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_solution : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∀ («λ» Λ : ℝ),
        0 < «λ» →
          «λ» ≤ Λ →
            ∃ C ε₀ τ₀,
              0 < C ∧
                0 < ε₀ ∧
                  0 < τ₀ ∧
                    ∀ (A₀ : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ),
                      (∀ (v w : Poincare.ClosedSmoothModel 3), (A₀ v) w = (A₀ w) v) →
                        (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A₀ v) v) →
                          (∀ (v : Poincare.ClosedSmoothModel 3), (A₀ v) v ≤ Λ * ‖v‖ ^ 2) →
                            ∀ (T : ℝ),
                              0 < T →
                                T ≤ τ₀ →
                                  ∀ (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (Λb : ℝ),
                                    (∀ (i j : Fin 3),
                                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑(b i j)) ≤
                                          ε₀) →
                                      (∀ (i j : Fin 3),
                                          Poincare.ParabolicHolder.holderSeminorm α
                                              (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                                            Λb) →
                                        Λb * T ^ (α / 2) ≤ ε₀ →
                                          ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                                            ∃ G,
                                              (∀ t ∈ Set.Icc 0 T,
                                                  ∀ (x : Poincare.ClosedSmoothModel 3),
                                                    ↑(WithLp.fst ↑G.ut) (t, x) =
                                                      ↑(WithLp.fst ↑f) (t, x) +
                                                        ∑ i,
                                                          ∑ j,
                                                            ((A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                                  ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
                                                                ↑(WithLp.fst ↑(b i j)) (t, x)) *
                                                              ((↑(WithLp.fst ↑G.ddu) (t, x))
                                                                  ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                                ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
                                                ‖G‖ ≤ C * ‖f‖ :=
⋯
'Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
def Poincare.NearFrozenParabolicRightInverse.graphPullback : {α T : ℝ} →
  0 ≤ α →
    0 < T →
      (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) →
        Poincare.ParabolicSolutionGraph.Graph α T →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T :=
fun {α T} hα hT S =>
  { toFun := Poincare.FrozenEllipticHeatOperator.mapGraph hα S, map_add' := ⋯, map_smul' := ⋯ }.mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) ⋯
'Poincare.NearFrozenParabolicRightInverse.graphPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∀ («λ» Λ : ℝ),
        0 < «λ» →
          «λ» ≤ Λ →
            ∃ C ε₀ τ₀,
              0 < C ∧
                0 < ε₀ ∧
                  0 < τ₀ ∧
                    ∀ (A₀ : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ),
                      (∀ (v w : Poincare.ClosedSmoothModel 3), (A₀ v) w = (A₀ w) v) →
                        (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A₀ v) v) →
                          (∀ (v : Poincare.ClosedSmoothModel 3), (A₀ v) v ≤ Λ * ‖v‖ ^ 2) →
                            ∀ (T : ℝ),
                              0 < T →
                                T ≤ τ₀ →
                                  ∀ (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (Λb : ℝ),
                                    (∀ (i j : Fin 3),
                                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑(b i j)) ≤
                                          ε₀) →
                                      (∀ (i j : Fin 3),
                                          Poincare.ParabolicHolder.holderSeminorm α
                                              (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                                            Λb) →
                                        Λb * T ^ (α / 2) ≤ ε₀ →
                                          ∃ S,
                                            (∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                                                ∀ t ∈ Set.Icc 0 T,
                                                  ∀ (x : Poincare.ClosedSmoothModel 3),
                                                    ↑(WithLp.fst ↑(S f).ut) (t, x) =
                                                      ↑(WithLp.fst ↑f) (t, x) +
                                                        ∑ i,
                                                          ∑ j,
                                                            ((A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                                  ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
                                                                ↑(WithLp.fst ↑(b i j)) (t, x)) *
                                                              ((↑(WithLp.fst ↑(S f).ddu) (t, x))
                                                                  ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                                ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
                                              ‖S‖ ≤ C :=
⋯
'Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3 : RingHomCompTriple (RingHom.id ℝ)
  (RingHom.id ℝ) (RingHom.id ℝ) :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozenInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∀ («λ» Λ : ℝ),
        0 < «λ» →
          «λ» ≤ Λ →
            ∃ D,
              0 < D ∧
                ∀ (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ),
                  (∀ (v w : Poincare.ClosedSmoothModel 3), (A v) w = (A w) v) →
                    (∀ (v : Poincare.ClosedSmoothModel 3), «λ» * ‖v‖ ^ 2 ≤ (A v) v) →
                      (∀ (v : Poincare.ClosedSmoothModel 3), (A v) v ≤ Λ * ‖v‖ ^ 2) →
                        ∀ (T : ℝ),
                          0 < T →
                            T ≤ 1 →
                              ∃ P,
                                (∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                                    ∀ t ∈ Set.Icc 0 T,
                                      ∀ (x : Poincare.ClosedSmoothModel 3),
                                        ↑(WithLp.fst ↑(P f).ut) (t, x) =
                                          ↑(WithLp.fst ↑f) (t, x) +
                                            ∑ i,
                                              ∑ j,
                                                (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                    ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
                                                  ((↑(WithLp.fst ↑(P f).ddu) (t, x))
                                                      ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                                    ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
                                  ‖P‖ ≤ D :=
⋯
'Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2 : ∀ {T : ℝ}
  (i : Poincare.ParabolicHolder.Pairs (Poincare.ParabolicHolder.cylinder T)), IsBoundedSMul ℝ ℝ :=
⋯
'Poincare.NearFrozenParabolicRightInverse.holderPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2 : ∀ {α T : ℝ} (hα : 0 ≤ α),
  0 < T →
    ∀ (S : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3) (c : ℝ)
      (G : Poincare.ParabolicSolutionGraph.Graph α T),
      Poincare.FrozenEllipticHeatOperator.mapGraph hα S (c • G) =
        (RingHom.id ℝ) c • Poincare.FrozenEllipticHeatOperator.mapGraph hα S G :=
⋯
'Poincare.NearFrozenParabolicRightInverse.graphPullback._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
theorem Poincare.NearFrozenParabolicRightInverse.frozen_error_small : ∀ {α T : ℝ}
  (P : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T)
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ),
  0 < α →
    0 < T →
      ∀ {D ε Λb : ℝ},
        ‖P‖ ≤ D →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
            (∀ (i j : Fin 3),
                Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                  Λb) →
              9 * D * ε ≤ 1 / 4 →
                9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 →
                  ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
                    ‖(Poincare.NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 :=
⋯
'Poincare.NearFrozenParabolicRightInverse.frozen_error_small' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_MODULE_AUDIT declarations=26; every declaration has exactly the required three dependencies
```

Exit code: `0`.

</details>

<details>
<summary>024-final-statements</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/final-statements.lean
```

Source snapshot: `024-final-statements_final-statements.lean`, SHA-256 `2ae50c2506a78b695410107b252f18334815c8969d044070782e6c94f0deccaa`.

```text
theorem mul_comm.{u_1} : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a :=
⋯
theorem le_of_eq.{u_1} : ∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b :=
⋯
```

Exit code: `0`.

</details>

<details>
<summary>025-imported-target</summary>

```sh
lake env lean /private/tmp/near-frozen-evidence/imported-target.lean
```

Source snapshot: `025-imported-target_imported-target.lean`, SHA-256 `cba2f2205f99fafcdd1b3af3ad50f4c4485f85736981ebb04cc5e58e3481cca5`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>026-final-source</summary>

```sh
lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `026-final-source_NearFrozenParabolicRightInverse.lean`, SHA-256 `8cf6a3468b88ae4fd75cca35c4fe20c3082b3fca0f7984f3e13ab3d81230a985`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>027-final-token-scan</summary>

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Source snapshot: `027-final-token-scan_NearFrozenParabolicRightInverse.lean`, SHA-256 `8cf6a3468b88ae4fd75cca35c4fe20c3082b3fca0f7984f3e13ab3d81230a985`.

```text
```

Exit code: `1`.

</details>

<details>
<summary>028-final-diff-check</summary>

```sh
git diff --check
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>029-base-diff-check</summary>

```sh
git diff --check 571442448b8afd8484cd770e22944f54daec05e5
```

```text
```

Exit code: `0`.

</details>

<details>
<summary>030-lean-scope</summary>

```sh
git diff --name-status 571442448b8afd8484cd770e22944f54daec05e5 -- '*.lean'
```

```text
A	Poincare/Global/NearFrozenParabolicRightInverse.lean
```

Exit code: `0`.

</details>

<details>
<summary>031-frozen-scope</summary>

```sh
git diff 571442448b8afd8484cd770e22944f54daec05e5 -- Poincare.lean harness/tasks/near-frozen-parabolic-right-inverse.md harness/v2/contracts
```

Source snapshot: `031-frozen-scope_Poincare.lean`, SHA-256 `8701d62a4f5e185173a2727e2d6eae85ba12c39fcffff487122918622407fc9e`.

```text
```

Exit code: `0`.

</details>

<details>
<summary>032-commits</summary>

```sh
git log --oneline 571442448b8afd8484cd770e22944f54daec05e5..HEAD
```

```text
5c1f77a4 fix: remove notation metadata for exact module dependency gate
e5aeb288 feat: prove uniform near-frozen parabolic solvability and operator bound
4e4226c8 feat: correct frozen inverse for small Holder coefficient perturbations
c298c25b feat: bound frozen elliptic inverse uniformly by ellipticity
d019de04 feat: construct frozen elliptic continuous linear solution operator
```

Exit code: `0`.

</details>

<details>
<summary>033-receipt</summary>

```sh
python3 /private/tmp/near-frozen-evidence/receipt.py
```

```text
$ git status --short --branch
## worker/near-frozen-parabolic-right-inverse
exit=0
$ git rev-parse HEAD
5c1f77a4c417fd194622b3a7b5b989609c045da9
exit=0
$ git worktree list --porcelain
worktree /Users/mjkang/Develop/poincare
HEAD 571442448b8afd8484cd770e22944f54daec05e5
branch refs/heads/main

worktree /private/tmp/poincare-workers/finite-atlas-parametrix-survey
HEAD 6a69ba044e45ae9bfc534c2a5b0c43f8adc641a5
branch refs/heads/worker/finite-atlas-parametrix-survey

worktree /private/tmp/poincare-workers/near-frozen-parabolic-right-inverse
HEAD 5c1f77a4c417fd194622b3a7b5b989609c045da9
branch refs/heads/worker/near-frozen-parabolic-right-inverse

worktree /Users/mjkang/.codex/worktrees/focused-job-gates/poincare
HEAD a87c80a6ff90952ad633b894ef6fc467e60c8ee6
branch refs/heads/codex/focused-job-gates

worktree /Users/mjkang/.codex/worktrees/formalization-until-6/poincare
HEAD 64c9f999c9c699cb52e87ea36fad294d43b774d4
branch refs/heads/codex/formalization-until-6

worktree /Users/mjkang/.codex/worktrees/frozen-statement-contracts/poincare
HEAD b6fd0aa7d6865696f69b1c03c82d507fd4b5f5d7
branch refs/heads/codex/frozen-statement-contracts

worktree /Users/mjkang/.codex/worktrees/grounded-topology-consumer/poincare
HEAD ed7052816a46ee5a2328364b421d411edd3f401f
branch refs/heads/codex/grounded-topology-consumer

worktree /Users/mjkang/.codex/worktrees/harness-throughput/poincare
HEAD 3d8dc9f20a5b943d1fc55019ad968713947ca137
branch refs/heads/codex/harness-throughput

worktree /Users/mjkang/.codex/worktrees/poincare-interrupted-evidence
HEAD 81cde04465ad1a0e6144c0d219e62d4cfd7ed7d3
branch refs/heads/codex/allow-repeated-interrupted-task-block

worktree /Users/mjkang/.codex/worktrees/proof-workflow-improvements/poincare
HEAD 5d408763930e07ab9237c5c889056064bbe398ec
branch refs/heads/codex/proof-workflow-improvements

worktree /Users/mjkang/.codex/worktrees/theorem-dependency-registry/poincare
HEAD 64351986f66e9654ea233d0eab90acd4ae57df4b
branch refs/heads/codex/theorem-dependency-registry

exit=0
$ lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
exit=0
$ git -C .lake/packages/mathlib rev-parse HEAD
7175569c842f9164564bd76ff8b207e7b4705522
exit=0
$ git -C .lake/packages/mathlib remote get-url origin
https://github.com/leanprover-community/mathlib4.git
exit=0
SOURCE_SHA256=8cf6a3468b88ae4fd75cca35c4fe20c3082b3fca0f7984f3e13ab3d81230a985
```

Exit code: `0`.

</details>

## Probe source appendix

<details>
<summary>001-dependencies_dependencies.lean</summary>

SHA-256: `8c22754bb27333e58a449a0b29b90171c2b2505af72658c9ae1c2c285d87abf7`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse
set_option pp.proofs false
#print Poincare.FrozenEllipticHeatOperator.mapHolder
#print Poincare.FrozenEllipticHeatOperator.norm_mapHolder_le
#print Poincare.FrozenEllipticHeatOperator.norm_forcing_pullback_le
#print Poincare.FrozenEllipticHeatOperator.mapGraph
#print Poincare.FrozenEllipticHeatOperator.norm_mapGraph_le
#print Poincare.FrozenEllipticHeatOperator.trace_pullback
#print Poincare.FrozenEllipticHeatOperator.exists_symmetric_factor
#print Poincare.FrozenEllipticHeatOperator.factor_norm_bounds
#print Poincare.FrozenEllipticHeatOperator.exists_frozen_solution_graph_bound
#print Poincare.NearIdentityParabolicRightInverse.multiplier
#print Poincare.NearIdentityParabolicRightInverse.multiplier_apply
#print Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le
#print Poincare.NearIdentityParabolicRightInverse.neumann_data_eq
#print Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two
#print Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant
#print Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution
#print Poincare.DuhamelSolutionOperatorCLM.duhamelOperator
#print Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves
#print Poincare.DuhamelSolutionOperatorCLM.boundConstant
#print Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec
#print Poincare.ParabolicSolutionGraph.Graph.ext_of_u
#print Poincare.ParabolicHolderMultiplier.norm_error_le
#print Poincare.ParabolicHolderMultiplier.forcing_apply
#print Poincare.ParabolicHolder.ext
#print Poincare.ParabolicHolder.add_apply
#print Poincare.ParabolicHolder.smul_apply
#print Poincare.ParabolicHolder.ofFunction_apply
#print Poincare.ParabolicHolder.supNorm_nonneg
#print Poincare.ParabolicHolder.holderSeminorm_nonneg
#print Poincare.ParametrixNeumannCorrection.correctedInverse
```

</details>

<details>
<summary>002-pullbacks_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `9c6f9590d306bf2753bf02b976209960ce3948c038ddb312ac5f25882fc3a45d`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y (E := E) α T ℝ →L[ℝ] Y (E := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y (E := E) α T ℝ →ₗ[ℝ] Y (E := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph (E := E) α T →L[ℝ] Graph (E := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y (E := E) α T ℝ →L[ℝ] Graph (E := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y (E := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>005-pullbacks_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `ed416da484a57a01e2cab9b5d045dd99bfa6f52bf5088c830ee20a90eef126cb`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>006-pullbacks-gates-0_006-pullbacks-gates-audit.lean</summary>

SHA-256: `f934ca2463db5f825b8df3b53ac162510e0c2cfd4d5a21fc72725c5d64434e0a`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

end Poincare.NearFrozenParabolicRightInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if `Poincare.NearFrozenParabolicRightInverse.isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>007-pullbacks-gates-0_007-pullbacks-gates-audit.lean</summary>

SHA-256: `ffd02b613ab6ecd10f55100b54a635706caf60ad6d4a006425d7a7b9a773ed8c`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

end Poincare.NearFrozenParabolicRightInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.NearFrozenParabolicRightInverse).isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>008-frozen-bound_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `4363a3285b01c7243add86747c073dea966bde66e9f453345c10b62599454c95`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>009-frozen-bound-gates-0_009-frozen-bound-gates-audit.lean</summary>

SHA-256: `ba6d1e61f4acb180e375af5b2b00409472401cfe8a57ec8fcdd0ba3f08238c94`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

end Poincare.NearFrozenParabolicRightInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.NearFrozenParabolicRightInverse).isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>010-mathlib-statements_mathlib-statements.lean</summary>

SHA-256: `47c92781db9db5c1571a51139a51414c927cd88d5b9497ab03b4d4c09fa2270b`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse
set_option pp.proofs false
#print ContinuousLinearMap.opNorm_le_bound
#print ContinuousLinearMap.le_opNorm
#print ContinuousLinearMap.opNorm_comp_le
#print ContinuousLinearMap.comp
#print LinearMap.mkContinuous
#print ContinuousLinearEquiv.coe_coe
#print ContinuousLinearEquiv.apply_symm_apply
#print ContinuousLinearMap.id_apply
#print mul_le_mul_of_nonneg_right
#print mul_le_mul_of_nonneg_left
#print mul_le_mul
#print max_le_max
#print pow_le_pow_left₀
#print Real.rpow_le_rpow
#print Real.rpow_nonneg
#print norm_nonneg
#print Finset.sum_add_distrib
#print add_mul
#print congrArg
#print mul_pos
#print div_pos
#print le_of_lt
#print mul_div_cancel₀
```

</details>

<details>
<summary>011-neumann_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `568b1235681e2ef96cf1b5ba02ef335695231f99f87a6161b1abb7a2f56dc3b1`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>012-neumann-gates-0_012-neumann-gates-audit.lean</summary>

SHA-256: `1f7e98a840b5d4eabea87995eda78b8538d3882fe22feef3c30f1f45019a63d1`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

end Poincare.NearFrozenParabolicRightInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.NearFrozenParabolicRightInverse).isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>013-existence_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `08312d23e945050437fc19b7b76d3cf9720d06de720c48fe0e6b16f25a38ffba`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) *
              (S f).ddu (t, x) (e i) (e j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    <;> ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>014-existence-clean_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `07ab264829e853c1714c19e207f992970ff703f4b1ddc1143a25172e3317a657`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) *
              (S f).ddu (t, x) (e i) (e j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>015-exact-target_exact-target.lean</summary>

SHA-256: `abc474c0731d15362cc6d7064f7151b1869e43655018462a3574e5135d23c101`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) *
              (S f).ddu (t, x) (e i) (e j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse

namespace Poincare.NearFrozenParabolicRightInverse
open Set
local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
example :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := exists_nearFrozen_solution
end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>016-existence-gates-0_016-existence-gates-audit.lean</summary>

SHA-256: `1c49df01a8386b1c03a6bcf333c937fe36751fe6d495c0574fb2e1c0f2e2a2f4`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : E →L[ℝ] E) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := E) α T ℝ →ₗ[ℝ] Y («E» := E) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : E →L[ℝ] E) :
    Graph («E» := E) α T →L[ℝ] Graph («E» := E) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := E) α T →ₗ[ℝ] Graph («E» := E) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : E ≃L[ℝ] E) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  (graphPullback hα.le hT (S.symm : E →L[ℝ] E)).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : E →L[ℝ] E)))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : Bilin) (S : E ≃L[ℝ] E)
    (hS : ∀ v w : E, inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : E, A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) (e i) (e j) := by
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A (e i) (e j) *
      H.ddu (t, S.symm x) (S.symm (e i)) (S.symm (e j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : E ≃L[ℝ] E)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : E →L[ℝ] E)‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : E →L[ℝ] E) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : E →L[ℝ] E) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : E →L[ℝ] E) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : E →L[ℝ] E) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) *
        max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : E →L[ℝ] E)‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Bilin), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : E →L[ℝ] E)‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : E →L[ℝ] E)‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : Bilin)
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A (e i) (e j) * (P f).ddu (t, x) (e i) (e j))
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) (e i) (e j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := E) α T ℝ →L[ℝ] Y («E» := E) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := E) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A (e i) (e j) + b i j (t, x)) *
      (P g).ddu (t, x) (e i) (e j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
    (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : E,
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) *
              (S f).ddu (t, x) (e i) (e j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.NearFrozenParabolicRightInverse).isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>019-module-audit_module-audit.lean</summary>

SHA-256: `76e91aac87869791424f65921bf156ab0f0416c0e8ac42bbab22381e85c878ed`.

```lean
import Poincare.Global.NearFrozenParabolicRightInverse
set_option pp.proofs false
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.NearFrozenParabolicRightInverse
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print $(mkIdent n)))
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>020-without-notation_NearFrozenParabolicRightInverse.lean</summary>

SHA-256: `8cf6a3468b88ae4fd75cca35c4fe20c3082b3fca0f7984f3e13ab3d81230a985`.

```lean
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.NearIdentityParabolicRightInverse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false

namespace Poincare.NearFrozenParabolicRightInverse

open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
open DuhamelSolutionOperatorCLM

variable {α T : ℝ}

/-- Spatial substitution on scalar forcing is a bounded linear map. -/
def holderPullback (hα : 0 ≤ α) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ :=
  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
     map_add' := fun f g => by
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c f => by
       apply ParabolicHolder.ext
       intro p _
       rfl } : Y («E» := (ClosedSmoothModel 3)) α T ℝ →ₗ[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ).mkContinuous
    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)

/-- Pullback preserves the linear structure of genuine derivative graphs. -/
def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
    Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  ({ toFun := mapGraph hα S
     map_add' := fun G H => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl
     map_smul' := fun c G => by
       apply Graph.ext_of_u hT
       apply ParabolicHolder.ext
       intro p _
       rfl } : Graph («E» := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T).mkContinuous
    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)

/-- The heat inverse conjugated by the symmetric elliptic factor. -/
def frozenInverse (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3)) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  (graphPullback hα.le hT (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))).comp
    ((duhamelOperator α T hα hα1 hT hT1).comp
      (holderPullback hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))))

/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
theorem frozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
    (hS : ∀ v w : (ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w))
    (hA : ∀ v w : (ClosedSmoothModel 3), A v w = inner ℝ (S v) (S w))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  intro t ht x
  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
  change H.ut (t, S.symm x) = f (t, x) +
    ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
      H.ddu (t, S.symm x) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
  simp_rw [hA]
  rw [trace_pullback S hS]
  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq

/-- The conjugated norm records only the heat bound and spatial distortions. -/
theorem frozenInverse_norm_le (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖frozenInverse S hα hα1 hT hT1‖ ≤
      (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
        boundConstant α hα hα1 * max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) := by
  have hC := (boundConstant_spec α hα hα1).1
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
  let H := duhamelOperator α T hα hα1 hT hT1 g
  have hg := norm_forcing_pullback_le hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) f
  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right
        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
        (norm_nonneg g))
  change ‖mapGraph hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H‖ ≤ _
  apply (norm_mapGraph_le hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H).trans
  calc
    _ ≤ (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
        (boundConstant α hα hα1 * (max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) * ‖f‖)) :=
      mul_le_mul_of_nonneg_left
        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
    _ = _ := by ring

/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
theorem exists_frozen_operator_bound :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ D : ℝ, 0 < D ∧ ∀ (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A v w = A w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ 1 →
      ∃ P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
          (P f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
        ‖P‖ ≤ D := by
  intro α hα hα1 μ Λ hμ hμΛ
  let q := 1 / Real.sqrt μ
  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
  have hC := (boundConstant_spec α hα hα1).1
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro A hSym hlo hhi T hT hT1
  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
  refine ⟨frozenInverse S hα hα1 hT hT1,
    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
  have hI2 : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) ≤ max 1 (q ^ 2) :=
    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
  have hIa : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 (q ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
  have hSa : max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
  apply mul_le_mul _ hSa (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le

/-- Correct a frozen inverse using the original coefficient multiplier. -/
def nearFrozenInverse
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
  ParametrixNeumannCorrection.correctedInverse P
    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR

/-- The correction adds the perturbation to the frozen coefficients exactly. -/
theorem nearFrozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ))
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (P f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
          (nearFrozenInverse P b hR f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
  let g := (↑((Units.oneSub R hR)⁻¹) :
    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ) f
  intro t ht x
  have hg := congrArg (fun v : Y («E» := (ClosedSmoothModel 3)) α T ℝ => v (t, x))
    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
  change g (t, x) = f (t, x) +
    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
  change (P g).ut (t, x) = f (t, x) +
    ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
      (P g).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
  rw [hP g t ht x, hg]
  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- A half-size multiplier error increases the frozen bound by at most two. -/
theorem nearFrozenInverse_norm_le
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
    {D : ℝ} (hP : ‖P‖ ≤ D) :
    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
  have hD : 0 ≤ D := (norm_nonneg P).trans hP
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  calc
    _ ≤ D * 2 := mul_le_mul hP
      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
      (norm_nonneg _) hD
    _ = _ := mul_comm _ _

/-- The original split Hölder bound controls the frozen error uniformly. -/
theorem frozen_error_small
    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
    (hP : ‖P‖ ≤ D)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
    (hε : 9 * D * ε ≤ 1 / 4)
    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
  have hD := (norm_nonneg P).trans hP
  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
      9 * D * (ε + Λb * T ^ (α / 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
  constructor <;> nlinarith only [hn, hε, hΛ]

/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
theorem exists_nearFrozen_operator :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
    ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
      Λb * T ^ (α / 2) ≤ ε₀ →
      ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
          (S f).ut (t, x) = f (t, x) +
            ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
              (S f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧ ‖S‖ ≤ C := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
    ring
  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
    calc
      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ ≤ _ := hε
  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
    nearFrozenInverse_norm_le P b hR hhalf hPN⟩

/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
theorem exists_nearFrozen_solution :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T,
      (∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3), G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) * G.ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
      ‖G‖ ≤ C * ‖f‖ := by
  intro α hα hα1 μ Λ hμ hμΛ
  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
  exact ⟨S f, hS f, (S.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩

end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>021-linear-map-grep_ContinuousLinearMap.lean</summary>

SHA-256: `bb26ac2b8a771841cb6dc83fd8d04865da3e1d66eb68249056a51a0d3b283272`.

```lean
/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Constructions of continuous linear maps between (semi-)normed spaces

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`LinearMap` `f : E →ₛₗ[σ] F` is the coercion of some `ContinuousLinearMap` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `LinearMap.mkContinuous`, boundedness implies continuity. The
other direction, `ContinuousLinearMap.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`ContinuousLinearMap.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `LinearMap.mkContinuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

@[expose] public section

open Metric ContinuousLinearMap

open Set Real

open NNReal

variable {𝕜 𝕜₂ E F G : Type*}

/-! ## General constructions -/

section SeminormedAddCommGroup

variable [Ring 𝕜] [Ring 𝕜₂]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 G]
variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`LinearMap.mkContinuous_norm_le`. -/
def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `LinearMap.mkContinuous` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous_norm_le`. -/
def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩

theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₗ[𝕜] G :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

@[simp, norm_cast]
theorem LinearMap.mkContinuous_coe (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuous C h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
theorem LinearMap.mkContinuous_apply (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuous C h x = f x :=
  rfl

@[simp, norm_cast]
theorem LinearMap.mkContinuousOfExistsBound_coe (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuousOfExistsBound h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
theorem LinearMap.mkContinuousOfExistsBound_apply (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuousOfExistsBound h x = f x :=
  rfl

namespace ContinuousLinearMap

theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound _ h

theorem bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : AntilipschitzWith K f) (x) :
    ‖x‖ ≤ K * ‖f x‖ :=
  ZeroHomClass.bound_of_antilipschitz _ h x

end ContinuousLinearMap

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
    (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv

end

end SeminormedAddCommGroup

section SeminormedBounded
variable [SeminormedRing 𝕜] [Ring 𝕜₂] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite-dimensional domain
in `LinearMap.toContinuousLinearMap`. -/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul, f.map_smul, mul_comm]; exact norm_smul_le _ _

@[simp]
theorem LinearMap.toContinuousLinearMap₁_coe (f : 𝕜 →ₗ[𝕜] E) :
    (f.toContinuousLinearMap₁ : 𝕜 →ₗ[𝕜] E) = f :=
  rfl

@[simp]
theorem LinearMap.toContinuousLinearMap₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
    f.toContinuousLinearMap₁ x = f x :=
  rfl

end SeminormedBounded

section Normed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

theorem ContinuousLinearMap.isUniformEmbedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    IsUniformEmbedding f :=
  (AddMonoidHomClass.antilipschitz_of_bound f hf).isUniformEmbedding f.uniformContinuous

end Normed

/-! ## Homotheties -/

section Seminormed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- A (semi-)linear map which is a homothety is a continuous linear map.
Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
for the other theorems about homotheties in this file.
-/
def ContinuousLinearMap.ofHomothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀ x, ‖f x‖ = a * ‖x‖) :
    E →SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

theorem ContinuousLinearEquiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
    (∀ x : E, ‖f x‖ = a * ‖x‖) → ∀ y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖ := by
  intro hf y
  calc
    ‖f.symm y‖ = a⁻¹ * (a * ‖f.symm y‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_lt ha).symm, one_mul]
    _ = a⁻¹ * ‖f (f.symm y)‖ := by rw [hf]
    _ = a⁻¹ * ‖y‖ := by simp

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
noncomputable def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le

end Seminormed
```

</details>

<details>
<summary>021-linear-map-grep_Equiv.lean</summary>

SHA-256: `aa9303f6dd87e253402b2425cdb68db29aedeab37c1606dc76356f666deb7146`.

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.LinearMapPiProd

/-!
# Continuous linear equivalences

Continuous semilinear / linear / star-linear equivalences between topological modules are denoted
by `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise
open scoped Ring

universe u v w u'

section

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological semiring `R`. -/
structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous toFun := by first | fun_prop | dsimp; fun_prop
  continuous_invFun : Continuous invFun := by first | fun_prop | dsimp; fun_prop

attribute [inherit_doc ContinuousLinearEquiv] ContinuousLinearEquiv.continuous_toFun
ContinuousLinearEquiv.continuous_invFun

@[inherit_doc]
notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

@[inherit_doc]
notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

/-- `ContinuousSemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear equivs `M → M₂`.  See also `ContinuousLinearEquivClass F R M M₂` for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outParam Type*}
    [Semiring R] [Semiring S] (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [EquivLike F M M₂] : Prop extends SemilinearEquivClass F σ M M₂ where
  map_continuous : ∀ f : F, Continuous f := by first | fun_prop | dsimp; fun_prop
  inv_continuous : ∀ f : F, Continuous (EquivLike.inv f) := by first | fun_prop | dsimp; fun_prop

attribute [inherit_doc ContinuousSemilinearEquivClass]
ContinuousSemilinearEquivClass.map_continuous
ContinuousSemilinearEquivClass.inv_continuous

/-- `ContinuousLinearEquivClass F σ M M₂` asserts `F` is a type of bundled continuous
`R`-linear equivs `M → M₂`. This is an abbreviation for
`ContinuousSemilinearEquivClass F (RingHom.id R) M M₂`. -/
abbrev ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

namespace ContinuousSemilinearEquivClass

variable (F : Type*) {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M] [Module S M₂]

-- `σ'` becomes a metavariable, but it's OK since it's an outparam
instance (priority := 100) continuousSemilinearMapClass [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : ContinuousSemilinearMapClass F σ M M₂ :=
  { s with }

instance (priority := 100) [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : HomeomorphClass F M M₂ :=
  { s with }

end ContinuousSemilinearEquivClass

namespace ContinuousLinearMap

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

variable (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, (proj i : (∀ i, φ i) →L[R] φ i).ker : Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      Continuous.comp (continuous_apply (A := φ) i) <| continuous_subtype_val
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

end Pi

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoid

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

/-- A continuous linear equivalence induces a continuous linear map. -/
@[coe]
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance ContinuousLinearMap.coe : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨toContinuousLinearMap⟩

instance equivLike :
    EquivLike (M₁ ≃SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance continuousSemilinearEquivClass :
    ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

@[simp]
theorem coe_mk (e : M₁ ≃ₛₗ[σ₁₂] M₂) (a b) : ⇑(ContinuousLinearEquiv.mk e a b) = e := rfl

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl

@[simp, norm_cast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
  rfl

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  toLinearEquiv_injective <| LinearEquiv.ext <| congr_fun h

theorem coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun _e _e' h => ext <| funext <| ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/-- A continuous linear equivalence induces a homeomorphism. -/
def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl

theorem isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e :=
  (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s

theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s

@[simp]
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image

theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x

-- Make some straightforward lemmas available to `simp`.
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero

theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y

@[simp]
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x

theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x

theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_toFun

protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.continuous.continuousOn

protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.continuous.continuousAt

protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.continuous.continuousWithinAt

theorem comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _

theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

/-- An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext <| funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R₁ M]

/-- A continuous linear equivalence seen as a `ContinuousAddEquiv`. -/
def toContinuousAddEquiv (e : M₁ ≃L[R₁] M) : M₁ ≃ₜ+ M :=
  e.toAddEquiv.toContinuousAddEquiv fun _ ↦ e.toHomeomorph.isOpen_preimage

@[simp]
lemma toContinuousAddEquiv_coe (e : M₁ ≃L[R₁] M) : ⇑e.toContinuousAddEquiv = e := rfl

end

section

variable (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

@[simp]
theorem refl_apply (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl

end

@[simp, norm_cast]
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence -/
@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
theorem toLinearEquiv_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  rfl

@[simp]
theorem coe_symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

@[simp]
theorem toHomeomorph_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  rfl

@[simp]
theorem coe_symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph.symm = e.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun → apply, invFun → symm_apply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
    continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun }

@[simp]
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv := by
  ext
  rfl

/-- Product of two continuous linear equivalences. The map comes from `Equiv.prodCongr`. -/
def prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  { e.toLinearEquiv.prodCongr e'.toLinearEquiv with
    continuous_toFun := e.continuous_toFun.prodMap e'.continuous_toFun
    continuous_invFun := e.continuous_invFun.prodMap e'.continuous_invFun }

@[simp, norm_cast]
theorem prodCongr_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prodCongr e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prodCongr [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prodCongr e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prodMap (e' : M₃ →L[R₁] M₄) :=
  rfl

theorem prodCongr_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prodCongr e').symm = e.symm.prodCongr e'.symm :=
  rfl

variable (R₁ M₁ M₂)

/-- Product of modules is commutative up to continuous linear isomorphism. -/
@[simps! apply toLinearEquiv]
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ :=
  { LinearEquiv.prodComm R₁ M₁ M₂ with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

section prodAssoc

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
lemma prodAssoc_toLinearEquiv :
    (prodAssoc R M₁ M₂ M₃).toLinearEquiv = LinearEquiv.prodAssoc R M₁ M₂ M₃ := rfl

@[simp]
lemma coe_prodAssoc :
    (prodAssoc R M₁ M₂ M₃ : (M₁ × M₂) × M₃ → M₁ × M₂ × M₃) = Equiv.prodAssoc M₁ M₂ M₃ := rfl

@[simp]
lemma prodAssoc_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    prodAssoc R M₁ M₂ M₃ ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

@[simp]
lemma prodAssoc_symm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) :
    (prodAssoc R M₁ M₂ M₃).symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃) := rfl

end prodAssoc

section prodProdProdComm

variable (R M₁ M₂ M₃ M₄ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]

/-- The product of topological modules is four-way commutative up to continuous linear isomorphism.
This is `LinearEquiv.prodProdProdComm` prodAssoc as a continuous linear equivalence. -/
def prodProdProdComm : ((M₁ × M₂) × M₃ × M₄) ≃L[R] (M₁ × M₃) × M₂ × M₄ where
  toLinearEquiv := LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem prodProdProdComm_symm :
    (prodProdProdComm R M₁ M₂ M₃ M₄).symm = prodProdProdComm R M₁ M₃ M₂ M₄ :=
  rfl

@[simp]
lemma prodProdProdComm_toLinearEquiv :
    (prodProdProdComm R M₁ M₂ M₃ M₄).toLinearEquiv = LinearEquiv.prodProdProdComm R M₁ M₂ M₃ M₄ :=
  rfl

@[simp]
lemma coe_prodProdProdComm :
    (prodProdProdComm R M₁ M₂ M₃ M₄ : (M₁ × M₂) × M₃ × M₄ → (M₁ × M₃) × M₂ × M₄) =
      Equiv.prodProdProdComm M₁ M₂ M₃ M₄ := rfl

@[simp]
lemma prodProdProdComm_apply (p₁ : M₁) (p₂ : M₂) (p₃ : M₃) (p₄ : M₄) :
    prodProdProdComm R M₁ M₂ M₃ M₄ ((p₁, p₂), p₃, p₄) = ((p₁, p₃), p₂, p₄) := rfl

end prodProdProdComm

section prodUnique

variable (R M N : Type*) [Semiring R]
  [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace N] [AddCommMonoid N]
  [Unique N] [Module R M] [Module R N]

/-- The natural equivalence `M × N ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.prodUnique` as a continuous linear equivalence. -/
def prodUnique : (M × N) ≃L[R] M where
  toLinearEquiv := LinearEquiv.prodUnique
  continuous_toFun := by
    change Continuous (Equiv.prodUnique M N)
    dsimp; fun_prop
  continuous_invFun := by
    change Continuous fun x ↦ (x, default)
    fun_prop

@[simp]
lemma coe_prodUnique : (prodUnique R M N).toEquiv = Equiv.prodUnique M N := rfl

@[simp]
lemma prodUnique_apply (x : M × N) : prodUnique R M N x = x.1 := rfl

@[simp]
lemma prodUnique_symm_apply (x : M) : (prodUnique R M N).symm x = (x, default) := rfl

/-- The natural equivalence `N × M ≃L[R] M` for any `Unique` type `N`.
This is `Equiv.uniqueProd` as a continuous linear equivalence. -/
def uniqueProd : (N × M) ≃L[R] M where
  toLinearEquiv := LinearEquiv.uniqueProd
  continuous_toFun := by
    change Continuous (Equiv.uniqueProd M N)
    dsimp; fun_prop
  continuous_invFun := by
    change Continuous fun x ↦ (default, x)
    fun_prop

@[simp]
lemma coe_uniqueProd : (uniqueProd R M N).toEquiv = Equiv.uniqueProd M N := rfl

@[simp]
lemma uniqueProd_apply (x : N × M) : uniqueProd R M N x = x.2 := rfl

@[simp]
lemma uniqueProd_symm_apply (x : M) : (uniqueProd R M N).symm x = (default, x) := rfl

end prodUnique

variable {R₁ M₁ M₂}

protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.bijective

protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.injective

protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.surjective

@[simp]
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

@[simp]
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b

@[simp] theorem symm_trans_self (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.trans e = .refl R₂ M₂ :=
  ext <| funext fun _ ↦ apply_symm_apply _ _

@[simp] theorem self_trans_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.trans e.symm = .refl R₁ M₁ :=
  ext <| funext fun _ ↦ symm_apply_apply _ _

@[simp]
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

@[simp]
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' e '' s = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp, norm_cast]
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl

-- The priority should be higher than `comp_coe`.
@[simp high]
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

-- The priority should be higher than `comp_coe`.
@[simp high]
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

@[simp]
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (ContinuousLinearEquiv.symm : (M₁ ≃SL[σ₁₂] M₂) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl

theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

protected lemma image_eq_preimage_symm (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage_symm s

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' e ⁻¹' s = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' e.symm ⁻¹' s = s :=
  e.symm.symm_preimage_preimage s

lemma isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e :=
  e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

protected theorem _root_.LinearEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁]
    [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂]
    [IsUniformAddGroup E₁] [IsUniformAddGroup E₂] (e : E₁ ≃ₛₗ[σ₁₂] E₂)
    (h₁ : Continuous e) (h₂ : Continuous e.symm) : IsUniformEmbedding e :=
  ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other. See also `equivOfInverse'`. -/
def equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    continuous_toFun := f₁.continuous
    invFun := f₂
    continuous_invFun := f₂.continuous
    left_inv := h₁
    right_inv := h₂ }

@[simp]
theorem equivOfInverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
theorem symm_equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl

/-- Create a `ContinuousLinearEquiv` from two `ContinuousLinearMap`s that are
inverse of each other, in the `ContinuousLinearMap.comp` sense. See also `equivOfInverse`. -/
def equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h₁ : f₁.comp f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂ :=
  equivOfInverse f₁ f₂
    (fun x ↦ by simpa using congr($(h₂) x)) (fun x ↦ by simpa using congr($(h₁) x))

@[simp]
theorem equivOfInverse'_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse' f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

/-- The inverse of `equivOfInverse'` is obtained by swapping the order of its parameters. -/
@[simp]
theorem symm_equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse' f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁ :=
  rfl

theorem eq_comp_toContinuousLinearMap_symm (e₁₂ : M₁ ≃SL[σ₁₂] M₂) [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃]
    (f : M₂ →SL[σ₂₃] M₃) (g : M₁ →SL[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toContinuousLinearMap ↔ f.comp e₁₂.toContinuousLinearMap = g := by
  aesop

theorem eq_toContinuousLinearMap_symm_comp {e₁₂ : M₁ ≃SL[σ₁₂] M₂} [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
    (f : M₃ →SL[σ₃₁] M₁) (g : M₃ →SL[σ₃₂] M₂) :
    f = e₁₂.symm.toContinuousLinearMap.comp g ↔ e₁₂.toContinuousLinearMap.comp f = g := by
  aesop

variable (M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
instance automorphismGroup : Group (M₁ ≃L[R₁] M₁) where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := rfl
  mul_one f := rfl
  one_mul f := rfl
  inv_mul_cancel f := ext <| funext fun _ ↦ f.left_inv _

variable {M₁} {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

/-- The continuous linear equivalence between `ULift M₁` and `M₁`.

This is a continuous version of `ULift.moduleEquiv`. -/
def ulift : ULift M₁ ≃L[R₁] M₁ :=
  { ULift.moduleEquiv with
    continuous_toFun := continuous_uliftDown
    continuous_invFun := continuous_uliftUp }

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) where
  toFun f := (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

/-- A pair of continuous (semi)linear equivalences generates a linear equivalence between the spaces
of continuous linear maps. See also `ContinuousLinearEquiv.arrowCongr`. -/
@[simps]
def arrowCongrEquivₛₗ [SMulCommClass R₃ R₃ M₃] [SMulCommClass R₄ R₄ M₄]
    [ContinuousAdd M₃] [ContinuousConstSMul R₃ M₃] [ContinuousAdd M₄] [ContinuousConstSMul R₄ M₄]
    (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ₛₗ[σ₄₃] (M₂ →SL[σ₂₃] M₃) where
  toEquiv := arrowCongrEquiv e₁₂ e₄₃
  map_add' := by simp
  map_smul' := by simp

section Pi

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.
This is `Equiv.piCongrLeft` as a `ContinuousLinearEquiv`.
-/
def piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*}
    (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃L[R] (i : ι) → φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

/-- The product over `S ⊕ T` of a family of topological modules
is isomorphic (topologically and algebraically) to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `ContinuousLinearEquiv`.
-/
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*)
    (A : S ⊕ T → Type*) [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
    [∀ st, TopologicalSpace (A st)] :
    ((st : S ⊕ T) → A st) ≃L[R] ((s : S) → A (Sum.inl s)) × ((t : T) → A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

/-- The product `Π t : α, f t` of a family of topological modules is isomorphic
(both topologically and algebraically) to the space `f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `ContinuousLinearEquiv`.
-/
@[simps! -fullyApplied]
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] [∀ x, TopologicalSpace (f x)] :
    (Π t, f t) ≃L[R] f default where
  __ := LinearEquiv.piUnique R f
  __ := Homeomorph.piUnique f

end Pi

section piCongrRight

variable {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R₁ (M i)] {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)]
  [∀ i, Module R₁ (N i)] (f : (i : ι) → M i ≃L[R₁] N i)

/-- Combine a family of continuous linear equivalences into a continuous linear equivalence of
pi-types. -/
def piCongrRight : ((i : ι) → M i) ≃L[R₁] (i : ι) → N i :=
  { LinearEquiv.piCongrRight fun i ↦ f i with
    continuous_toFun := by
      exact continuous_pi fun i ↦ (f i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun := by
      exact continuous_pi fun i => (f i).continuous_invFun.comp (continuous_apply i) }

@[simp]
theorem piCongrRight_apply (m : (i : ι) → M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem piCongrRight_symm_apply (n : (i : ι) → N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

section DistribMulAction

variable {G : Type*} [Group G] [DistribMulAction G M₁] [ContinuousConstSMul G M₁]
  [SMulCommClass G R₁ M₁]

/-- Scalar multiplication by a group element as a continuous linear equivalence. -/
@[simps! apply_toLinearEquiv apply_apply]
def smulLeft : G →* M₁ ≃L[R₁] M₁ where
  toFun g := ⟨DistribMulAction.toModuleAut _ _ g, continuous_const_smul _, continuous_const_smul _⟩
  map_mul' _ _ := toLinearEquiv_injective <| map_mul (DistribMulAction.toModuleAut _ _) _ _
  map_one' := toLinearEquiv_injective <| map_one <| DistribMulAction.toModuleAut _ _

end DistribMulAction

end AddCommMonoid

section Aut

/-!
### Automorphisms as continuous linear equivalences and as units of the ring of endomorphisms

The next theorems cover the identification between `M ≃L[R] M` and the group of units of the ring
`M →L[R] M`.
-/

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def ofUnit (f : (M →L[R] M)ˣ) : M ≃L[R] M where
  toLinearEquiv :=
    { toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp }
  continuous_toFun := f.val.continuous
  continuous_invFun := f.inv.continuous

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def toUnit (f : M ≃L[R] M) : (M →L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

variable (R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def unitsEquiv : (M →L[R] M)ˣ ≃* M ≃L[R] M where
  toFun := ofUnit
  invFun := toUnit
  map_mul' x y := by
    ext
    rfl

@[simp]
theorem unitsEquiv_apply (f : (M →L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M →L[R] M) x :=
  rfl

end Aut

section AutRing

/-!
### Units of a ring as linear automorphisms
-/

variable (R : Type*) [Semiring R] [TopologicalSpace R] [ContinuousMul R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`. -/
def unitsEquivAut : Rˣ ≃ R ≃L[R] R where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩
  left_inv u := Units.ext <| by simp
  right_inv e := ext₁ <| by simp

variable {R}

@[simp]
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl

@[simp]
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl

@[simp]
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl

end AutRing

section Pi

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/-- Continuous linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`.
-/
@[simps! -fullyApplied apply symm_apply]
def piFinTwo (M : Fin 2 → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : ((i : _) → M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied apply symm_apply]
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

section
variable {n : ℕ} {R : Type*} {M : Fin n.succ → Type*} {N : Type*}
variable [Semiring R]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

variable (R M) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps!]
def _root_.Fin.consEquivL : (M 0 × Π i, M (Fin.succ i)) ≃L[R] (Π i, M i) where
  __ := Fin.consLinearEquiv R M
  continuous_toFun := continuous_id.fst.finCons continuous_id.snd
  continuous_invFun := .prodMk (continuous_apply 0) (by fun_prop)

/-- `Fin.cons` in the codomain of continuous linear maps. -/
abbrev _root_.ContinuousLinearMap.finCons
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : N →L[R] M 0) (fs : N →L[R] Π i, M (Fin.succ i)) :
    N →L[R] Π i, M i :=
  Fin.consEquivL R M ∘L f.prod fs

end

end Pi

section AddCommGroup

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [IsTopologicalAddGroup M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  { e.toLinearEquiv.skewProd e'.toLinearEquiv ↑f with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prodMk
        ((e'.continuous_toFun.comp continuous_snd).add <| f.continuous.comp continuous_fst)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prodMk
        (e'.continuous_invFun.comp <|
          continuous_snd.sub <| f.continuous.comp <| e.continuous_invFun.comp continuous_fst) }

@[simp]
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl

@[simp]
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

variable (R) in
/-- The negation map as a continuous linear equivalence. -/
def neg [ContinuousNeg M] :
    M ≃L[R] M :=
  { LinearEquiv.neg R with
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }

@[simp]
theorem coe_neg [ContinuousNeg M] :
    (neg R : M → M) = -id := rfl

@[simp]
theorem neg_apply [ContinuousNeg M] (x : M) :
    neg R x = -x := by simp

@[simp]
theorem symm_neg [ContinuousNeg M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y

theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x

variable [Module R M₂] [IsTopologicalAddGroup M]

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × f₁.ker :=
  equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by simp [h x]

@[simp]
theorem fst_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
theorem snd_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem equivOfRightInverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂ × f₁.ker) :
    (equivOfRightInverse f₁ f₂ h).symm y = f₂ y.1 + y.2 :=
  rfl

end Ring

section RestrictScalars

/-- If M is an `R`-module and `S`-module and `R`-module structure is defined by an action of `R` on
`S` (formally, we have two scalar towers), then any `S`-linear equivalence on `M` is an `R`-linear
equivalence. -/
@[simps! toLinearEquiv apply symm_apply]
def restrictScalars (R : Type*) {S : Type*} {M : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M] [TopologicalSpace M]
    [LinearMap.CompatibleSMul M M R S] (f : M ≃L[S] M) : M ≃L[R] M where
  toLinearEquiv := f.toLinearEquiv.restrictScalars R
  continuous_invFun := f.continuous_invFun
  continuous_toFun := f.continuous_toFun

end RestrictScalars

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} {M M₂ M₃ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₂] [TopologicalSpace M₃]

variable [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
def IsInvertible (f : M →L[R] M₂) : Prop :=
  ∃ (A : M ≃L[R] M₂), A = f

open Classical in
/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ →L[R] M) else 0

@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M →L[R] M₂) := ⟨f, rfl⟩

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  simp [inverse]

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp] lemma inverse_of_not_isInvertible
    {f : M →L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dif_neg hf

@[simp]
theorem isInvertible_zero_iff :
    IsInvertible (0 : M →L[R] M₂) ↔ Subsingleton M ∧ Subsingleton M₂ := by
  refine ⟨fun ⟨e, he⟩ ↦ ?_, ?_⟩
  · have A : Subsingleton M := by
      refine ⟨fun x y ↦ e.injective ?_⟩
      simp [he, ← ContinuousLinearEquiv.coe_coe]
    exact ⟨A, e.toEquiv.symm.subsingleton⟩
  · rintro ⟨hM, hM₂⟩
    let e : M ≃L[R] M₂ :=
    { toFun := 0
      invFun := 0
      left_inv x := Subsingleton.elim _ _
      right_inv x := Subsingleton.elim _ _
      map_add' x y := Subsingleton.elim _ _
      map_smul' c x := Subsingleton.elim _ _ }
    refine ⟨e, ?_⟩
    ext x
    exact Subsingleton.elim _ _

@[simp] theorem inverse_zero : inverse (0 : M →L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M →L[R] M₂)
  · rcases isInvertible_zero_iff.1 h with ⟨hM, hM₂⟩
    ext x
    exact Subsingleton.elim _ _
  · exact inverse_of_not_isInvertible h

lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.of_inverse {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

lemma inverse_eq {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) :
    f.inverse = g := by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this, inverse_equiv]
  rfl

lemma IsInvertible.inverse_apply_eq {f : M →L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    ((e : M₂ →L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ →L[R] M₃) ∘L f) := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L (e : M₃ →L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ →L[R] M)) ∘L e.symm := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ →L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, zero_comp]

@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M →L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf, comp_zero]

lemma IsInvertible.inverse_comp_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, coe_comp', Function.comp_apply]

lemma IsInvertible.inverse_comp_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, coe_comp', Function.comp_apply]

@[simp]
theorem ringInverse_equiv (e : M ≃L[R] M) : (↑e)⁻¹ʳ = inverse (e : M →L[R] M) := by
  suffices ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M)⁻¹ʳ = inverse ↑e by
    convert this
  simp
  rfl

/-- The function `ContinuousLinearEquiv.inverse` can be written in terms of `Ring.inverse` for the
ring of self-maps of the domain. -/
theorem inverse_eq_ringInverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = ((e.symm : M₂ →L[R] M).comp f)⁻¹ʳ ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = (e'.trans e.symm : M →L[R] M)⁻¹ʳ ∘L (e.symm : M₂ →L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

theorem ringInverse_eq_inverse : Ring.inverse = inverse (R := R) (M := M) := by
  ext
  simp [inverse_eq_ringInverse (ContinuousLinearEquiv.refl R M)]

@[simp] theorem inverse_id : (ContinuousLinearMap.id R M).inverse = .id R M := by
  rw [← ringInverse_eq_inverse]
  exact Ring.inverse_one _

namespace IsInvertible

variable {f : M →L[R] M₂}

@[simp]
theorem self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem self_apply_inverse (hf : f.IsInvertible) (y : M₂) : f (f.inverse y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem inverse_apply_self (hf : f.IsInvertible) (y : M) : f.inverse (f y) = y := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem bijective (hf : f.IsInvertible) : Function.Bijective f := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

protected theorem injective (hf : f.IsInvertible) : Function.Injective f :=
  hf.bijective.injective

protected theorem surjective (hf : f.IsInvertible) : Function.Surjective f :=
  hf.bijective.surjective

protected theorem inverse (hf : f.IsInvertible) : f.inverse.IsInvertible := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
protected theorem inverse_inverse (hf : f.IsInvertible) : f.inverse.inverse = f := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem of_isInvertible_inverse (hf : f.inverse.IsInvertible) : f.IsInvertible := by
  by_contra H
  obtain ⟨_, _⟩ : Subsingleton M₂ ∧ Subsingleton M := by simpa [inverse, H] using hf
  simp_all [Subsingleton.elim f 0]

@[simp]
theorem _root_.ContinuousLinearMap.isInvertible_inverse_iff :
    f.inverse.IsInvertible ↔ f.IsInvertible :=
  ⟨.of_isInvertible_inverse, .inverse⟩

end IsInvertible

/-- Composition of a map on a product with the exchange of the product factors -/
theorem coprod_comp_prodComm [ContinuousAdd M] (f : M₂ →L[R] M) (g : M₃ →L[R] M) :
    f.coprod g ∘L ContinuousLinearEquiv.prodComm R M₃ M₂ = g.coprod f := by
  ext <;> simp

end ContinuousLinearMap

-- Restricting a continuous linear equivalence to a map between submodules.
section map

namespace ContinuousLinearEquiv

variable {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [TopologicalSpace M]
  [AddCommMonoid M₂] [TopologicalSpace M₂]
  {module_M : Module R M} {module_M₂ : Module R₂ M₂} {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- Continuous linear equivalence between two equal submodules:
this is `LinearEquiv.ofEq` as a continuous linear equivalence -/
def ofEq (p q : Submodule R M) (h : p = q) : p ≃L[R] q where
  toLinearEquiv := LinearEquiv.ofEq _ _ h
  continuous_toFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').continuous
  continuous_invFun := by
    have h' : (fun x ↦ x ∈ p) = (fun x ↦ x ∈ q) := by simp [h]
    exact (Homeomorph.ofEqSubtypes h').symm.continuous

/--
A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from any submodule `p` of the domain onto the image of that submodule.

This is the continuous linear version of `LinearEquiv.submoduleMap`.
This is `ContinuousLinearEquiv.ofSubmodule'` but with map on the right instead of comap on the left.
-/
def submoduleMap (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) :
    p ≃SL[σ₁₂] Submodule.map (e : M →ₛₗ[σ₁₂] M₂) p where
  __ := LinearEquiv.submoduleMap e.toLinearEquiv p
  continuous_toFun := map_continuous ((e.toContinuousLinearMap.comp p.subtypeL).codRestrict _ _)
  continuous_invFun := (map_continuous e.symm).restrict fun x hx ↦
    ((LinearEquiv.submoduleMap e.toLinearEquiv p).symm ⟨x, hx⟩).2

@[simp]
lemma submoduleMap_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    e.submoduleMap p x = e x := by
  rfl

@[simp]
lemma submoduleMap_symm_apply (e : M ≃SL[σ₁₂] M₂) (p : Submodule R M)
    (x : p.map (e : M →ₛₗ[σ₁₂] M₂)) :
    (e.submoduleMap p).symm x = e.symm x := by
  rfl

/-- A continuous linear equivalence which maps a submodule of one module onto another,
restricts to a continuous linear equivalence of the two submodules.
This is `LinearEquiv.ofSubmodules` as a continuous linear equivalence. -/
def ofSubmodules (e : M ≃SL[σ₁₂] M₂)
    (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) : p ≃SL[σ₁₂] q :=
  (e.submoduleMap p).trans (.ofEq _ _ h)

@[simp]
theorem ofSubmodules_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : p) :
    e.ofSubmodules p q h x = e x :=
  rfl

@[simp]
theorem ofSubmodules_symm_apply (e : M ≃SL[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : q) : (e.ofSubmodules p q h).symm x = e.symm x :=
  rfl

/-- A continuous linear equivalence of two modules restricts to a continuous linear equivalence
from the preimage of any submodule to that submodule.
This is `ContinuousLinearEquiv.ofSubmodule` but with `comap` on the left
instead of `map` on the right. -/
def ofSubmodule' (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃SL[σ₁₂] U :=
  f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.toLinearEquiv.symm) |>.symm

theorem ofSubmodule'_toContinuousLinearMap (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toContinuousLinearMap =
      (f.toContinuousLinearMap.comp ((U.comap f.toLinearMap).subtypeL)).codRestrict U
        ((fun ⟨x, hx⟩ ↦ by simpa [Submodule.mem_comap])) := by
  rfl

@[simp]
theorem ofSubmodule'_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) :
    (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
theorem ofSubmodule'_symm_apply (f : M ≃SL[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : U) :
    ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) := rfl

end ContinuousLinearEquiv

end map

namespace Submodule

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- If `p` is a closed complemented submodule,
then there exists a submodule `q` and a continuous linear equivalence `M ≃L[R] (p × q)` such that
`e (x : p) = (x, 0)`, `e (y : q) = (0, y)`, and `e.symm x = x.1 + x.2`.

In fact, the properties of `e` imply the properties of `e.symm` and vice versa,
but we provide both for convenience. -/
lemma ClosedComplemented.exists_submodule_equiv_prod [IsTopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    ∃ (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (∀ x : p, e x = (x, 0)) ∧ (∀ y : q, e y = (0, y)) ∧ (∀ x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨f.ker, .equivOfRightInverse f p.subtypeL hf,
    fun _ ↦ by ext <;> simp [hf], fun _ ↦ by ext <;> simp, fun _ ↦ rfl⟩

end Submodule

namespace MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [IsTopologicalSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M]

/-- The function `op` is a continuous linear equivalence. -/
@[simps!]
def opContinuousLinearEquiv : M ≃L[R] Mᵐᵒᵖ where
  __ := MulOpposite.opLinearEquiv R

end MulOpposite

namespace ContinuousLinearEquiv
variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V] [Module S V] [ContinuousConstSMul S V]
  [AddCommMonoid W] [Module R W] [TopologicalSpace W] [Module S W] [ContinuousConstSMul S W]
  [AddCommMonoid G] [Module R G] [TopologicalSpace G] [Module S G] [ContinuousConstSMul S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

/-- Left scalar multiplication of a unit and a continuous linear equivalence,
as a continuous linear equivalence. -/
instance : SMul Sˣ (V ≃L[R] W) where smul α e :=
  { __ := α • e.toLinearEquiv
    continuous_toFun := α.isUnit.continuous_const_smul_iff.mpr e.continuous
    continuous_invFun := α⁻¹.isUnit.continuous_const_smul_iff.mpr e.symm.continuous }

@[simp] theorem smul_apply (α : Sˣ) (e : V ≃L[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl

theorem symm_smul_apply (e : V ≃L[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl

@[simp] theorem symm_smul [SMulCommClass R S V]
    (e : V ≃L[R] W) (α : Sˣ) : (α • e).symm = α⁻¹ • e.symm := rfl

@[simp] theorem toLinearEquiv_smul (e : V ≃L[R] W) (α : Sˣ) :
    (α • e).toLinearEquiv = α • e.toLinearEquiv := rfl

theorem smul_trans [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V)
    (f : V ≃L[R] W) : (α • e).trans f = α • (e.trans f) := by
  ext; simp [LinearMapClass.map_smul_of_tower f]

theorem trans_smul [IsScalarTower S R G] (α : Sˣ) (e : G ≃L[R] V) (f : V ≃L[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

end ContinuousLinearEquiv
end
```

</details>

<details>
<summary>021-linear-map-grep_LinearMap.lean</summary>

SHA-256: `551705e41b4d87608c74c31e6370f5db4f6d46c309ce6fcde5c5145d64daee6c`.

```lean
/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Continuous linear maps

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `RingHom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.
-/

@[expose] public section

assert_not_exists TrivialStar

open LinearMap (ker range)
open Topology Filter Pointwise

universe u v w u'

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by fun_prop

attribute [inherit_doc ContinuousLinearMap] ContinuousLinearMap.cont

@[inherit_doc]
notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

@[inherit_doc]
notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

/-- `ContinuousSemilinearMapClass F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear maps `M → M₂`.  See also `ContinuousLinearMapClass F R M M₂` for the case where
`σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class ContinuousSemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam <| R →+* S) (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M]
    (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [FunLike F M M₂] : Prop
    extends SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂

/-- `ContinuousLinearMapClass F R M M₂` asserts `F` is a type of bundled continuous
`R`-linear maps `M → M₂`.  This is an abbreviation for
`ContinuousSemilinearMapClass F (RingHom.id R) M M₂`. -/
abbrev ContinuousLinearMapClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M₂] :=
  ContinuousSemilinearMapClass F (RingHom.id R) M M₂

/-- The *strong dual* of a topological vector space `M` over a ring `R`. This is the space of
continuous linear functionals and is equipped with the topology of uniform convergence
on bounded subsets. `StrongDual R M` is an abbreviation for `M →L[R] R`. -/
abbrev StrongDual (R : Type*) [Semiring R] [TopologicalSpace R]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M] [Module R M] : Type _ := M →L[R] R

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

attribute [coe] ContinuousLinearMap.toLinearMap
/-- Coerce continuous linear maps to linear maps. -/
instance LinearMap.coe : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) := ⟨toLinearMap⟩

theorem coe_injective : Function.Injective ((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) := by
  intro f g H
  cases f
  cases g
  congr

instance funLike : FunLike (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective' _ _ h := coe_injective (DFunLike.coe_injective h)

instance continuousSemilinearMapClass :
    ContinuousSemilinearMapClass (M₁ →SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f :=
  rfl

@[continuity, fun_prop]
protected theorem continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2

@[continuity, fun_prop]
protected theorem continuous_toLinearMap (f : M₁ →SL[σ₁₂] M₂) : Continuous f.toLinearMap :=
  f.2

@[simp]
protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (f : E₁ →SL[σ₁₂] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff

theorem coeFn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) (↑) :=
  DFunLike.coe_injective

theorem toContinuousAddMonoidHom_injective :
    Function.Injective ((↑) : (M₁ →SL[σ₁₂] M₂) → ContinuousAddMonoidHom M₁ M₂) :=
  (DFunLike.coe_injective.of_comp_iff _).1 DFunLike.coe_injective

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_inj {f g : M₁ →SL[σ₁₂] M₂} :
    (f : ContinuousAddMonoidHom M₁ M₂) = g ↔ f = g :=
  toContinuousAddMonoidHom_injective.eq_iff

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection]. -/
def Simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (toFun → apply, toLinearMap → coe, as_prefix coe)

@[ext]
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

/-- Copy of a `ContinuousLinearMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : M₁ →SL[σ₁₂] M₂ where
  toLinearMap := f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
theorem coe_copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

theorem range_coeFn_eq :
    Set.range ((⇑) : (M₁ →SL[σ₁₂] M₂) → (M₁ → M₂)) =
      {f | Continuous f} ∩ Set.range ((⇑) : (M₁ →ₛₗ[σ₁₂] M₂) → (M₁ → M₂)) := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩

lemma range_toLinearMap (f : M₁ →SL[σ₁₂] M₂) : Set.range f.toLinearMap = Set.range f := by simp

-- make some straightforward lemmas available to `simp`.
protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f

protected theorem map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y

@[simp]
protected theorem map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _

protected theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul (f : M₁ →ₗ[S] M₂) c x

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 <| LinearMap.ext_ring h

@[simp]
theorem apply_val_ker (f : M₁ →SL[σ₁₂] M₂) (x : f.ker) : f x = 0 := x.2

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `Submodule.span` of this set. -/
theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

/-- Under a continuous linear map, the image of the `TopologicalClosure` of a submodule is
contained in the `TopologicalClosure` of its image. -/
theorem _root_.Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤
      (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/-- If a continuous linear map stabilizes a submodule, then it stabilizes its topological
closure. -/
theorem _root_.Submodule.topologicalClosure_mem_invtSubmodule [TopologicalSpace R₁]
    [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] {f : M₁ →L[R₁] M₁} {s : Submodule R₁ M₁}
    (hs : s ∈ Module.End.invtSubmodule f) :
    s.topologicalClosure ∈ Module.End.invtSubmodule f := by
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hs ⊢
  exact (s.topologicalClosure_map f).trans (Submodule.topologicalClosure_mono hs)

/-- Under a dense continuous linear map, a submodule whose `TopologicalClosure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂]
    [TopologicalSpace R₁] [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁]
    [ContinuousSMul R₂ M₂] [ContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f)
    {s : Submodule R₁ M₁} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

section SMul

variable {S₂ T₂ : Type*}
variable [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]
variable [DistribSMul T₂ M₂] [SMulCommClass R₂ T₂ M₂] [ContinuousConstSMul T₂ M₂]

instance instSMul : SMul S₂ (M₁ →SL[σ₁₂] M₂) where
  smul c f := ⟨c • (f : M₁ →ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩

theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : S₂) (f : M₁ →SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp, norm_cast]
theorem coe_smul' (c : S₂) (f : M₁ →SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ → M₂) :=
  rfl

instance isScalarTower [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] :
    IsScalarTower S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance smulCommClass [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

end SMul

section SMulMonoid

variable {S₂ : Type*} [Monoid S₂]
variable [DistribMulAction S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]

instance mulAction : MulAction S₂ (M₁ →SL[σ₁₂] M₂) where
  one_smul _f := ext fun _x => one_smul _ _
  mul_smul _a _b _f := ext fun _x => mul_smul _ _ _

end SMulMonoid

/-- The continuous map that is constantly zero. -/
instance zero : Zero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

instance inhabited : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : M₁) : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[norm_cast]
theorem coe_zero' : ⇑(0 : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_zero :
    ((0 : M₁ →SL[σ₁₂] M₂) : ContinuousAddMonoidHom M₁ M₂) = 0 := rfl

instance uniqueOfLeft [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

instance uniqueOfRight [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

theorem exists_ne_zero {f : M₁ →SL[σ₁₂] M₂} (hf : f ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra! h
  exact hf (ContinuousLinearMap.ext h)

section

variable (R₁ M₁)

/-- the identity map as a continuous linear map. -/
protected def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end

instance one : One (M₁ →L[R₁] M₁) :=
  ⟨.id R₁ M₁⟩

theorem one_def : (1 : M₁ →L[R₁] M₁) = .id R₁ M₁ := rfl

theorem id_apply (x : M₁) : ContinuousLinearMap.id R₁ M₁ x = x := rfl

@[simp, norm_cast]
theorem coe_id : (ContinuousLinearMap.id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(ContinuousLinearMap.id R₁ M₁) = id :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : M₁ →L[R₁] M₁) : M₁ →ₗ[R₁] M₁) = 1 :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_id :
    (ContinuousLinearMap.id R₁ M₁ : ContinuousAddMonoidHom M₁ M₁) = .id _ := rfl

@[simp, norm_cast]
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = .id _ _ := by
  rw [← coe_id, coe_inj]

@[simp] theorem one_apply (x : M₁) : (1 : M₁ →L[R₁] M₁) x = x := rfl

instance [Nontrivial M₁] : Nontrivial (M₁ →L[R₁] M₁) :=
  ⟨0, 1, fun e ↦
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

section Add

variable [ContinuousAdd M₂]

instance add : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp]
theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
  rfl

@[simp, norm_cast]
theorem coe_add (f g : M₁ →SL[σ₁₂] M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g :=
  rfl

@[norm_cast]
theorem coe_add' (f g : M₁ →SL[σ₁₂] M₂) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_add (f g : M₁ →SL[σ₁₂] M₂) :
    ↑(f + g) = (f + g : ContinuousAddMonoidHom M₁ M₂) := rfl

-- The `AddMonoid` instance exists to help speedup unification
instance : AddMonoid (M₁ →SL[σ₁₂] M₂) where
  zero_add := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  add_zero := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  add_assoc := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  nsmul := (· • ·)
  nsmul_zero f := by
    ext
    simp
  nsmul_succ n f := by
    ext
    simp [add_smul]

instance addCommMonoid : AddCommMonoid (M₁ →SL[σ₁₂] M₂) where
  add_comm := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ↑(∑ d ∈ t, f d) = (∑ d ∈ t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
  map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[simp, norm_cast]
theorem coe_sum' {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ⇑(∑ d ∈ t, f d) = ∑ d ∈ t, ⇑(f d) := by simp only [← coe_coe, coe_sum, LinearMap.coe_sum]

theorem sum_apply {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) (b : M₁) :
    (∑ d ∈ t, f d) b = ∑ d ∈ t, f d b := by simp only [coe_sum', Finset.sum_apply]

end Add

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[simp, norm_cast]
theorem coe_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp, norm_cast]
theorem coe_comp' (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : ⇑(h.comp f) = h ∘ f :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (↑(h.comp f) : ContinuousAddMonoidHom M₁ M₃) = (h : ContinuousAddMonoidHom M₂ M₃).comp f := rfl

theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl

@[simp]
theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f.comp (.id R₁ M₁) = f :=
  ext fun _x => rfl

@[simp]
theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : (ContinuousLinearMap.id R₂ M₂).comp f = f :=
  ext fun _x => rfl

section

variable {R E F : Type*} [Semiring R]
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]

/-- `g ∘ f = id` as `ContinuousLinearMap`s implies `g ∘ f = id` as functions. -/
lemma leftInverse_of_comp {f : E →L[R] F} {g : F →L[R] E}
    (hinv : g.comp f = ContinuousLinearMap.id R E) : Function.LeftInverse g f := by
  simpa [← Function.rightInverse_iff_comp] using congr(⇑$hinv)

/-- `f ∘ g = id` as `ContinuousLinearMap`s implies `f ∘ g = id` as functions. -/
lemma rightInverse_of_comp {f : E →L[R] F} {g : F →L[R] E}
    (hinv : f.comp g = ContinuousLinearMap.id R F) : Function.RightInverse g f :=
  leftInverse_of_comp hinv

end

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 := by
  ext
  simp

@[simp]
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ →SL[σ₁₂] M₂) : g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  ext
  simp

@[simp]
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  ext
  simp

theorem comp_finsetSum {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : ι → M₁ →SL[σ₁₂] M₂) : g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by
  ext
  simp

@[deprecated (since := "2026-04-08")] alias comp_finset_sum := comp_finsetSum

theorem finsetSum_comp {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₃] (g : ι → M₂ →SL[σ₂₃] M₃)
    (f : M₁ →SL[σ₁₂] M₂) : (∑ i ∈ s, g i).comp f = ∑ i ∈ s, (g i).comp f := by
  ext
  simp only [coe_comp', coe_sum', Function.comp_apply, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_comp := finsetSum_comp

theorem comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
    {σ₃₄ : R₃ →+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

theorem cancel_left {g : M₂ →SL[σ₂₃] M₃} {f₁ f₂ : M₁ →SL[σ₁₂] M₂} (hg : Function.Injective g)
    (h : g.comp f₁ = g.comp f₂) : f₁ = f₂ := by
  ext x
  exact hg congr($h x)

instance instMul : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩

theorem mul_def (f g : M₁ →L[R₁] M₁) : f * g = f.comp g :=
  rfl

@[simp, norm_cast]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : (↑(f * g) : M₁ →ₗ[R₁] M₁) = f * g :=
  rfl

@[simp, norm_cast]
theorem coe_mul' (f g : M₁ →L[R₁] M₁) : ⇑(f * g) = f ∘ g :=
  rfl

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
  rfl

instance monoidWithZero : MonoidWithZero (M₁ →L[R₁] M₁) where
  mul_zero f := ext fun _ => map_zero f
  zero_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

@[simp, norm_cast]
theorem coe_pow' (f : M₁ →L[R₁] M₁) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

@[simp, norm_cast]
theorem coe_pow (f : M₁ →L[R₁] M₁) (n : ℕ) : (↑(f ^ n) : M₁ →ₗ[R₁] M₁) = f ^ n :=
  DFunLike.ext' <| (coe_pow' f n).trans <| .symm <| hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

instance instNatCast [ContinuousAdd M₁] : NatCast (M₁ →L[R₁] M₁) where
  natCast n := n • (1 : M₁ →L[R₁] M₁)

instance semiring [ContinuousAdd M₁] : Semiring (M₁ →L[R₁] M₁) where
  __ := ContinuousLinearMap.monoidWithZero
  __ := ContinuousLinearMap.addCommMonoid
  left_distrib f g h := ext fun x => map_add f (g x) (h x)
  right_distrib _ _ _ := ext fun _ => LinearMap.add_apply _ _ _
  toNatCast := instNatCast
  natCast_zero := zero_smul ℕ (1 : M₁ →L[R₁] M₁)
  natCast_succ n := AddMonoid.nsmul_succ n (1 : M₁ →L[R₁] M₁)

/-- `ContinuousLinearMap.toLinearMap` as a `RingHom`. -/
@[simps]
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ →L[R₁] M₁) →+* M₁ →ₗ[R₁] M₁ where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem natCast_apply [ContinuousAdd M₁] (n : ℕ) (m : M₁) : (↑n : M₁ →L[R₁] M₁) m = n • m :=
  rfl

@[simp]
theorem ofNat_apply [ContinuousAdd M₁] (n : ℕ) [n.AtLeastTwo] (m : M₁) :
    (ofNat(n) : M₁ →L[R₁] M₁) m = OfNat.ofNat n • m :=
  rfl

/-- Construct a homeomorphism from an invertible continuous linear map. -/
@[simps]
def homeomorphOfUnit (T : (M₁ →L[R₁] M₁)ˣ) : M₁ ≃ₜ M₁ where
  toFun := T.1
  invFun := T⁻¹.1
  left_inv x := by rw [← mul_apply, Units.inv_mul, one_apply]
  right_inv x := by rw [← mul_apply, Units.mul_inv, one_apply]

theorem isHomeomorph_of_isUnit {T : M₁ →L[R₁] M₁} (hT : IsUnit T) : IsHomeomorph T := by
  obtain ⟨T, rfl⟩ := hT
  exact (homeomorphOfUnit T).isHomeomorph

section ApplyAction

variable [ContinuousAdd M₁]

/-- The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (M₁ →L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom

@[simp]
protected theorem smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl

/-- `ContinuousLinearMap.applyModule` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨fun {_ _} => ContinuousLinearMap.ext⟩

instance applySMulCommClass : SMulCommClass R₁ (M₁ →L[R₁] M₁) M₁ where
  smul_comm r e m := (e.map_smul r m).symm

instance applySMulCommClass' : SMulCommClass (M₁ →L[R₁] M₁) R₁ M₁ where
  smul_comm := map_smul

instance continuousConstSMul_apply : ContinuousConstSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩

end ApplyAction

theorem isClosed_ker [T1Space M₂] (f : M₁ →SL[σ₁₂] M₂) :
    IsClosed (f.ker : Set M₁) :=
  continuous_iff_isClosed.1 (map_continuous f) _ isClosed_singleton

theorem isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] (f : M' →SL[σ₁₂] M₂) :
    IsComplete (f.ker : Set M') :=
  (isClosed_ker f).isComplete

instance completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂]
    (f : M' →SL[σ₁₂] M₂) : CompleteSpace f.ker :=
  (isComplete_ker f).completeSpace_coe

instance completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T2Space M₂]
    (f g : M' →SL[σ₁₂] M₂) : CompleteSpace (LinearMap.eqLocus f g) :=
  IsClosed.completeSpace_coe (hs := isClosed_eq (map_continuous f) (map_continuous g))

/-- Restrict codomain of a continuous linear map. -/
def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    M₁ →SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h

@[norm_cast]
theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h :=
  rfl

@[simp]
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl

@[simp]
theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = ker (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker_codRestrict p h

/-- Restrict the codomain of a continuous linear map `f` to `f.range`. -/
abbrev rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range (f : M₁ →ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)

@[simp]
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ →ₛₗ[σ₁₂] LinearMap.range (f : M₁ →ₛₗ[σ₁₂] M₂)) =
      (f : M₁ →ₛₗ[σ₁₂] M₂).rangeRestrict :=
  rfl

/-- `Submodule.subtype` as a `ContinuousLinearMap`. -/
def _root_.Submodule.subtypeL (p : Submodule R₁ M₁) : p →L[R₁] M₁ where
  cont := continuous_subtype_val
  toLinearMap := p.subtype

@[simp, norm_cast]
theorem _root_.Submodule.coe_subtypeL (p : Submodule R₁ M₁) :
    (p.subtypeL : p →ₗ[R₁] M₁) = p.subtype :=
  rfl

@[simp]
theorem _root_.Submodule.coe_subtypeL' (p : Submodule R₁ M₁) : ⇑p.subtypeL = p.subtype :=
  rfl

@[simp]
theorem _root_.Submodule.subtypeL_apply (p : Submodule R₁ M₁) (x : p) : p.subtypeL x = x :=
  rfl

theorem _root_.Submodule.range_subtypeL (p : Submodule R₁ M₁) :
    range (p.subtypeL : p →ₗ[R₁] M₁) = p :=
  Submodule.range_subtype _

theorem _root_.Submodule.ker_subtypeL (p : Submodule R₁ M₁) : ker (p.subtypeL : p →ₗ[R₁] M₁) = ⊥ :=
  Submodule.ker_subtype _

section

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

/-- The linear map `fun x => c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `ContinuousLinearMap.smulRightₗ` and `ContinuousLinearMap.smulRightL`. -/
@[simps coe]
def smulRight (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.toLinearMap.smulRight f with cont := c.2.smul continuous_const }

@[simp]
theorem smulRight_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ → M₂) x = c x • f :=
  rfl

@[simp]
lemma smulRight_zero (f : M₁ →L[R] S) : f.smulRight (0 : M₂) = 0 := by ext; simp

@[simp]
theorem zero_smulRight {x : M₂} : (0 : M₁ →L[R] S).smulRight x = 0 := by ext; simp

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

theorem smulRight_comp_smulRight {M₃ : Type*} [AddCommMonoid M₃] [Module R₁ M₃]
    [TopologicalSpace M₃] [ContinuousSMul R₁ M₃] (f : M₃ →L[R₁] R₁) (g : M₁ →L[R₁] R₁) {x : M₂}
    {y : M₃} : (smulRight f x).comp (smulRight g y) = smulRight g (f y • x) := by
  ext
  simp

@[deprecated (since := "2025-12-18")] alias smulRight_comp := smulRight_comp_smulRight

theorem range_smulRight_apply {R : Type*} [DivisionSemiring R] [Module R M₁] [Module R M₂]
    [TopologicalSpace R] [ContinuousSMul R M₂] {f : M₁ →L[R] R} (hf : f ≠ 0) (x : M₂) :
    range (f.smulRight x : M₁ →ₗ[R] M₂) = Submodule.span R {x} :=
  LinearMap.range_smulRight_apply (by simpa [coe_inj, ← coe_zero] using hf) x

section ToSpanSingleton

variable (R₁)
variable [ContinuousSMul R₁ M₁]

/-- Given an element `x` of a topological space `M` over a semiring `R`, the natural continuous
linear map from `R` to `M` by taking multiples of `x`. -/
def toSpanSingleton (x : M₁) : R₁ →L[R₁] M₁ where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x
  cont := continuous_id.smul continuous_const

@[simp]
theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl

@[simp]
theorem toSpanSingleton_zero : toSpanSingleton R₁ (0 : M₁) = 0 := by ext; simp

theorem toSpanSingleton_apply_one (x : M₁) : toSpanSingleton R₁ x 1 = x :=
  one_smul _ _

@[deprecated (since := "2025-12-05")] alias toSpanSingleton_one := toSpanSingleton_apply_one

@[simp] theorem toSpanSingleton_apply_map_one (c : R₁ →L[R₁] M₂) :
    toSpanSingleton R₁ (c 1) = c := by
  ext
  simp [← ContinuousLinearMap.map_smul_of_tower]

@[deprecated (since := "2025-12-18")] alias smulRight_one_one := toSpanSingleton_apply_map_one

theorem toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) :
    toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y :=
  coe_inj.mp <| LinearMap.toSpanSingleton_add _ _

theorem toSpanSingleton_smul {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
    [SMulCommClass R₁ α M₁] (c : α) (x : M₁) :
    toSpanSingleton R₁ (c • x) = c • toSpanSingleton R₁ x :=
  coe_inj.mp <| LinearMap.toSpanSingleton_smul _ _

theorem smulRight_id : smulRight (.id R₁ R₁) = toSpanSingleton R₁ (M₁ := M₁) := rfl

theorem smulRight_one_eq_toSpanSingleton (x : M₁) :
    (1 : R₁ →L[R₁] R₁).smulRight x = toSpanSingleton R₁ x :=
  rfl

@[deprecated (since := "2025-12-05")] alias one_smulRight_eq_toSpanSingleton :=
  smulRight_one_eq_toSpanSingleton

@[simp]
theorem toLinearMap_toSpanSingleton (x : M₁) :
    (toSpanSingleton R₁ x).toLinearMap = LinearMap.toSpanSingleton R₁ M₁ x := rfl

variable {R₁}

theorem comp_toSpanSingleton (f : M₁ →L[R₁] M₂) (x : M₁) :
    f ∘L toSpanSingleton R₁ x = toSpanSingleton R₁ (f x) :=
  coe_inj.mp <| LinearMap.comp_toSpanSingleton _ _

omit [ContinuousSMul R₁ M₁] in
theorem toSpanSingleton_comp (f : M₁ →L[R₁] R₁) (g : M₂) :
    toSpanSingleton R₁ g ∘L f = f.smulRight g := rfl

@[simp] theorem toSpanSingleton_inj {f f' : M₂} :
    toSpanSingleton R₁ f = toSpanSingleton R₁ f' ↔ f = f' := by
  simp [ContinuousLinearMap.ext_ring_iff]

@[deprecated (since := "2025-12-18")] alias smulRight_one_eq_iff := toSpanSingleton_inj

theorem toSpanSingleton_comp_toSpanSingleton [ContinuousMul R₁] {x : M₂} {c : R₁} :
    (toSpanSingleton R₁ x).comp (toSpanSingleton R₁ c) =
      toSpanSingleton R₁ (c • x) := smulRight_comp_smulRight 1 1

end ToSpanSingleton

end Semiring

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {R₃ : Type*} [Ring R₃] {M : Type*}
  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] {M₄ : Type*} [TopologicalSpace M₄]
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {σ₁₃ : R →+* R₃}

section

protected theorem map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = -f x := by
  exact map_neg f x

protected theorem map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := by
  exact map_sub f x y

@[simp]
theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end

section

variable [IsTopologicalAddGroup M₂]

instance neg : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp]
theorem neg_apply (f : M →SL[σ₁₂] M₂) (x : M) : (-f) x = -f x :=
  rfl

@[simp, norm_cast]
theorem coe_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f :=
  rfl

@[norm_cast]
theorem coe_neg' (f : M →SL[σ₁₂] M₂) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_neg (f : M →SL[σ₁₂] M₂) :
    ↑(-f) = -(f : ContinuousAddMonoidHom M M₂) := rfl

instance sub : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

instance addCommGroup : AddCommGroup (M →SL[σ₁₂] M₂) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  zsmul := (· • ·)
  zsmul_zero' f := by ext; simp
  zsmul_succ' n f := by ext; simp [add_smul, add_comm]
  zsmul_neg' n f := by ext; simp [add_smul]
  neg_add_cancel _ := by ext; apply neg_add_cancel

theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
  rfl

@[simp, norm_cast]
theorem coe_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[simp, norm_cast]
theorem coe_sub' (f g : M →SL[σ₁₂] M₂) : ⇑(f - g) = f - g :=
  rfl

@[simp, norm_cast]
theorem toContinuousAddMonoidHom_sub (f g : M →SL[σ₁₂] M₂) :
    ↑(f - g) = (f - g : ContinuousAddMonoidHom M M₂) := rfl

end

@[simp]
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    g.comp (-f) = -g.comp f := by
  ext x
  simp

@[simp]
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (-g).comp f = -g.comp f := by
  ext
  simp

@[simp]
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₂]
    [IsTopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) :
    g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := by
  ext
  simp

@[simp]
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [IsTopologicalAddGroup M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := by
  ext
  simp

instance ring [IsTopologicalAddGroup M] : Ring (M →L[R] M) where
  __ := ContinuousLinearMap.semiring
  __ := ContinuousLinearMap.addCommGroup
  intCast z := z • (1 : M →L[R] M)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

@[simp]
theorem intCast_apply [IsTopologicalAddGroup M] (z : ℤ) (m : M) : (↑z : M →L[R] M) m = z • m :=
  rfl

theorem toSpanSingleton_pow [TopologicalSpace R] [IsTopologicalRing R] (c : R) (n : ℕ) :
    toSpanSingleton R c ^ n = toSpanSingleton R (c ^ n) := by
  induction n with
  | zero => ext; simp
  | succ n ihn =>
    rw [pow_succ, ihn, mul_def, toSpanSingleton_comp_toSpanSingleton, smul_eq_mul, pow_succ']

@[deprecated (since := "2025-12-18")] alias smulRight_one_pow := toSpanSingleton_pow

section

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]


/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M →L[R] LinearMap.ker f₁` along
`LinearMap.range f₂`. -/
def projKerOfRightInverse [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →L[R] LinearMap.ker (f₁ : M →ₛₗ[σ₁₂] M₂) :=
  (.id R M - f₂.comp f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]
theorem coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (f₁.projKerOfRightInverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : f₁.ker) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp

@[simp]
theorem projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff.2 <| by simp [h y]

end

end Ring

section DivisionRing

variable {R M : Type*}

/-- A nonzero continuous linear functional is open. -/
protected theorem isOpenMap_of_ne_zero [TopologicalSpace R] [DivisionRing R] [ContinuousSub R]
    [AddCommGroup M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]
    (f : StrongDual R M) (hf : f ≠ 0) : IsOpenMap f :=
  let ⟨x, hx⟩ := exists_ne_zero hf
  IsOpenMap.of_sections fun y =>
    ⟨fun a => y + (a - f y) • (f x)⁻¹ • x, Continuous.continuousAt <| by fun_prop, by simp,
      fun a => by simp [hx]⟩

end DivisionRing

section SMulMonoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
theorem smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    (c • h).comp f = c • h.comp f :=
  rfl

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]
variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →L[R] N₃) (c : S)
    (fₗ : M →L[R] N₂) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
    h.comp (c • f) = σ₂₃ c • h.comp f := by
  ext x
  simp only [coe_smul', coe_comp', Function.comp_apply, Pi.smul_apply, map_smulₛₗ]

instance distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M →SL[σ₁₂] M₂) where
  smul_add a f g := ext fun x => smul_add a (f x) (g x)
  smul_zero a := ext fun _ => smul_zero a

end SMulMonoid

section SMul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ M₃]
  [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂)

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

instance module : Module S₃ (M →SL[σ₁₃] M₃) where
  zero_smul _ := ext fun _ => zero_smul S₃ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _

instance isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] :
    IsCentralScalar S₃ (M →SL[σ₁₃] M₃) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

variable (S) [ContinuousAdd N₃]

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coeLM : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f

variable {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
def coeLMₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f

end SMul

section toSpanSingletonLE

variable (R S M : Type*) [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
  [SMulCommClass R S M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul S M]
  [TopologicalSpace R] [ContinuousSMul R M]

/-- `ContinuousLinearMap.toSpanSingleton` as a linear equivalence. -/
@[simps -fullyApplied]
def toSpanSingletonLE : M ≃ₗ[S] (R →L[R] M) where
  toFun := toSpanSingleton R
  invFun f := f 1
  map_add' := toSpanSingleton_add R
  map_smul' := toSpanSingleton_smul R
  left_inv x := by simp
  right_inv f := by ext; simp

end toSpanSingletonLE

section SMulRightₗ

variable {R S T M M₂ : Type*} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]
  [TopologicalSpace M₂] [ContinuousSMul S M₂] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M₂] [Module T M₂] [ContinuousConstSMul T M₂] [SMulCommClass R T M₂]
  [SMulCommClass S T M₂]

/-- Given `c : E →L[R] S`, `c.smulRightₗ` is the linear map from `F` to `E →L[R] F`
sending `f` to `fun e => c e • f`. See also `ContinuousLinearMap.smulRightL`. -/
def smulRightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ where
  toFun := c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]
theorem coe_smulRightₗ (c : M →L[R] S) : ⇑(smulRightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smulRight :=
  rfl

end SMulRightₗ

section Semiring
variable {R S M : Type*} [Semiring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M]
  [ContinuousConstSMul S M] [IsTopologicalAddGroup M]

instance algebra : Algebra S (M →L[R] M) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

@[simp] theorem algebraMap_apply (r : S) (m : M) : algebraMap S (M →L[R] M) r m = r • m := rfl

end Semiring

section RestrictScalars

section Semiring
variable {A M₁ M₂ R S : Type*} [Semiring A] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommMonoid M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A]

variable (R) in
/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M₁ M₂ R A` to match assumptions of
`LinearMap.map_smul_of_tower`. -/
def restrictScalars (f : M₁ →L[A] M₂) : M₁ →L[R] M₂ :=
  ⟨(f : M₁ →ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]
theorem coe_restrictScalars (f : M₁ →L[A] M₂) :
    (f.restrictScalars R : M₁ →ₗ[R] M₂) = (f : M₁ →ₗ[A] M₂).restrictScalars R := rfl

@[simp]
theorem coe_restrictScalars' (f : M₁ →L[A] M₂) : ⇑(f.restrictScalars R) = f := rfl

@[simp]
theorem toContinuousAddMonoidHom_restrictScalars (f : M₁ →L[A] M₂) :
    ↑(f.restrictScalars R) = (f : ContinuousAddMonoidHom M₁ M₂) := rfl

@[simp] lemma restrictScalars_zero : (0 : M₁ →L[A] M₂).restrictScalars R = 0 := rfl

@[simp]
lemma restrictScalars_add [ContinuousAdd M₂] (f g : M₁ →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := rfl

variable [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂] [SMulCommClass R S M₂]

@[simp]
theorem restrictScalars_smul (c : S) (f : M₁ →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

variable [ContinuousAdd M₂]

variable (A R S M₁ M₂) in
/-- `ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`. -/
def restrictScalarsₗ : (M₁ →L[A] M₂) →ₗ[S] M₁ →L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R := rfl

end Semiring

section Ring
variable {A R S M₁ M₂ : Type*} [Ring A] [Ring R] [Ring S]
  [AddCommGroup M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A] [IsTopologicalAddGroup M₂]

@[simp]
lemma restrictScalars_sub (f g : M₁ →L[A] M₂) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := rfl

@[simp]
lemma restrictScalars_neg (f : M₁ →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R := rfl

end Ring
end RestrictScalars

end ContinuousLinearMap

namespace Submodule

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

variable {p : Submodule R M}

namespace ClosedComplemented

variable [T1Space p]

theorem exists_isClosed_isCompl (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h fun f hf => ⟨ker f, isClosed_ker f, LinearMap.isCompl_of_proj hf⟩

/-- An arbitrary choice of closed complement of a closed complemented submodule. -/
noncomputable def complement (h : ClosedComplemented p) : Submodule R M :=
  Classical.choose h.exists_isClosed_isCompl

theorem isClosed_complement (h : ClosedComplemented p) : IsClosed (h.complement : Set M) :=
  Classical.choose_spec (h.exists_isClosed_isCompl) |>.1

theorem isCompl_complement (h : ClosedComplemented p) : IsCompl p h.complement :=
  Classical.choose_spec (h.exists_isClosed_isCompl) |>.2

protected theorem isClosed [IsTopologicalAddGroup M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) := by
  rcases h with ⟨f, hf⟩
  have : (ContinuousLinearMap.id R M - p.subtypeL.comp f).ker = p :=
    LinearMap.ker_id_sub_eq_of_proj hf
  exact this ▸ isClosed_ker _

end ClosedComplemented

@[simp]
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  ⟨0, fun x => by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp]
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  ⟨(ContinuousLinearMap.id R M).codRestrict ⊤ fun _x => trivial,
    fun x => Subtype.ext_iff.2 <| by simp⟩

end Submodule

theorem ContinuousLinearMap.closedComplemented_ker_of_rightInverse {R : Type*} [Ring R]
    {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommGroup M₂] [Module R M] [Module R M₂] [IsTopologicalAddGroup M] (f₁ : M →L[R] M₂)
    (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) : f₁.ker.ClosedComplemented :=
  ⟨f₁.projKerOfRightInverse f₂ h, f₁.projKerOfRightInverse_apply_idem f₂ h⟩

namespace ContinuousLinearMap

@[grind =]
theorem isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {f : M →L[R] M} :
    IsIdempotentElem f.toLinearMap ↔ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← coe_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

/-- Idempotent operators are equal iff their range and kernels are. -/
lemma IsIdempotentElem.ext_iff {p q : M →L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ p.range = q.range ∧ p.ker = q.ker := by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, IsIdempotentElem.ext⟩ := IsIdempotentElem.ext_iff

/-- `range f` is invariant under `T` if and only if `f ∘L T ∘L f = T ∘L f`,
for idempotent `f`. -/
lemma IsIdempotentElem.range_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.range ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f := by
  simpa [← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨IsIdempotentElem.conj_eq_of_range_mem_invtSubmodule,
  IsIdempotentElem.range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

/-- `ker f` is invariant under `T` if and only if `f ∘L T ∘L f = f ∘L T`,
for idempotent `f`. -/
lemma IsIdempotentElem.ker_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.ker ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T := by
  simpa [← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨IsIdempotentElem.conj_eq_of_ker_mem_invtSubmodule,
  IsIdempotentElem.ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
lemma IsIdempotentElem.commute_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    Commute f T ↔ (f.range ∈ Module.End.invtSubmodule T ∧ f.ker ∈ Module.End.invtSubmodule T) := by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← coe_comp] using
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

variable [IsTopologicalAddGroup M]

/-- An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
theorem IsIdempotentElem.commute_iff_of_isUnit {f T : M →L[R] M} (hT : IsUnit T)
    (hf : IsIdempotentElem f) :
    Commute f T ↔ f.range.map (T : M →ₗ[R] M) = f.range ∧ f.ker.map (T : M →ₗ[R] M) = f.ker := by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M →L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← ContinuousLinearMap.coe_comp] using
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap

@[deprecated (since := "2025-12-27")] alias IsIdempotentElem.range_eq_ker :=
  LinearMap.IsIdempotentElem.range_eq_ker
@[deprecated (since := "2025-12-27")] alias IsIdempotentElem.ker_eq_range :=
  LinearMap.IsIdempotentElem.ker_eq_range

theorem IsIdempotentElem.isClosed_range [T1Space M] {p : M →L[R] M}
    (hp : IsIdempotentElem p) : IsClosed (p.range : Set M) :=
  LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

end ContinuousLinearMap

section topDualPairing

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜]

variable (𝕜 E) in
/-- The canonical pairing of a vector space and its topological dual. -/
def topDualPairing : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜

@[simp]
theorem topDualPairing_apply (v : E →L[𝕜] 𝕜)
    (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl

end topDualPairing
```

</details>

<details>
<summary>022-scalar-grep_Basic.lean</summary>

SHA-256: `f4f33f1236afe8fef845242ee85773d8821a6aa724839908f790b47bd90d760c`.

```lean
/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Monotonicity.Attr

import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Util.CompileInductive

/-!
# Lemmas on the monotone multiplication typeclasses

This file builds on `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` by proving several
lemmas that do not immediately follow from the typeclass specifications.
-/

public section

open Function

variable {α M₀ G₀ : Type*}

section MulZeroClass

variable [MulZeroClass α] {a b c d : α}

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/-- Assumes left strict covariance. -/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/-- Assumes right strict covariance. -/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

end Preorder

section PartialOrder

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb

theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α] {a b c d : α}

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`, assuming left covariance. -/

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right covariance. -/

@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/

theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : ℕ}

@[simp] lemma pow_succ_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ (n + 1)
  | 0 => (pow_one a).symm ▸ ha
  | _ + 1 => pow_succ a _ ▸ mul_nonneg (pow_succ_nonneg ha _) ha

@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha

lemma zero_pow_le_one [ZeroLEOneClass M₀] : ∀ n : ℕ, (0 : M₀) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one

lemma pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (fun n : ℕ ↦ a ^ n) :=
  antitone_nat_of_succ_le fun n ↦ by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n), pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

lemma pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : a ^ n ≤ a ^ m := pow_right_anti₀ ha₀ ha₁ hmn

lemma pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

lemma sq_le [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

lemma pow_le_one₀ [PosMulMono M₀] {n : ℕ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ^ n ≤ 1 :=
  pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : M₀) ≤ a * b := ha.trans <| le_mul_of_one_le_right (zero_le_one.trans ha) hb

lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]
protected lemma Bound.one_lt_mul [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] :
    1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
lemma mul_le_one₀ [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb₀).trans <| by rwa [one_mul]

lemma pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)

lemma pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

lemma one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n :=
  pow_zero a ▸ pow_right_mono₀ ha n.zero_le

lemma one_lt_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
lemma Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
lemma pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hmn : m ≤ n) :
    a ^ m ≤ a ^ n :=
  pow_right_mono₀ ha hmn

lemma le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
lemma Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : 0 < n) :
    a ≤ a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)

lemma pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} :=
  fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

variable [Preorder α] {f g : α → M₀}

lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha

lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf

lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp hf

lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf

lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder

section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha

lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

section strict_mono
variable [PosMulStrictMono M₀]

@[simp] lemma pow_succ_pos (ha : 0 < a) : ∀ n, 0 < a ^ (n + 1)
  | 0 => by simpa using ha
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_succ_pos ha _) ha

@[simp] lemma pow_pos [ZeroLEOneClass M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

@[gcongr, bound]
lemma pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)

/-- See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`. -/
lemma pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n ≠ 0) :
    StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn

lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt

lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (pow_right_strictMono₀ h).le_iff_le

lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

end ZeroLEOneClass

lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

lemma pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m ≤ a ^ n ↔ n ≤ m :=
  (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α → M₀}

lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf

lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp hf

lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf

lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf

lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

lemma pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff

lemma pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine ⟨fun h ↦ ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

lemma one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

lemma pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

lemma one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

lemma sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma sq_lt_one_iff₀ (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_le_sq_iff₀ (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

end ZeroLEOneClass

variable [MulPosMono M₀]

lemma lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

lemma le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

lemma sq_eq_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := by
  simp [ha, hb]

lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

lemma sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero

lemma sq_le_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section CancelMonoidWithZero

variable [MonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α :=
  ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α :=
  ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

theorem PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT α] :
    PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

end PartialOrder

end CancelMonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] {a b c : G₀}

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma mul_inv_left_le (hb : 0 ≤ b) : a * (a⁻¹ * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma le_mul_inv_left (hb : b ≤ 0) : b ≤ a * (a⁻¹ * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma inv_mul_left_le (hb : 0 ≤ b) : a⁻¹ * (a * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma le_inv_mul_left (hb : b ≤ 0) : b ≤ a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma mul_inv_right_le (ha : 0 ≤ a) : a * b * b⁻¹ ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma le_mul_inv_right (ha : a ≤ 0) : a ≤ a * b * b⁻¹ := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma inv_mul_right_le (ha : 0 ≤ a) : a * b⁻¹ * b ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma le_inv_mul_right (ha : a ≤ 0) : a ≤ a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma mul_div_mul_right_le (h : 0 ≤ a / b) : a * c / (b * c) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma le_mul_div_mul_right (h : a / b ≤ 0) : a / b ≤ a * c / (b * c) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

end Preorder

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

/-- See `div_self` for the version with equality when `a ≠ 0`. -/
lemma div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel`. -/
lemma mul_inv_le_one : a * a⁻¹ ≤ 1 := by simpa only [div_eq_mul_inv] using div_self_le_one a

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel`. -/
lemma inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀]

section PosMulReflectLT

variable [PosMulReflectLT G₀] {a b c : G₀}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀` implies `PosMulStrictMono G₀`. -/
theorem PosMulReflectLT.toPosMulStrictMono : PosMulStrictMono G₀ where
  mul_lt_mul_of_pos_left a ha b c hbc :=
    lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀`
allows us to upgrade `MulPosMono G₀` to `MulPosReflectLE G₀`.
The other implication holds without the `PosMulReflectLT G₀` assumption,
see `MulPosReflectLT.toMulPosStrictMono` for a stronger version below.

This theorem shows that in the presence of the assumption `PosMulReflectLT G₀`,
it makes no sense to optimize between assumptions `MulPosMono G₀`, `MulPosStrictMono G₀`,
`MulPosReflectLT G₀`, and `MulPosReflectLE G₀`. -/
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

/-- See `le_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_le_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]

/-- See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← inv_mul_le_iff₀ ha, mul_one]

lemma one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

/-- One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/-- One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

/-- See `lt_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_lt_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

section ZeroLEOneClass

variable [ZeroLEOneClass G₀]

@[bound]
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]
lemma inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
  (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

lemma one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]
lemma inv_mul_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 :=
  inv_mul_le_of_le_mul₀ hb zero_le_one <| by rwa [mul_one]

section ZPow
variable {m n : ℤ}

lemma zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

lemma zpow_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _

lemma zpow_right_mono₀ (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
lemma zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn

lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a ^ n ≤ a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn

lemma one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn

lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

lemma zpow_le_one_of_nonpos₀ (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 := by
  simpa using zpow_right_mono₀ ha hn

lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : n ≤ 0) : 1 ≤ a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn

lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn

lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn

lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn

lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono₀ ha).le_iff_le

@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt

lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m ≤ a ^ n ↔ n ≤ m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt

@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 ≤ a ^ n ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 ≤ a ^ n ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end ZPow

end ZeroLEOneClass

section MulPosMono

variable [MulPosMono G₀] {n : ℤ}

lemma zpow_left_monoOn₀ (hn : 0 ≤ n) : MonotoneOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn; simpa using pow_left_monotoneOn

lemma zpow_left_strictMonoOn₀ (hn : 0 < n) : StrictMonoOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)

lemma zpow_le_zpow_left₀ (hn : 0 ≤ n) (ha : 0 ≤ a) (h : a ≤ b) : a ^ n ≤ b ^ n :=
  zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h

lemma zpow_lt_zpow_left₀ (hn : 0 < n) (ha : 0 ≤ a) (h : a < b) : a ^ n < b ^ n :=
  zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h

end MulPosMono

end PosMulReflectLT

section MulPosReflectLT
variable [MulPosReflectLT G₀] {a b c : G₀}

namespace Right

lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

variable (G₀) in
/-- For a group with zero, `MulPosReflectLT G₀` implies `MulPosStrictMono G₀`. -/
theorem _root_.MulPosReflectLT.toMulPosStrictMono : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc :=
    lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le

lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

end Right

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

/-- See `le_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_le_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `lt_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_lt_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `le_div_iff₀'` for a version with multiplication on the other side. -/
lemma le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

/-- See `div_le_iff₀'` for a version with multiplication on the other side. -/
lemma div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- See `lt_div_iff₀'` for a version with multiplication on the other side. -/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

/-- See `div_lt_iff₀'` for a version with multiplication on the other side. -/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]

lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']

lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [div_lt_iff₀ hc, div_mul_cancel₀ _ hc.ne']

/-- See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

/-- See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha, one_mul]

lemma one_le_div₀ (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]
lemma one_lt_div₀ (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]
lemma div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]
lemma div_lt_one₀ (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

/-- One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/-- One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/-- One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative). -/
lemma mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/-- One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative). -/
lemma div_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
lemma mul_inv_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[bound]
lemma div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[mono, gcongr, bound]
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

end MulPosReflectLT

section Both

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/-- See `inv_anti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [inv_le_iff_one_le_mul₀' ha, le_mul_inv_iff₀ hb, one_mul]

/-- See `inv_strictAnti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha, lt_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba

lemma strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  fun ⦃_⦄ ha ⦃_⦄ _ h ↦ inv_strictAnti₀ (Set.mem_setOf.mp ha) h

lemma antitoneOn_inv_pos : AntitoneOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  strictAntiOn_inv_pos.antitoneOn

/-- See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumption. -/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha), inv_inv]

/-- See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumption. -/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/-- See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumption. -/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha, inv_inv]

/-- See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumption. -/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]

lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
  lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c :=
  (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]
lemma div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]
lemma div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)

lemma div_lt_div₀' (hac : a ≤ c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end Both

end PartialOrder

section LinearOrder
variable [LinearOrder G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_gt h

lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 ≤ b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha ↦ (div_nonneg ha hb).not_gt h

end PosMulMono

variable {m n : ℤ}

section ZeroLEOne

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

lemma inv_le_one_iff₀ : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff

lemma zpow_eq_one_iff_right₀ (ha₀ : 0 ≤ a) (ha₁ : a ≠ 1) {n : ℤ} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

end ZeroLEOne

section MulPosMono

variable [PosMulReflectLT G₀] [MulPosMono G₀]

lemma zpow_le_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb

lemma zpow_lt_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] [MulPosMono G₀]

lemma zpow_left_injOn₀ : ∀ {n : ℤ}, n ≠ 0 → {a | 0 ≤ a}.InjOn fun a : G₀ ↦ a ^ n
  | (n + 1 : ℕ), _ => by simpa using mod_cast (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
  | .negSucc n, _ => by
    simpa using inv_injective.comp_injOn (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn

lemma zpow_left_inj₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b := (zpow_left_injOn₀ hn).eq_iff ha hb

end PosMulStrictMono
end GroupWithZero.LinearOrder

section CommGroupWithZero

section Preorder
variable [CommGroupWithZero G₀] [Preorder G₀] {a b c : G₀}

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma mul_div_mul_left_le (h : 0 ≤ a / b) : c * a / (c * b) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma le_mul_div_mul_left (h : a / b ≤ 0) : a / b ≤ c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

end Preorder

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulMono.toMulPosMono
  PosMulStrictMono.toMulPosStrictMono PosMulReflectLT.toMulPosReflectLT

/-- See `le_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ a * c ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_le_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ a * c := by
  rw [inv_mul_le_iff₀ hc, mul_comm]

/-- See `le_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a ≤ b * c⁻¹ ↔ c * a ≤ b := by
  rw [le_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_le_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  rw [mul_inv_le_iff₀ hc, mul_comm]

lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [div_le_iff₀ hb, ← mul_div_right_comm, le_div_iff₀ hd]

/-- See `le_div_iff₀` for a version with multiplication on the other side. -/
lemma le_div_iff₀' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  rw [le_div_iff₀ hc, mul_comm]

/-- See `div_le_iff₀` for a version with multiplication on the other side. -/
lemma div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  rw [div_le_iff₀ hc, mul_comm]

lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  rw [le_div_iff₀ ha, le_div_iff₀' hc]

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  rw [div_le_iff₀ hb, div_le_iff₀' hc]

/-- See `lt_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_lt_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- See `lt_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  rw [lt_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_lt_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  rw [mul_inv_lt_iff₀ hc, mul_comm]

lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [div_lt_iff₀ hb, ← mul_div_right_comm, lt_div_iff₀ hd]

/-- See `lt_div_iff₀` for a version with multiplication on the other side. -/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [lt_div_iff₀ hc, mul_comm]

/-- See `div_lt_iff₀` for a version with multiplication on the other side. -/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  rw [div_lt_iff₀ hc, mul_comm]

lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  rw [lt_div_iff₀ ha, lt_div_iff₀' hc]

lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

end CommGroupWithZero
```

</details>

<details>
<summary>022-scalar-grep_Defs.lean</summary>

SHA-256: `7c106171cb7a79773caa632ff4dd575c6e097c3d840bf0c0af57d3955f88ea66`.

```lean
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Batteries.Logic
public import Batteries.Util.LibraryNote
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.OfNat
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Simps.Basic

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(Add)?(Comm)?(Semigroup|Monoid|Group)`, where `Add` means that
the class uses additive notation and `Comm` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `Mathlib/Algebra/Group/Basic.lean`.

We register the following instances:

- `Pow M ℕ`, for monoids `M`, and `Pow G ℤ` for groups `G`;
- `SMul ℕ M` for additive monoids `M`, and `SMul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `Add.add`, `Neg.neg`/`Sub.sub`, `Mul.mul`, `Div.div`, and `HPow.hPow`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

universe u v w

open Function

variable {G : Type*}

section Mul

variable [Mul G]

/-- A mixin for left cancellative multiplication. -/
@[mk_iff] class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative (i.e. left regular). -/
  protected mul_left_cancel (a : G) : IsLeftRegular a
/-- A mixin for right cancellative multiplication. -/
@[mk_iff] class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative (i.e. right regular). -/
  protected mul_right_cancel (a : G) : IsRightRegular a
/-- A mixin for cancellative multiplication. -/
@[mk_iff]
class IsCancelMul (G : Type u) [Mul G] : Prop extends IsLeftCancelMul G, IsRightCancelMul G

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

attribute [to_additive] IsLeftCancelMul
attribute [to_additive] isLeftCancelMul_iff

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

attribute [to_additive] IsRightCancelMul
attribute [to_additive] isRightCancelMul_iff

/-- A mixin for cancellative addition. -/
@[mk_iff]
class IsCancelAdd (G : Type u) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

attribute [to_additive] IsCancelMul
attribute [to_additive existing] isCancelMul_iff

section Regular

variable {R : Type*}

@[to_additive] theorem isCancelMul_iff_forall_isRegular [Mul R] :
    IsCancelMul R ↔ ∀ r : R, IsRegular r := by
  rw [isCancelMul_iff, isLeftCancelMul_iff, isRightCancelMul_iff, ← forall_and]
  exact forall_congr' fun _ ↦ isRegular_iff.symm

/-- If all multiplications cancel on the left then every element is left-regular. -/
@[to_additive /-- If all additions cancel on the left then every element is add-left-regular. -/]
theorem IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R) : IsLeftRegular g :=
  (isLeftCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel on the right then every element is right-regular. -/
@[to_additive /-- If all additions cancel on the right then every element is add-right-regular. -/]
theorem IsRightRegular.all [Mul R] [IsRightCancelMul R] (g : R) : IsRightRegular g :=
  (isRightCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel then every element is regular. -/
@[to_additive /-- If all additions cancel then every element is add-regular. -/]
theorem IsRegular.all [Mul R] [IsCancelMul R] (g : R) : IsRegular g := ⟨.all g, .all g⟩

end Regular

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  (IsLeftCancelMul.mul_left_cancel a ·)

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ ↦ mul_left_cancel

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  (IsRightCancelMul.mul_right_cancel b ·)

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel

@[to_additive (attr := simp)]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end IsRightCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

section IsCommutative

/-- A Prop stating that the addition is commutative. -/
class IsAddCommutative (M : Type*) [Add M] : Prop where
  is_comm : Std.Commutative (α := M) (· + ·)

/-- A Prop stating that the multiplication is commutative. -/
@[to_additive existing]
class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)

attribute [instance] IsAddCommutative.is_comm
attribute [instance] IsMulCommutative.is_comm

@[to_additive]
lemma isMulCommutative_iff {M : Type*} [Mul M] : IsMulCommutative M ↔ ∀ a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨_, IsMulCommutative.of_comm⟩ := isMulCommutative_iff

/-- An alternative to `mul_comm` which uses the mixin `IsMulCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `mul_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/
@[to_additive
/-- An alternative to `add_comm` which uses the mixin `IsAddCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `add_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/ ]
lemma mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a :=
  IsMulCommutative.is_comm.comm ..

end IsCommutative

/-- A commutative additive magma is a type with an addition which commutes. -/
@[ext]
class AddCommMagma (G : Type u) extends Add G where
  /-- Addition is commutative in a commutative additive magma. -/
  protected add_comm : ∀ a b : G, a + b = b + a

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
class CommMagma (G : Type u) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

attribute [to_additive] CommMagma

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

attribute [to_additive] CommSemigroup

section CommMagma

variable [CommMagma G] {a : G}

@[to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm

@[to_additive]
instance CommMagma.to_isCommutative : IsMulCommutative G := ⟨⟨mul_comm⟩⟩

@[to_additive (attr := simp)]
lemma isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[to_additive (attr := simp)]
lemma isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
  ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
  ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`. -/]
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G, IsLeftCancelMul G

library_note «lower cancel priority» /--
We lower the priority of inheriting from cancellative structures.
This attempts to avoid expensive checks involving bundling and unbundling with the `IsDomain` class.
since `IsDomain` already depends on `Semiring`, we can synthesize that one first.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60simpNF.60.20complaining.20here.3F
-/
attribute [instance 75] LeftCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G, IsLeftCancelAdd G

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
add_decl_doc LeftCancelSemigroup.toIsLeftCancelMul

/-- Any `AddLeftCancelSemigroup` satisfies `IsLeftCancelAdd`. -/
add_decl_doc AddLeftCancelSemigroup.toIsLeftCancelAdd

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G, IsRightCancelMul G

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G, IsRightCancelAdd G

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
add_decl_doc RightCancelSemigroup.toIsRightCancelMul

/-- Any `AddRightCancelSemigroup` satisfies `IsRightCancelAdd`. -/
add_decl_doc AddRightCancelSemigroup.toIsRightCancelAdd

/-- Bundling an `Add` and `Zero` structure together without any axioms about their
compatibility. See `AddZeroClass` for the additional assumption that 0 is an identity. -/
class AddZero (M : Type*) extends Zero M, Add M

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
@[to_additive (attr := ext)]
class MulOne (M : Type*) extends One M, Mul M

/-- An additive monoid is Dedekind-finite if every left inverse is also a right inverse.
Also called von Neumann-finite or directly finite. -/
class IsDedekindFiniteAddMonoid (M : Type*) [AddZero M] : Prop where
  add_eq_zero_symm {a b : M} : a + b = 0 → b + a = 0

/-- A monoid is Dedekind-finite if every left inverse is also a right inverse.
It is more common to talk about Dedekind-finite rings, but https://arxiv.org/abs/2102.01598
does define Dedekind-finite monoids in §2.2. -/
@[to_additive (attr := mk_iff)] class IsDedekindFiniteMonoid (M : Type*) [MulOne M] : Prop where
  mul_eq_one_symm {a b : M} : a * b = 1 → b * a = 1

export IsDedekindFiniteMonoid (mul_eq_one_symm)
export IsDedekindFiniteAddMonoid (add_eq_zero_symm)
attribute [to_additive existing] isDedekindFiniteMonoid_iff

@[to_additive] theorem mul_eq_one_comm {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ↔ b * a = 1 where
  mp := mul_eq_one_symm
  mpr := mul_eq_one_symm

@[to_additive] instance (priority := low) (M) [MulOne M] [IsMulCommutative M] :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm := mul_comm' .. |>.trans

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (M : Type u) extends AddZero M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[to_additive]
class MulOneClass (M : Type u) extends MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

@[to_additive (attr := ext)]
theorem MulOneClass.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
theorem one_mul : ∀ a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
theorem mul_one : ∀ a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section

variable {M : Type u}

attribute [to_additive existing] npowRec

variable [One M] [Semigroup M] (m n : ℕ) (hn : n ≠ 0) (a : M) (ha : 1 * a = a)
include hn ha

@[to_additive] theorem npowRec_add : npowRec (m + n) a = npowRec m a * npowRec n a := by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]

@[to_additive] theorem npowRec_succ : npowRec (n + 1) a = a * npowRec n a := by
  rw [Nat.add_comm, npowRec_add 1 n hn a ha, npowRec, npowRec, ha]

end

library_note «forgetful inheritance» /--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = MetricSpace` and `P = TopologicalSpace`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `MetricSpace` / `TopologicalSpace`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `TopologicalSpace`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `MetricSpace` and
`TopologicalSpace` called `UniformSpace`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`UniformSpace.ofCore` or `RealInnerProduct.ofCore`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/-!
### Design note on `AddMonoid` and `Monoid`

An `AddMonoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`Polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `Polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `AddMonoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `SMul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `Polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `AddMonoid`). In this way, the two natural `SMul ℕ (Polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `Monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.
-/

/-- Exponentiation by repeated squaring. -/
@[to_additive /-- Scalar multiplication by repeated self-addition,
the additive version of exponentiation by repeated squaring. -/]
def npowBinRec {M : Type*} [One M] [Mul M] (k : ℕ) : M → M :=
  npowBinRec.go k 1
where
  /-- Auxiliary tail-recursive implementation for `npowBinRec`. -/
  @[to_additive nsmulBinRec.go /-- Auxiliary tail-recursive implementation for `nsmulBinRec`. -/]
  go (k : ℕ) : M → M → M :=
    k.binaryRec (fun y _ ↦ y) fun bn _n fn y x ↦ fn (cond bn (y * x) y) (x * x)

/--
A variant of `npowRec` which is a semigroup homomorphism from `ℕ₊` to `M`.
-/
def npowRec' {M : Type*} [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | 1, m => m
  | k + 2, m => npowRec' (k + 1) m * m

/--
A variant of `nsmulRec` which is a semigroup homomorphism from `ℕ₊` to `M`.
-/
def nsmulRec' {M : Type*} [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | 1, m => m
  | k + 2, m => nsmulRec' (k + 1) m + m

attribute [to_additive existing] npowRec'

@[to_additive]
theorem npowRec'_succ {M : Type*} [Mul M] [One M] {k : ℕ} (_ : k ≠ 0) (m : M) :
    npowRec' (k + 1) m = npowRec' k m * m :=
  match k with
  | _ + 1 => rfl

@[to_additive]
theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ← ih]

@[to_additive]
theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : ℕ} (k0 : k ≠ 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

@[to_additive]
theorem npowRec_eq {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) :
    npowRec (k + 1) m = 1 * npowRec' (k + 1) m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec, npowRec'_succ k.succ_ne_zero, ← mul_assoc]
      congr
      simp [ih]

@[to_additive]
theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : ℕ) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' ≠ 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by lia), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by lia), mul_assoc]

/--
An abbreviation for `npowRec` with an additional typeclass assumption on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated squaring
in compiled code.
-/
@[to_additive
/-- An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled
code as an automatic parameter. -/]
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowRec k m

/--
An abbreviation for `npowBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation.
-/
@[to_additive
/-- An abbreviation for `nsmulBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation
as an automatic parameter. -/]
abbrev npowBinRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowBinRec k m

@[to_additive (attr := csimp)]
theorem npowRec_eq_npowBinRec : @npowRecAuto = @npowBinRecAuto := by
  funext M _ _ k m
  rw [npowBinRecAuto, npowRecAuto, npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

@[to_additive] theorem npowBinRec_zero {M : Type*} [Mul M] [One M] (m : M) :
    npowBinRec 0 m = 1 := rfl

@[to_additive] theorem npowBinRec_succ {M : Type*} [Semigroup M] [One M] (n : ℕ) (m : M) :
    npowBinRec (n + 1) m = npowBinRec n m * m := by
  iterate 2 rw [← npowBinRecAuto, ← npowRec_eq_npowBinRec]
  rfl

/-- An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZero.toAdd

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl

@[default_instance high, to_additive]
instance Monoid.toPow {M : Type*} [Monoid M] : Pow M ℕ :=
  ⟨fun x n ↦ Monoid.npow n x⟩

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

@[to_additive (attr := simp) nsmul_eq_smul]
theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n :=
  rfl

@[to_additive] lemma left_inv_eq_right_inv (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

-- This lemma is higher priority than later `zero_smul` so that the `simpNF` is happy
@[to_additive (attr := simp high) zero_nsmul]
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _

@[to_additive succ_nsmul]
theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  Monoid.npow_succ n a

@[to_additive one_nsmul, simp]
lemma pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

@[to_additive succ_nsmul'] lemma pow_succ' (a : M) : ∀ n, a ^ (n + 1) = a * a ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ _ n, pow_succ, pow_succ', mul_assoc]

@[to_additive] lemma mul_pow_mul (a b : M) (n : ℕ) :
    (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ← ih, mul_assoc]

@[to_additive]
lemma pow_mul_comm' (a : M) (n : ℕ) : a ^ n * a = a * a ^ n := by rw [← pow_succ, pow_succ']

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]

-- TODO: Should `alias` automatically transfer `to_additive` statements?
@[to_additive existing two_nsmul] alias sq := pow_two

@[to_additive three'_nsmul]
lemma pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]

@[to_additive three_nsmul]
lemma pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ', pow_two]

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy
@[to_additive (attr := simp high) nsmul_zero] lemma one_pow : ∀ n, (1 : M) ^ n = 1
  | 0 => pow_zero _
  | n + 1 => by rw [pow_succ, one_pow, one_mul]

@[to_additive add_nsmul]
lemma pow_add (a : M) (m : ℕ) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, pow_zero, mul_one]
  | n + 1 => by rw [pow_succ, ← mul_assoc, ← pow_add, ← pow_succ, Nat.add_assoc]

@[to_additive] lemma pow_mul_comm (a : M) (m n : ℕ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, Nat.add_comm]

@[to_additive mul_nsmul] lemma pow_mul (a : M) (m : ℕ) : ∀ n, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero, pow_zero, pow_zero]
  | n + 1 => by rw [Nat.mul_succ, pow_add, pow_succ, pow_mul]

@[to_additive mul_nsmul']
lemma pow_mul' (a : M) (m n : ℕ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]

@[to_additive nsmul_left_comm]
lemma pow_right_comm (a : M) (m n : ℕ) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]

@[to_additive] protected lemma IsLeftRegular.mul_eq_one_symm {a b : M} (reg : IsLeftRegular a)
    (eq : a * b = 1) : b * a = 1 :=
  reg <| by simp [← mul_assoc, eq]

@[to_additive] protected lemma IsRightRegular.mul_eq_one_symm {a b : M} (reg : IsRightRegular a)
    (eq : b * a = 1) : a * b = 1 :=
  reg <| by simp [mul_assoc, eq]

variable (M)

@[to_additive] instance [IsLeftCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsLeftCancelMul.mul_left_cancel _).mul_eq_one_symm

@[to_additive] instance [IsRightCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsRightCancelMul.mul_right_cancel _).mul_eq_one_symm

namespace IsDedekindFiniteMonoid

/-- A monoid is Dedekind-finite if every element with a left inverse also has a right inverse. -/
@[to_additive] lemma of_exists_self_mul_eq_one (ex : ∀ x y : M, x * y = 1 → ∃ z, y * z = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show x = z by simpa [← mul_assoc, h] using congr_arg (x * ·) hz.symm]

/-- A monoid is Dedekind-finite if every element with a right inverse also has a left inverse. -/
@[to_additive] lemma of_exists_mul_self_eq_one (ex : ∀ x y : M, x * y = 1 → ∃ z, z * x = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show y = z by simpa [mul_assoc, h] using congr_arg (· * y) hz.symm]

end IsDedekindFiniteMonoid

end Monoid

/-- An additive monoid is torsion-free if scalar multiplication by every non-zero element `n : ℕ` is
injective. -/
@[mk_iff]
class IsAddTorsionFree (M : Type*) [AddMonoid M] where
  protected nsmul_right_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ n • a

/-- A monoid is torsion-free if power by every non-zero element `n : ℕ` is injective. -/
@[to_additive, mk_iff]
class IsMulTorsionFree (M : Type*) [Monoid M] where
  protected pow_left_injective ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun a : M ↦ a ^ n

attribute [to_additive existing] isMulTorsionFree_iff

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

/- This is assigned default rather than low priority because it gives the most common examples
of Dedekind-finite monoids and is used the most often. Benchmark results indicate default
priority performs better than low or high priority. -/
@[to_additive] instance (M) [CommMonoid M] : IsDedekindFiniteMonoid M := inferInstance

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddLeftCancelSemigroup` is not enough. -/
class AddLeftCancelMonoid (M : Type u) extends AddMonoid M, AddLeftCancelSemigroup M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
class LeftCancelMonoid (M : Type u) extends Monoid M, LeftCancelSemigroup M

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelSemigroup` is not enough. -/
class AddRightCancelMonoid (M : Type u) extends AddMonoid M, AddRightCancelSemigroup M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
class RightCancelMonoid (M : Type u) extends Monoid M, RightCancelSemigroup M

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `AddRightCancelMonoid` is not enough. -/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

/-- Commutative version of `AddCancelMonoid`. -/
class AddCancelCommMonoid (M : Type u) extends AddCommMonoid M, AddLeftCancelMonoid M

attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid -- See note [lower cancel priority]

/-- Commutative version of `CancelMonoid`. -/
@[to_additive]
class CancelCommMonoid (M : Type u) extends CommMonoid M, LeftCancelMonoid M

attribute [instance 75] CancelCommMonoid.toCommMonoid -- See note [lower cancel priority]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }

/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive /-- Any `AddCancelMonoid G` satisfies `IsCancelAdd G`. -/]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M where

end CancelMonoid

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`, which has better definitional behavior. -/
def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : ℤ → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zpowRec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : ℕ → G → G := nsmulRec) : ℤ → G → G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a

attribute [to_additive existing] zpowRec

section InvolutiveInv

/-- Auxiliary typeclass for types with an involutive `Neg`. -/
class InvolutiveNeg (A : Type*) extends Neg A where
  protected neg_neg : ∀ x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
class InvolutiveInv (G : Type*) extends Inv G where
  protected inv_inv : ∀ x : G, x⁻¹⁻¹ = x

variable [InvolutiveInv G]

@[to_additive (attr := simp)]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _

end InvolutiveInv

/-!
### Design note on `DivInvMonoid`/`SubNegMonoid` and `DivisionMonoid`/`SubtractionMonoid`

Those two pairs of made-up classes fulfill slightly different roles.

`DivInvMonoid`/`SubNegMonoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`Group`,
`GroupWithZero`, `DivisionRing`, `Field`) and for a few structures with a rather weak
pseudo-inverse (`Matrix`).

`DivisionMonoid`/`SubtractionMonoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `Set α`, `Finset α`, `Filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `DivisionMonoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `DivisionMonoid.inv_inv`, you can consider `WithTop Unit` with `a⁻¹ = ⊤` for all `a`.
* Without `DivisionMonoid.mul_inv_rev`, you can consider `WithTop α` with `a⁻¹ = a` for all `a`
  where `α` noncommutative.
* Without `DivisionMonoid.inv_eq_of_mul`, you can consider any `CommMonoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ENNReal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/-- In a class equipped with instances of both `Monoid` and `Inv`, this definition records what the
default definition for `Div` would be: `a * b⁻¹`.  This is later provided as the default value for
the `Div` instance in `DivInvMonoid`.

We keep it as a separate definition rather than inlining it in `DivInvMonoid` so that the `Div`
field of individual `DivInvMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : ℤ → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl

/-- In a class equipped with instances of both `AddMonoid` and `Neg`, this definition records what
the default definition for `Sub` would be: `a + -b`.  This is later provided as the default value
for the `Sub` instance in `SubNegMonoid`.

We keep it as a separate definition rather than inlining it in `SubNegMonoid` so that the `Sub`
field of individual `SubNegMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/-- A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, Sub (Foo X)` instance but no
`∀ X, Neg (Foo X)`. Suppose we also have an instance
`∀ X [Cromulent X], AddGroup (Foo X)`. Then the `(-)` coming from
`AddGroup.sub` cannot be definitionally equal to the `(-)` coming from
`Foo.Sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `AddMonoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  protected zsmul : ℤ → G → G
  protected zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  protected zsmul_succ' (n : ℕ) (a : G) :
      zsmul n.succ a = zsmul n a + a := by
    intros; rfl
  protected zsmul_neg' (n : ℕ) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

instance DivInvMonoid.toZPow {M} [DivInvMonoid M] : Pow M ℤ :=
  ⟨fun x n ↦ DivInvMonoid.zpow n x⟩

instance SubNegMonoid.toZSMul {M} [SubNegMonoid M] : SMul ℤ M :=
  ⟨SubNegMonoid.zsmul⟩

attribute [to_additive existing] DivInvMonoid.toZPow

/-- A group is called *cyclic* if it is generated by a single element. -/
class IsAddCyclic (G : Type u) [SMul ℤ G] : Prop where
  protected exists_zsmul_surjective : ∃ g : G, Function.Surjective (· • g : ℤ → G)

/-- A group is called *cyclic* if it is generated by a single element. -/
@[to_additive]
class IsCyclic (G : Type u) [Pow G ℤ] : Prop where
  protected exists_zpow_surjective : ∃ g : G, Function.Surjective (g ^ · : ℤ → G)

@[to_additive]
theorem exists_zpow_surjective (G : Type*) [Pow G ℤ] [IsCyclic G] :
    ∃ g : G, Function.Surjective (g ^ · : ℤ → G) :=
  IsCyclic.exists_zpow_surjective

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive (attr := simp) zsmul_eq_smul] theorem zpow_eq_pow (n : ℤ) (x : G) :
    DivInvMonoid.zpow n x = x ^ n :=
  rfl

@[to_additive (attr := simp) zero_zsmul] theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoid.zpow_zero' a

@[to_additive (attr := simp, norm_cast) natCast_zsmul]
theorem zpow_natCast (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a ^ (n : ℤ) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm


@[to_additive ofNat_zsmul]
lemma zpow_ofNat (a : G) (n : ℕ) : a ^ (ofNat(n) : ℤ) = a ^ OfNat.ofNat n :=
  zpow_natCast ..

theorem zpow_negSucc (a : G) (n : ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : ℕ) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive /-- Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_add_neg` ensuring that the types unfold better. -/]
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

@[to_additive]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

@[to_additive (attr := simp)]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

@[to_additive (attr := simp) one_zsmul]
lemma zpow_one (a : G) : a ^ (1 : ℤ) = a := by rw [zpow_ofNat, pow_one]

@[to_additive two_zsmul] lemma zpow_two (a : G) : a ^ (2 : ℤ) = a * a := by rw [zpow_ofNat, pow_two]

@[to_additive neg_one_zsmul]
lemma zpow_neg_one (x : G) : x ^ (-1 : ℤ) = x⁻¹ :=
  (zpow_negSucc x 0).trans <| congr_arg Inv.inv (pow_one x)

@[to_additive]
lemma zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ (-(n : ℤ)) = (a ^ n)⁻¹
  | _ + 1, _ => zpow_negSucc _ _

end DivInvMonoid

section InvOneClass

/-- Typeclass for expressing that `-0 = 0`. -/
class NegZeroClass (G : Type*) extends Zero G, Neg G where
  protected neg_zero : -(0 : G) = 0

/-- A `SubNegMonoid` where `-0 = 0`. -/
class SubNegZeroMonoid (G : Type*) extends SubNegMonoid G, NegZeroClass G

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
class InvOneClass (G : Type*) extends One G, Inv G where
  protected inv_one : (1 : G)⁻¹ = 1

/-- A `DivInvMonoid` where `1⁻¹ = 1`. -/
@[to_additive]
class DivInvOneMonoid (G : Type*) extends DivInvMonoid G, InvOneClass G

variable [InvOneClass G]

@[to_additive (attr := simp)]
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one

end InvOneClass

/-- A `SubtractionMonoid` is a `SubNegMonoid` with involutive negation and such that
`-(a + b) = -b + -a` and `a + b = 0 → -a = b`. -/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_add_rev (a b : G) : -(a + b) = -b + -a
  /-- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  protected neg_eq_of_add (a b : G) : a + b = 0 → -a = b

/-- A `DivisionMonoid` is a `DivInvMonoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `Group` and `GroupWithZero`. -/
@[to_additive]
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  protected mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /-- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  protected inv_eq_of_mul (a b : G) : a * b = 1 → a⁻¹ = b

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive (attr := simp) neg_add_rev]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

end DivisionMonoid

/-- Commutative `SubtractionMonoid`. -/
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G

/-- Commutative `DivisionMonoid`.

This is the immediate common ancestor of `CommGroup` and `CommGroupWithZero`. -/
@[to_additive SubtractionCommMonoid]
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G

/-- A `Group` is a `Monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.

Use `Group.ofLeftAxioms` or `Group.ofRightAxioms` to define a group structure
on a type with the minimum proof obligations.
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-- An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.

Use `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an
additive group structure on a type with the minimum proof obligations.
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : ∀ a : A, -a + a = 0

attribute [to_additive] Group

section Group

variable [Group G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

set_option backward.privateInPublic true in
@[to_additive]
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive (attr := simp)]
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹, inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

@[to_additive (attr := simp)]
theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]
theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G :=
  { inv_inv := fun a ↦ inv_eq_of_mul (inv_mul_cancel a)
    mul_inv_rev :=
      fun a b ↦ inv_eq_of_mul <| by rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    inv_eq_of_mul := fun _ _ ↦ inv_eq_of_mul }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where
  mul_right_cancel := fun a b c h ↦ by
    rw [← mul_inv_cancel_right b a, show b * a = c * a from h, mul_inv_cancel_right]
  mul_left_cancel := fun a {b c} h ↦ by
    rw [← inv_mul_cancel_left a b, show a * b = a * c from h, inv_mul_cancel_left]

end Group

/-- An additive commutative group is an additive group with commutative `(+)`. -/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
-- There is intentionally no `IsMulCommutative` for `CommGroup` instance for performance reasons.
@[to_additive]
class CommGroup (G : Type u) extends Group G, CommMonoid G

section CommGroup

variable [CommGroup G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm, mul_inv_cancel_left]

@[to_additive (attr := simp)]
lemma mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

@[to_additive (attr := simp)] lemma inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [mul_comm, mul_inv_cancel_right]

@[to_additive (attr := simp)] lemma mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_comm, inv_mul_cancel_right]

end CommGroup

namespace IsMulCommutative

/-- A magma which `IsMulCommutative` is a `CommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An additive magma which `IsMulCommutative` is a `AddCommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Mul M] [IsMulCommutative M] : CommMagma M where
  mul_comm := mul_comm'

/-- A `Semigroup` which `IsMulCommutative` is a `CommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddSemigroup` which `IsMulCommutative` is a `AddCommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Semigroup M] [IsMulCommutative M] :
    CommSemigroup M where

/-- A `Monoid` which `IsMulCommutative` is a `CommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `AddMonoid` which `IsMulCommutative` is a `AddCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Monoid M] [IsMulCommutative M] :
    CommMonoid M where

/-- A `DivisionMonoid` which `IsMulCommutative` is a `DivisionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `SubtractionMonoid` which `IsMulCommutative` is a `SubtractionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [DivisionMonoid M] [IsMulCommutative M] :
    DivisionCommMonoid M where

/-- A `Group` which `IsMulCommutative` is a `CommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddGroup` which `IsMulCommutative` is a `AddCommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {G : Type*} [Group G] [IsMulCommutative G] :
    CommGroup G where

end IsMulCommutative

/-! We initialize all projections for `@[simps]` here, so that we don't have to do it in later
files.

Note: the lemmas generated for the `npow`/`zpow` projections will *not* apply to `x ^ y`, since the
argument order of these projections doesn't match the argument order of `^`.
The `nsmul`/`zsmul` lemmas will be correct. -/
initialize_simps_projections Semigroup
initialize_simps_projections AddSemigroup
initialize_simps_projections CommSemigroup
initialize_simps_projections AddCommSemigroup
initialize_simps_projections LeftCancelSemigroup
initialize_simps_projections AddLeftCancelSemigroup
initialize_simps_projections RightCancelSemigroup
initialize_simps_projections AddRightCancelSemigroup
initialize_simps_projections Monoid
initialize_simps_projections AddMonoid
initialize_simps_projections CommMonoid
initialize_simps_projections AddCommMonoid
initialize_simps_projections LeftCancelMonoid
initialize_simps_projections AddLeftCancelMonoid
initialize_simps_projections RightCancelMonoid
initialize_simps_projections AddRightCancelMonoid
initialize_simps_projections CancelMonoid
initialize_simps_projections AddCancelMonoid
initialize_simps_projections CancelCommMonoid
initialize_simps_projections AddCancelCommMonoid
initialize_simps_projections DivInvMonoid
initialize_simps_projections SubNegMonoid
initialize_simps_projections DivInvOneMonoid
initialize_simps_projections SubNegZeroMonoid
initialize_simps_projections DivisionMonoid
initialize_simps_projections SubtractionMonoid
initialize_simps_projections DivisionCommMonoid
initialize_simps_projections SubtractionCommMonoid
initialize_simps_projections Group
initialize_simps_projections AddGroup
initialize_simps_projections CommGroup
initialize_simps_projections AddCommGroup
```

</details>

<details>
<summary>022-scalar-grep_PartialOrder.lean</summary>

SHA-256: `6515bdb4a68678b27490ec2b3332f6d7b1e529489ff9d844898ec1eda5637ec5`.

```lean
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Tactic.Trans
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.

We also define covering relations on a preorder.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

@[expose] public section

variable {α : Type*}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/--
A preorder is a reflexive, transitive relation `≤`.
In a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.
You can override this definition to set a better def-eq.
-/
class Preorder (α : Type*) extends LE α, LT α where
  protected le_refl : ∀ a : α, a ≤ a
  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

attribute [to_dual self (reorder := le_trans (a c, 4 5), lt_iff_le_not_ge (a b))] Preorder.mk

instance [Preorder α] : Std.LawfulOrderLT α where
  lt_iff := Preorder.lt_iff_le_not_ge

instance [Preorder α] : Std.IsPreorder α where
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans

variable [Preorder α] {a b c : α}

/-- The relation `≤` on a preorder is reflexive. -/
@[refl] lemma le_refl : ∀ a : α, a ≤ a := Preorder.le_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl : a ≤ a := le_refl a

/-- The relation `≤` on a preorder is transitive. -/
lemma le_trans : a ≤ b → b ≤ c → a ≤ c := Preorder.le_trans _ _ _

@[to_dual existing le_trans]
lemma ge_trans : b ≤ a → c ≤ b → c ≤ a := flip le_trans

@[to_dual self]
lemma lt_iff_le_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a := Preorder.lt_iff_le_not_ge _ _

@[to_dual self]
lemma lt_of_le_not_ge (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := lt_iff_le_not_ge.2 ⟨hab, hba⟩

@[to_dual ge_of_eq] lemma le_of_eq (hab : a = b) : a ≤ b := by rw [hab]
@[to_dual self] lemma le_of_lt (hab : a < b) : a ≤ b := (lt_iff_le_not_ge.1 hab).1
@[to_dual self] lemma not_le_of_gt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_not_ge.1 hab).2
@[to_dual self] lemma not_lt_of_ge (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self] alias LE.le.not_gt := not_lt_of_ge

lemma lt_irrefl (a : α) : ¬a < a := fun h ↦ not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']
lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']
lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]
lemma lt_trans : a < b → b < c → a < c := fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]
lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']
lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a ≤ b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a ≤ b := h.elim le_of_eq le_of_lt

@[to_dual self]
lemma lt_iff_gt_iff_le_iff_ge : (a < b ↔ b < a) ↔ (a ≤ b ↔ b ≤ a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
lemma lt_iff_le_iff_gt_iff_ge : (a < b ↔ a ≤ b) ↔ (b < a ↔ b ≤ a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
lemma lt_iff_ge_iff_gt_iff_le : (a < b ↔ b ≤ a) ↔ (b < a ↔ a ≤ b) := by
  grind [= lt_iff_le_not_ge]

instance instTransLE : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance instTransLT : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance instTransLTLE : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance instTransLELT : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
-- we have to express the following 4 instances in terms of `≥` instead of flipping the arguments
-- to `≤`, because otherwise `calc` gets confused.
@[to_dual existing instTransLE]
instance instTransGE : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
@[to_dual existing instTransLT]
instance instTransGT : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
@[to_dual existing instTransLTLE]
instance instTransGTGE : @Trans α α α GT.gt GE.ge GT.gt := ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]
instance instTransGEGT : @Trans α α α GE.ge GT.gt GT.gt := ⟨lt_of_le_of_lt'⟩

/-- `<` is decidable if `≤` is. -/
@[implicit_reducible]
def decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α :=
  fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

/-- `WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between. This is denoted `a ⩿ b`.
-/
@[to_dual self (reorder := 3 4)]
def WCovBy (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b

to_dual_insert_cast WCovBy := by grind

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy

/-- `CovBy a b` means that `b` covers `a`. This means that `a < b` and there is no element in
between. This is denoted `a ⋖ b`. -/
@[to_dual self (reorder := 3 4)]
def CovBy {α : Type*} [LT α] (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b

to_dual_insert_cast CovBy := by grind

@[inherit_doc]
infixl:50 " ⋖ " => CovBy

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type*) extends Preorder α where
  protected le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

attribute [to_dual self (reorder := le_antisymm (3 4))] PartialOrder.mk

instance [PartialOrder α] : Std.IsPartialOrder α where
  le_antisymm := PartialOrder.le_antisymm

variable [PartialOrder α] {a b : α}

lemma le_antisymm : a ≤ b → b ≤ a → a = b := PartialOrder.le_antisymm _ _

@[to_dual existing le_antisymm]
lemma ge_antisymm : b ≤ a → a ≤ b → a = b := flip le_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]
lemma le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']
lemma lt_of_le_of_ne : a ≤ b → a ≠ b → a < b := fun h₁ h₂ =>
  lt_of_le_not_ge h₁ <| mt (le_antisymm h₁) h₂

/-- Equality is decidable if `≤` is. -/
def decidableEqOfDecidableLE [DecidableLE α] : DecidableEq α
  | a, b =>
    if hab : a ≤ b then
      if hba : b ≤ a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

-- See Note [decidable namespace]
@[to_dual Decidable.lt_or_eq_of_le']
protected lemma Decidable.lt_or_eq_of_le [DecidableLE α] (hab : a ≤ b) : a < b ∨ a = b :=
  if hba : b ≤ a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']
protected lemma Decidable.le_iff_lt_or_eq [DecidableLE α] : a ≤ b ↔ a < b ∨ a = b :=
  ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']
lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']
lemma le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b := open scoped Classical in Decidable.le_iff_lt_or_eq

end PartialOrder
```

</details>

<details>
<summary>022-scalar-grep_Real.lean</summary>

SHA-256: `c95c6cf267c91508f3f839ea8d2c3baf74c86d8649c7833f0132a32081e5a929`.

```lean
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Qq

/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/

@[expose] public section


noncomputable section

open Real ComplexConjugate Finset Set

/-
## Definitions
-/
namespace Real
variable {x y z : ℝ}

/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re

noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl

theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl

theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]

theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]

theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]

@[simp, norm_cast]
theorem rpow_intCast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_intCast, Complex.ofReal_intCast,
    Complex.ofReal_re]

@[simp, norm_cast]
theorem rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by simpa using rpow_intCast x n

@[simp, norm_cast]
theorem rpow_neg_natCast (x : ℝ) (n : ℕ) : x ^ (-n : ℝ) = x ^ (-n : ℤ) := by
  rw [← rpow_intCast, Int.cast_neg, Int.cast_natCast]

@[simp]
lemma rpow_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (ofNat(n) : ℕ) :=
  rpow_natCast x n

@[simp]
theorem rpow_neg_ofNat (x : ℝ) (n : ℕ) [n.AtLeastTwo] : x ^ (-ofNat(n) : ℝ) = x ^ (-ofNat(n) : ℤ) :=
  rpow_neg_natCast _ _

@[simp]
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]

@[simp] lemma exp_one_pow (n : ℕ) : exp 1 ^ n = exp n := by rw [← rpow_natCast, exp_one_rpow]

theorem rpow_eq_zero_iff_of_nonneg (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]

@[simp]
lemma rpow_eq_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by
  simp [rpow_eq_zero_iff_of_nonneg, *]

lemma rpow_ne_zero (hx : 0 ≤ x) (hy : y ≠ 0) : x ^ y ≠ 0 ↔ x ≠ 0 := by
  simp [hx, hy]

open Real

theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) := by
  rw [rpow_def, Complex.cpow_def, if_neg]
  · have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
      simp only [Complex.log, Complex.norm_real, norm_eq_abs, abs_of_neg hx, log_neg_eq_log,
        Complex.arg_ofReal_of_neg hx, Complex.ofReal_mul]
      ring
    rw [this, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ←
      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx

-- simp is called on three goals at once (leaving one), with different simp sets
set_option linter.flexible false in
theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _

@[bound]
theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx]; apply exp_pos

@[simp]
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]

theorem rpow_zero_pos (x : ℝ) : 0 < x ^ (0 : ℝ) := by simp

@[simp]
theorem pi_rpow_zero {α : Type*} (f : α → ℝ) : f ^ (0 : ℝ) = 1 := by ext; simp

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]

theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _

theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]

@[simp]
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]

@[simp]
theorem pi_rpow_one {α : Type*} (f : α → ℝ) : f ^ (1 : ℝ) = f := by ext; simp

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]

theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]

@[bound]
theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]

theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y := by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]

@[bound]
theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)

theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) := by
  refine (abs_rpow_le_abs_rpow x y).trans ?_
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]

lemma rpow_inv_log (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ (log x)⁻¹ = exp 1 := by
  rw [rpow_def_of_pos hx₀, mul_inv_cancel₀]
  exact log_ne_zero.2 ⟨hx₀.ne', hx₁, by bound⟩

/-- See `Real.rpow_inv_log` for the equality when `x ≠ 1` is strictly positive. -/
lemma rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ ≤ exp 1 := by
  calc
    _ ≤ |x ^ (log x)⁻¹| := le_abs_self _
    _ ≤ |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_lt'
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y := by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg

variable {w x y z : ℝ}

theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]

theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _

/-- Variant of `Real.rpow_add'` that avoids having to prove `y + z = w` twice. -/
lemma rpow_of_add_eq (hx : 0 ≤ x) (hw : w ≠ 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h, rpow_add' hx]; rwa [h]

theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right-hand side is `1` while the left-hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) := by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 := by
          gcongr
          exacts [zero_rpow_nonneg z, zero_rpow_le_one y, zero_rpow_le_one z]
        _ = 1 := by simp
    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]

theorem rpow_sum_of_pos {ι : Type*} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x :=
  map_sum (⟨⟨fun (x : ℝ) => (a ^ x : ℝ), rpow_zero a⟩, rpow_add ha⟩ : ℝ →+ (Additive ℝ)) f s

theorem rpow_sum_of_nonneg {ι : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x ∈ s, f x) = ∏ x ∈ s, a ^ f x := by
  induction s using Finset.cons_induction with
  | empty => rw [sum_empty, Finset.prod_empty, rpow_zero]
  | cons i s hi ihs =>
    rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]

/-- See also `rpow_neg` for a version with `(x ^ y)⁻¹` in the RHS. -/
theorem rpow_neg_eq_inv_rpow (x y : ℝ) : x ^ (-y) = x⁻¹ ^ y := by
  simp [rpow_def, Complex.cpow_neg, Complex.inv_cpow_eq_ite, apply_ite]

/-- See also `rpow_neg_eq_inv_rpow` for a version with `x⁻¹ ^ y` in the RHS. -/
theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]

theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]

theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]

protected theorem _root_.HasCompactSupport.rpow_const {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (fun x ↦ f x ^ r) :=
  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

theorem ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]

theorem ofReal_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * I * y) := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, norm_neg, arg_ofReal_of_neg hlt, ← ofReal_neg, arg_ofReal_of_nonneg (neg_nonneg.2 hx),
    ofReal_zero, zero_mul, add_zero]

lemma cpow_ofReal (x : ℂ) (y : ℝ) :
    x ^ (y : ℂ) = ↑(‖x‖ ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [re_ofReal_mul, im_ofReal_mul, log_re, log_im, mul_comm y, mul_comm y, Real.exp_mul,
      Real.exp_log]
    rwa [norm_pos_iff]

lemma cpow_ofReal_re (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).re = ‖x‖ ^ y * Real.cos (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

lemma cpow_ofReal_im (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).im = ‖x‖ ^ y * Real.sin (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

theorem norm_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, norm_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

theorem norm_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact norm_cpow_of_ne_zero hz w; rw [norm_zero]]
  rcases eq_or_ne w.re 0 with hw | hw
  · simp [h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, norm_zero]
    exact ne_of_apply_ne re hw

theorem norm_cpow_le (z w : ℂ) : ‖z ^ w‖ ≤ ‖z‖ ^ w.re / Real.exp (arg z * im w) := by
  by_cases! h : z = 0 → w.re = 0 → w = 0
  · exact (norm_cpow_of_imp h).le
  · simp [h]

@[simp]
theorem norm_cpow_real (x : ℂ) (y : ℝ) : ‖x ^ (y : ℂ)‖ = ‖x‖ ^ y := by
  rw [norm_cpow_of_imp] <;> simp

@[simp]
theorem norm_cpow_inv_nat (x : ℂ) (n : ℕ) : ‖x ^ (n⁻¹ : ℂ)‖ = ‖x‖ ^ (n⁻¹ : ℝ) := by
  rw [← norm_cpow_real]; simp

theorem norm_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : ‖(x : ℂ) ^ y‖ = x ^ y.re := by
  rw [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), arg_ofReal_of_nonneg hx.le,
    zero_mul, Real.exp_zero, div_one, Complex.norm_of_nonneg hx.le]

theorem norm_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    ‖(x : ℂ) ^ y‖ = x ^ re y := by
  rw [norm_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, abs_of_nonneg]

open Filter in
lemma norm_ofReal_cpow_eventually_eq_atTop (c : ℂ) :
    (fun t : ℝ ↦ ‖(t : ℂ) ^ c‖) =ᶠ[atTop] fun t ↦ t ^ c.re := by
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_cpow_eq_rpow_re_of_pos ht]

lemma norm_natCast_cpow_of_re_ne_zero (n : ℕ) {s : ℂ} (hs : s.re ≠ 0) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg n.cast_nonneg hs]

lemma norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ (s.re) := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) _]

lemma norm_natCast_cpow_pos_of_pos {n : ℕ} (hn : 0 < n) (s : ℂ) : 0 < ‖(n : ℂ) ^ s‖ :=
  (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

theorem cpow_mul_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℂ) :
    (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z := by
  rw [cpow_mul, ofReal_cpow hx]
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im, neg_lt_zero]; exact Real.pi_pos
  · rw [← ofReal_log hx, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

end Complex

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is positive (namely 1)
when the exponent is zero. The other cases are done in `evalRpow`. -/
@[positivity (_ : ℝ) ^ (0 : ℝ)]
meta def evalRpowZero : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(Real.rpow_zero_pos $a))
  | _, _, _ => throwError "not Real.rpow"

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : ℝ) ^ (_ : ℝ)]
meta def evalRpow : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q($a ^ ($b : ℝ)) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa =>
        pure (.positive q(Real.rpow_pos_of_pos $pa $b))
    | .nonnegative pa =>
        pure (.nonnegative q(Real.rpow_nonneg $pa $b))
    | _ => pure .none
  | _, _, _ => throwError "not Real.rpow"

end Mathlib.Meta.Positivity

/-!
## Further algebraic properties of `rpow`
-/


namespace Real

variable {x y z : ℝ} {n : ℕ}

theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.ofReal_inj, Complex.ofReal_cpow (rpow_nonneg hx _),
      Complex.ofReal_cpow hx, Complex.ofReal_mul, Complex.cpow_mul, Complex.ofReal_cpow hx] <;>
    simp only [(Complex.ofReal_mul _ _).symm, (Complex.ofReal_log hx).symm, Complex.ofReal_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]

lemma rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_natCast, ← rpow_mul hx, mul_comm y]

lemma rpow_zpow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : (x ^ y) ^ n = (x ^ n) ^ y := by
  simp_rw [← rpow_intCast, ← rpow_mul hx, mul_comm y]

lemma rpow_add_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_def, rpow_def, Complex.ofReal_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx), Complex.ofReal_intCast,
    Complex.cpow_intCast, ← Complex.ofReal_zpow, mul_comm, Complex.re_ofReal_mul, mul_comm]

lemma rpow_add_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  simpa using rpow_add_intCast hx y n

lemma rpow_sub_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_add_intCast hx y (-n)

lemma rpow_sub_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_sub_intCast hx y n

lemma rpow_add_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_intCast]

lemma rpow_add_natCast' (hx : 0 ≤ x) (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_add' hx h, rpow_natCast]

lemma rpow_sub_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_intCast]

lemma rpow_sub_natCast' (hx : 0 ≤ x) (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
  rw [rpow_sub' hx h, rpow_natCast]

theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1

theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1

lemma rpow_add_one' (hx : 0 ≤ x) (h : y + 1 ≠ 0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' hx h, rpow_one]

lemma rpow_one_add' (hx : 0 ≤ x) (h : 1 + y ≠ 0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' hx h, rpow_one]

lemma rpow_sub_one' (hx : 0 ≤ x) (h : y - 1 ≠ 0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' hx h, rpow_one]

lemma rpow_one_sub' (hx : 0 ≤ x) (h : 1 - y ≠ 0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' hx h, rpow_one]

theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  simp

theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [rpow_neg_eq_inv_rpow, rpow_one]

-- TODO: fix non-terminal simp (acting on three goals, with different simp sets, leaving two)
set_option linter.flexible false in
theorem mul_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
  iterate 2 rw [Real.rpow_def_of_nonneg]; split_ifs with h_ifs <;> simp_all
  · rw [log_mul ‹_› ‹_›, add_mul, exp_add, rpow_def_of_pos (hy.lt_of_ne' ‹_›)]
  all_goals positivity

theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rw [← rpow_neg_eq_inv_rpow, rpow_neg hx]

theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]

@[push low] /- Lower priority than `log_pow` and `log_zpow`.
This is because otherwise the `pull` tactic will use `log_rpow` in places where it should
use `log_pow` or `log_zpow`. -/
theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x := by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]

theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩

@[simp] lemma rpow_rpow_inv (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul hx, mul_inv_cancel₀ hy, rpow_one]

@[simp] lemma rpow_inv_rpow (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul hx, inv_mul_cancel₀ hy, rpow_one]

theorem pow_rpow_inv_natCast (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, mul_inv_cancel₀ hn0, rpow_one]

theorem rpow_inv_natCast_pow (hx : 0 ≤ x) (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_natCast, ← rpow_mul hx, inv_mul_cancel₀ hn0, rpow_one]

lemma rpow_natCast_mul (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_natCast]

lemma rpow_mul_natCast (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_natCast]

lemma rpow_intCast_mul (hx : 0 ≤ x) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul hx, rpow_intCast]

lemma rpow_mul_intCast (hx : 0 ≤ x) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul hx, rpow_intCast]

/-! Note: lemmas about `(∏ i ∈ s, f i ^ r)` such as `Real.finsetProd_rpow` are proved
in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` instead. -/

/-!
## Order and monotonicity
-/


@[gcongr, bound]
theorem rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := by
  rw [le_iff_eq_or_lt] at hx; rcases hx with hx | hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz

theorem strictMonoOn_rpow_Ici_of_exponent_pos {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr, bound]
theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')

theorem monotoneOn_rpow_Ici_of_exponent_nonneg {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_le_rpow ha hab hr

lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z := by
  have := hx.trans hxy
  rw [← inv_lt_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_lt_rpow ?_ hxy (neg_pos.2 hz)
  all_goals positivity

lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z := by
  have := hx.trans_le hxy
  rw [← inv_le_inv₀, ← rpow_neg, ← rpow_neg]
  on_goal 1 => refine rpow_le_rpow ?_ hxy (neg_nonneg.2 hz)
  all_goals positivity

theorem rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h ↦ by gcongr, fun h ↦ by gcongr⟩

theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff hy hx hz

lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  ⟨lt_imp_lt_of_le_imp_le fun h ↦ rpow_le_rpow_of_nonpos hx h hz.le,
    fun h ↦ rpow_lt_rpow_of_neg hy h hz⟩

lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff_of_neg hy hx hz

lemma le_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hx _ hz, rpow_inv_rpow] <;> positivity

lemma rpow_inv_le_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff _ hy hz, rpow_inv_rpow] <;> positivity

lemma lt_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  lt_iff_lt_of_le_iff_le <| rpow_inv_le_iff_of_pos hy hx hz

lemma rpow_inv_lt_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  lt_iff_lt_of_le_iff_le <| le_rpow_inv_iff_of_pos hy hx hz

theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z := by
  rw [← rpow_le_rpow_iff_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x < y ^ z⁻¹ ↔ y < x ^ z := by
  rw [← rpow_lt_rpow_iff_of_neg _ hx hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ < y ↔ y ^ z < x := by
  rw [← rpow_lt_rpow_iff_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  rw [← rpow_le_rpow_iff_of_neg hy _ hz, rpow_inv_rpow _ hz.ne] <;> positivity

theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)

@[gcongr]
theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; gcongr; exact log_nonneg hx

@[deprecated (since := "2025-10-28")] alias rpow_lt_rpow_of_exponent_neg :=
  rpow_lt_rpow_of_neg

theorem strictAntiOn_rpow_Ioi_of_exponent_neg {r : ℝ} (hr : r < 0) :
    StrictAntiOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow_of_neg ha hab hr

@[deprecated (since := "2025-10-28")] alias rpow_le_rpow_of_exponent_nonpos :=
  rpow_le_rpow_of_nonpos

theorem antitoneOn_rpow_Ioi_of_exponent_nonpos {r : ℝ} (hr : r ≤ 0) :
    AntitoneOn (fun (x : ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr

@[simp]
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z := by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_iff_left₀ (log_pos hx)]

@[simp]
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_ge, rpow_le_rpow_left_iff hx, lt_iff_not_ge]

theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)

theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)

@[simp]
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y ≤ x ^ z ↔ z ≤ y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]

@[simp]
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y < x ^ z ↔ z < y := by
  rw [lt_iff_not_ge, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_ge]

theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz

theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  rw [← one_rpow z]
  gcongr

theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  convert rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm

theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 := by
  convert rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm

theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz

theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  rw [← one_rpow z]
  gcongr

theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
    1 < x ^ z := by
  convert rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm

theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm

theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx.le, log_neg_iff hx]

theorem rpow_lt_one_iff (hx : 0 ≤ x) :
    x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]

theorem rpow_lt_one_iff' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x ^ y < 1 ↔ x < 1 := by
  rw [← Real.rpow_lt_rpow_iff hx zero_le_one hy, Real.one_rpow]

theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx.le, log_neg_iff hx]

theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, (zero_lt_one' ℝ).not_gt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]

/-- This is a more general but less convenient version of `rpow_le_rpow_of_exponent_ge`.
This version allows `x = 0`, so it explicitly forbids `x = y = 0`, `z ≠ 0`. -/
theorem rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y)
    (h : x = 0 → y = 0 → z = 0) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [h rfl rfl]
    · rw [zero_rpow hy0]
      apply zero_rpow_nonneg
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz

/-- This version of `rpow_le_rpow_of_exponent_ge` allows `x = 0` but requires `0 ≤ z`.
See also `rpow_le_rpow_of_exponent_ge_of_imp` for the most general version. -/
theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  rpow_le_rpow_of_exponent_ge_of_imp hx0 hx1 hyz fun _ hy ↦ le_antisymm (hyz.trans_eq hy) hz

lemma rpow_max {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) :
    (max x y) ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (by gcongr)]
  · rw [max_eq_left hxy, max_eq_left (by gcongr)]

theorem self_le_rpow_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : y ≤ 1) : x ≤ x ^ y := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · one_ne_zero)

theorem self_le_rpow_of_one_le (h₁ : 1 ≤ x) (h₂ : 1 ≤ y) : x ≤ x ^ y := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

theorem rpow_le_self_of_le_one (h₁ : 0 ≤ x) (h₂ : x ≤ 1) (h₃ : 1 ≤ y) : x ^ y ≤ x := by
  simpa only [rpow_one]
    using rpow_le_rpow_of_exponent_ge_of_imp h₁ h₂ h₃ fun _ ↦ (absurd · (one_pos.trans_le h₃).ne')

theorem rpow_le_self_of_one_le (h₁ : 1 ≤ x) (h₂ : y ≤ 1) : x ^ y ≤ x := by
  simpa only [rpow_one] using rpow_le_rpow_of_exponent_le h₁ h₂

theorem self_lt_rpow_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : y < 1) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

theorem self_lt_rpow_of_one_lt (h₁ : 1 < x) (h₂ : 1 < y) : x < x ^ y := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

theorem rpow_lt_self_of_lt_one (h₁ : 0 < x) (h₂ : x < 1) (h₃ : 1 < y) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_gt h₁ h₂ h₃

theorem rpow_lt_self_of_one_lt (h₁ : 1 < x) (h₂ : y < 1) : x ^ y < x := by
  simpa only [rpow_one] using rpow_lt_rpow_of_exponent_lt h₁ h₂

theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } := by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← mul_inv_cancel₀ hx, rpow_mul hy, rpow_mul hz, hyz]

lemma rpow_left_inj (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injOn hz).eq_iff hx hy

lemma rpow_inv_eq (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_left_inj _ hy hz, rpow_inv_rpow hx hz]; positivity

lemma eq_rpow_inv (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_left_inj hx _ hz, rpow_inv_rpow hy hz]; positivity

theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ log x ≤ z * log y := by
  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]

lemma le_pow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_natCast _ _ ▸ le_rpow_iff_log_le hx hy

lemma le_zpow_iff_log_le {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y :=
  rpow_intCast _ _ ▸ le_rpow_iff_log_le hx hy

lemma le_rpow_of_log_le (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

lemma le_pow_of_log_le (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ le_rpow_of_log_le hy h

lemma le_zpow_of_log_le {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ le_rpow_of_log_le hy h

theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ log x < z * log y := by
  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]

lemma lt_pow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_natCast _ _ ▸ lt_rpow_iff_log_lt hx hy

lemma lt_zpow_iff_log_lt {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y :=
  rpow_intCast _ _ ▸ lt_rpow_iff_log_lt hx hy

lemma lt_rpow_of_log_lt (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

lemma lt_pow_of_log_lt (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ lt_rpow_of_log_lt hy h

lemma lt_zpow_of_log_lt {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ lt_rpow_of_log_lt hy h

lemma rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z ≤ y ↔ z * log x ≤ log y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma pow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_natCast]

lemma zpow_le_iff_le_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n ≤ y ↔ n * log x ≤ log y := by
  rw [← rpow_le_iff_le_log hx hy, rpow_intCast]

lemma le_log_of_rpow_le (hx : 0 < x) (h : x ^ z ≤ y) : z * log x ≤ log y :=
  log_rpow hx _ ▸ log_le_log (by positivity) h

lemma le_log_of_pow_le (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_natCast _ _ ▸ h)

lemma le_log_of_zpow_le {n : ℤ} (hx : 0 < x) (h : x ^ n ≤ y) : n * log x ≤ log y :=
  le_log_of_rpow_le hx (rpow_intCast _ _ ▸ h)

lemma rpow_le_of_le_log (hy : 0 < y) (h : log x ≤ z * log y) : x ≤ y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans (rpow_pos_of_pos hy _).le
  · exact (le_rpow_iff_log_le hx hy).2 h

lemma pow_le_of_le_log (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_natCast _ _ ▸ rpow_le_of_le_log hy h

lemma zpow_le_of_le_log {n : ℤ} (hy : 0 < y) (h : log x ≤ n * log y) : x ≤ y ^ n :=
  rpow_intCast _ _ ▸ rpow_le_of_le_log hy h

lemma rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log y := by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma pow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_natCast]

lemma zpow_lt_iff_lt_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ^ n < y ↔ n * log x < log y := by
  rw [← rpow_lt_iff_lt_log hx hy, rpow_intCast]

lemma lt_log_of_rpow_lt (hx : 0 < x) (h : x ^ z < y) : z * log x < log y :=
  log_rpow hx _ ▸ log_lt_log (by positivity) h

lemma lt_log_of_pow_lt (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_natCast _ _ ▸ h)

lemma lt_log_of_zpow_lt {n : ℤ} (hx : 0 < x) (h : x ^ n < y) : n * log x < log y :=
  lt_log_of_rpow_lt hx (rpow_intCast _ _ ▸ h)

lemma rpow_lt_of_lt_log (hy : 0 < y) (h : log x < z * log y) : x < y ^ z := by
  obtain hx | hx := le_or_gt x 0
  · exact hx.trans_lt (rpow_pos_of_pos hy _)
  · exact (lt_rpow_iff_log_lt hx hy).2 h

lemma pow_lt_of_lt_log (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_natCast _ _ ▸ rpow_lt_of_lt_log hy h

lemma zpow_lt_of_lt_log {n : ℤ} (hy : 0 < y) (h : log x < n * log y) : x < y ^ n :=
  rpow_intCast _ _ ▸ rpow_lt_of_lt_log hy h

theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx.le]

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff₀ ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this

/-- `log x` is bounded above by a multiple of every power of `x` with positive exponent. -/
lemma log_le_rpow_div {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) : log x ≤ x ^ ε / ε := by
  rcases hx.eq_or_lt with rfl | h
  · rw [log_zero, zero_rpow hε.ne', zero_div]
  rw [le_div_iff₀' hε]
  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
    (sub_one_lt _).le

/-- The (real) logarithm of a natural number `n` is bounded by a multiple of every power of `n`
with positive exponent. -/
lemma log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : log n ≤ n ^ ε / ε :=
  log_le_rpow_div n.cast_nonneg hε

lemma strictMono_rpow_of_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMono (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
  exact exp_strictMono.comp <| StrictMono.const_mul strictMono_id <| Real.log_pos hb

lemma monotone_rpow_of_base_ge_one {b : ℝ} (hb : 1 ≤ b) :
    Monotone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

lemma strictAnti_rpow_of_base_lt_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictAnti (b ^ · : ℝ → ℝ) := by
  simp_rw [Real.rpow_def_of_pos hb₀]
  exact exp_strictMono.comp_strictAnti <| StrictMono.const_mul_of_neg strictMono_id
      <| Real.log_neg hb₀ hb₁

lemma antitone_rpow_of_base_le_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b ≤ 1) :
    Antitone (b ^ · : ℝ → ℝ) := by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

lemma rpow_right_inj (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_gt with h | h
  · exact (strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (strictMono_rpow_of_base_gt_one h).injective H

/-- Guessing rule for the `bound` tactic: when trying to prove `x ^ y ≤ x ^ z`, we can either assume
`1 ≤ x` or `0 < x ≤ 1`. -/
@[bound] lemma rpow_le_rpow_of_exponent_le_or_ge {x y z : ℝ}
    (h : 1 ≤ x ∧ y ≤ z ∨ 0 < x ∧ x ≤ 1 ∧ z ≤ y) : x ^ y ≤ x ^ z := by
  rcases h with ⟨x1, yz⟩ | ⟨x0, x1, zy⟩
  · exact Real.rpow_le_rpow_of_exponent_le x1 yz
  · exact Real.rpow_le_rpow_of_exponent_ge x0 x1 zy

end Real

namespace Complex

lemma norm_prime_cpow_le_one_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_natCast_cpow_of_re_ne_zero p <| by rw [neg_re]; linarith only [hs]]
  refine (Real.rpow_le_rpow_of_nonpos zero_lt_two (Nat.cast_le.mpr p.prop.two_le) <|
    by rw [neg_re]; linarith only [hs]).trans ?_
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two <| (neg_lt_neg hs).le

lemma one_sub_prime_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  refine sub_ne_zero_of_ne fun H ↦ ?_
  have := norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only at this
  rw [← H, norm_one] at this
  norm_num at this

lemma norm_natCast_cpow_le_norm_natCast_cpow_of_pos {n : ℕ} (hn : 0 < n) {w z : ℂ}
    (h : w.re ≤ z.re) :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ := by
  simp_rw [norm_natCast_cpow_of_pos hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

lemma norm_natCast_cpow_le_norm_natCast_cpow_iff {n : ℕ} (hn : 1 < n) {w z : ℂ} :
    ‖(n : ℂ) ^ w‖ ≤ ‖(n : ℂ) ^ z‖ ↔ w.re ≤ z.re := by
  simp_rw [norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hn),
    Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hn)]

lemma norm_log_natCast_le_rpow_div (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ‖log n‖ ≤ n ^ ε / ε := by
  rcases n.eq_zero_or_pos with rfl | h
  · rw [Nat.cast_zero, Nat.cast_zero, log_zero, norm_zero, Real.zero_rpow hε.ne', zero_div]
  rw [← natCast_log, norm_real, norm_of_nonneg <| Real.log_nonneg <| by
    exact_mod_cast Nat.one_le_of_lt h.lt]
  exact Real.log_natCast_le_rpow_div n hε

end Complex


/-!
## Square roots of reals
-/


namespace Real

variable {z x y : ℝ}

section Sqrt

theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
  obtain h | h := le_or_gt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_natCast, ← rpow_mul h]
    simp
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]

theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = √x ^ r := by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring

end Sqrt

end Real

namespace Complex

lemma cpow_inv_two_re (x : ℂ) : (x ^ (2⁻¹ : ℂ)).re = √((‖x‖ + x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_re, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, cos_half, ← sqrt_mul, ← mul_div_assoc, mul_add, mul_one, norm_mul_cos_arg]
  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

lemma cpow_inv_two_im_eq_sqrt {x : ℂ} (hx : 0 ≤ x.im) :
    (x ^ (2⁻¹ : ℂ)).im = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub,
    mul_one, norm_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

lemma cpow_inv_two_im_eq_neg_sqrt {x : ℂ} (hx : x.im < 0) :
    (x ^ (2⁻¹ : ℂ)).im = -√((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (norm_nonneg _),
    ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

lemma abs_cpow_inv_two_im (x : ℂ) : |(x ^ (2⁻¹ : ℂ)).im| = √((‖x‖ - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
    ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]

open scoped ComplexOrder in
lemma inv_natCast_cpow_ofReal_pos {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    0 < ((n : ℂ) ^ (x : ℂ))⁻¹ := by
  refine RCLike.inv_pos_of_pos ?_
  rw [show (n : ℂ) ^ (x : ℂ) = (n : ℝ) ^ (x : ℂ) from rfl, ← ofReal_cpow n.cast_nonneg']
  positivity

end Complex

section Tactics

/-!
## Tactic extensions for real powers
-/
namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

theorem IsNat.rpow_eq_pow {b : ℝ} {n : ℕ} (h : IsNat b n) (a : ℝ) : a ^ b = a ^ n := by
  rw [h.1, Real.rpow_natCast]

theorem IsInt.rpow_eq_inv_pow {b : ℝ} {n : ℕ} (h : IsInt b (.negOfNat n)) (a : ℝ) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1, Real.rpow_intCast, Int.negOfNat_eq, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isNat_rpow_pos {a b : ℝ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsNat (a ^ nb) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isNat_rpow_neg {a b : ℝ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNat (a ^ (Int.negOfNat nb)) ne) :
    IsNat (a ^ b) ne := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isInt_rpow_pos {a b : ℝ} {nb ne : ℕ}
    (pb : IsNat b nb) (pe' : IsInt (a ^ nb) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isInt_rpow_neg {a b : ℝ} {nb ne : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsInt (a ^ (Int.negOfNat nb)) (Int.negOfNat ne)) :
    IsInt (a ^ b) (Int.negOfNat ne) := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isNNRat_rpow_pos {a b : ℝ} {nb : ℕ}
    {num den : ℕ}
    (pb : IsNat b nb) (pe' : IsNNRat (a ^ nb) num den) :
    IsNNRat (a ^ b) num den := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsNat.rpow_eq_pow (since := "2025-10-21")]
theorem isRat_rpow_pos {a b : ℝ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsNat b nb) (pe' : IsRat (a ^ nb) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, rpow_natCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isNNRat_rpow_neg {a b : ℝ} {nb : ℕ}
    {num den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsNNRat (a ^ (Int.negOfNat nb)) num den) :
    IsNNRat (a ^ b) num den := by
  rwa [pb.out, Real.rpow_intCast]

@[deprecated IsInt.rpow_eq_inv_pow (since := "2025-10-21")]
theorem isRat_rpow_neg {a b : ℝ} {nb : ℕ}
    {num : ℤ} {den : ℕ}
    (pb : IsInt b (Int.negOfNat nb)) (pe' : IsRat (a ^ (Int.negOfNat nb)) num den) :
    IsRat (a ^ b) num den := by
  rwa [pb.out, Real.rpow_intCast]

/-- Given proofs
- that `a` is a natural number `m`
- that `b` is a nonnegative rational number `n / d`
- that `r ^ d = m ^ n` (written as `r ^ d = k`, `m ^ n = l`, `k = l`)

prove that `a ^ b = r`.
-/
theorem IsNat.rpow_isNNRat {a b : ℝ} {m n d r : ℕ} (ha : IsNat a m) (hb : IsNNRat b n d)
    (k : ℕ) (hr : r ^ d = k) (l : ℕ) (hm : m ^ n = l) (hkl : k = l) : IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d ≠ 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl, div_eq_mul_inv, Real.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
    Nat.cast_pow, Real.pow_rpow_inv_natCast] <;> positivity

theorem IsNNRat.rpow_isNNRat (a b : ℝ) (na da : ℕ) (ha : IsNNRat a na da)
    (nr dr : ℕ) (hnum : IsNat ((na : ℝ) ^ b) nr) (hden : IsNat ((da : ℝ) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : ℝ) nr dr by
    simpa [ha.to_eq, Real.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  rw [← hden.1]
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact lt_of_le_of_ne' da.cast_nonneg ha.den_nz

theorem rpow_isRat_eq_inv_rpow (a b : ℝ) (n d : ℕ) (hb : IsRat b (Int.negOfNat n) d) :
    a ^ b = (a⁻¹) ^ (n / d : ℝ) := by
  rw [← Real.rpow_neg_eq_inv_rpow, hb.neg_to_eq rfl rfl]

open Lean in
/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatRPowIsNNRat
    (a : Q(ℝ)) (na : Q(ℕ)) (pa : Q(IsNat $a $na))
    (b : Q(ℝ)) (nb db : Q(ℕ)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (ℕ × Σ r : Q(ℕ), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(ℕ) := mkRawNatLit r
  -- avoid evaluating powers in kernel
  let .some ⟨c, pc⟩ ← liftM <| OptionT.run <| evalNatPow er db | failure
  let .some ⟨d, pd⟩ ← liftM <| OptionT.run <| evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a` and `b` are both reals.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers,
except for the case `a < 0`, `b` isn't integer.

TODO: simplify terms like  `(-a : ℝ) ^ (b / 3 : ℝ)` and `(-a : ℝ) ^ (b / 2 : ℝ)` too,
possibly after first considering changing the junk value. -/
@[norm_num (_ : ℝ) ^ (_ : ℝ)]
meta def evalRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(ℝ), ~q(($a : ℝ)^($b : ℝ)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.rpow_eq_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.rpow_eq_inv_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : ℝ))
      assumeInstancesCommute
      return .eqTrans q(rpow_isRat_eq_inv_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

end Tactics
```

</details>

<details>
<summary>024-final-statements_final-statements.lean</summary>

SHA-256: `2ae50c2506a78b695410107b252f18334815c8969d044070782e6c94f0deccaa`.

```lean
import Poincare.Global.NearFrozenParabolicRightInverse
set_option pp.proofs false
#print mul_comm
#print le_of_eq
```

</details>

<details>
<summary>025-imported-target_imported-target.lean</summary>

SHA-256: `cba2f2205f99fafcdd1b3af3ad50f4c4485f85736981ebb04cc5e58e3481cca5`.

```lean
import Poincare.Global.NearFrozenParabolicRightInverse


namespace Poincare.NearFrozenParabolicRightInverse
open Set
local notation "E" => ClosedSmoothModel 3
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
example :
  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
  ∀ (A₀ : Bilin), (∀ v w, A₀ v w = A₀ w v) →
    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := E) α T ℝ) (Λb : ℝ),
    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ ε₀) →
    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := E) T) (b i j) ≤ Λb) →
    Λb * T ^ (α/2) ≤ ε₀ →
  ∀ f : ParabolicHolder.Y («E» := E) α T ℝ,
    ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
      (∀ t ∈ Icc 0 T, ∀ x : E, G.ut (t, x) = f (t, x) +
        ∑ i, ∑ j, (A₀ (e i) (e j) + b i j (t, x)) * G.ddu (t, x) (e i) (e j)) ∧
      ‖G‖ ≤ C * ‖f‖ := exists_nearFrozen_solution
end Poincare.NearFrozenParabolicRightInverse
```

</details>

<details>
<summary>031-frozen-scope_Poincare.lean</summary>

SHA-256: `8701d62a4f5e185173a2727e2d6eae85ba12c39fcffff487122918622407fc9e`.

```lean
import Poincare.RiemannCurvatureOperator
import Poincare.FlatModelConnection
import Poincare.LeviCivitaUniqueness
import Poincare.BianchiIdentity
import Poincare.RicciFlowEquation
import Poincare.LocalConnectionRegularity
import Poincare.ChartIdentification
import Poincare.CurvatureTensoriality
import Poincare.KoszulExistence
import Poincare.EuclideanLeviCivitaCheck
import Poincare.CurvatureConditions
import Poincare.ModelChristoffel
import Poincare.ChartTransport
import Poincare.MaximumPrinciple
import Poincare.ModelLaplacian
import Poincare.ModelLaplacianRootAliases
import Poincare.Statement
import Poincare.Global.CartanSuppliedBufferedPairAgreement
import Poincare.Global.CartanSuppliedDifferentialSuccessor
import Poincare.Global.CartanSuppliedDifferentialTransfer
import Poincare.Global.CartanSuppliedFinitePatchCover
import Poincare.Global.CartanSuppliedHomotopyEndpoints
import Poincare.Global.CartanSuppliedPatchPolicy
import Poincare.Global.CartanSuppliedReachableChain
import Poincare.Global.CartanSuppliedRestrictedDevelopment
import Poincare.Global.CartanSuppliedSourceGermTransfer
import Poincare.Global.CartanSuppliedSourceMap
import Poincare.Global.CartanSuppliedSubdivisionTransport
import Poincare.Global.CartanSuppliedTerminalTransport
import Poincare.Global.CartanSuppliedUniformPatchSwitch
import Poincare.Global.CartanSuppliedUnitRecognition
import Poincare.Global.CartanSuppliedWholeCellRealization
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.ClosedLaplacianStokesProducer
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.CompactCoefficientEllipticity
import Poincare.Global.ConnectionInstanceNaturality
import Poincare.Global.ControlledChartInstance
import Poincare.Global.CurvatureInstanceTransport
import Poincare.Global.DeTurckPrincipalIdentity
import Poincare.Global.DeTurckPrincipalSecondJet
import Poincare.Global.DuhamelParabolicHolderSeminorm
import Poincare.Global.DuhamelSolutionOperatorBound
import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.FiniteTriangulationStatements
import Poincare.Global.FixedChartAugmentedSystemRegularity
import Poincare.Global.FixedChartEndpointSlices
import Poincare.Global.FixedChartLocalSuccessorEquality
import Poincare.Global.FixedChartLocalSuccessorExistence
import Poincare.Global.FixedChartMappedGeodesicAssembly
import Poincare.Global.FixedChartMovingPositionJacobi
import Poincare.Global.FixedChartPatchSecondVariation
import Poincare.Global.FixedChartSuccessorDataPersistence
import Poincare.Global.FixedChartUniformDifferentialPullback
import Poincare.Global.FixedChartUniformEndpointReanchoring
import Poincare.Global.FixedChartUniformJacobiComparison
import Poincare.Global.FixedChartUniformNormalRadius
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.FixedChartUniformSourceNormal
import Poincare.Global.FrozenEllipticHeatOperator
import Poincare.Global.GenericJointRegularityCounterexample
import Poincare.Global.GeodesicFlowJointDerivative
import Poincare.Global.HamiltonChartDensityLocalDomination
import Poincare.Global.HamiltonCompactFamilyInvariantContinuity
import Poincare.Global.HamiltonEndpointEquivalences
import Poincare.Global.HamiltonFamilyVolumeMeasureContinuity
import Poincare.Global.HamiltonFiniteEnergyFlowInterface
import Poincare.Global.HamiltonInitialPinchingReactionCoreReduction
import Poincare.Global.HamiltonMeanFloorFromEnergyDomination
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonPoincareReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.HamiltonReactionCoreReduced
import Poincare.Global.HamiltonReactionCoreReduction
import Poincare.Global.HamiltonReactionEndpoint
import Poincare.Global.HamiltonStokesFreeReactionCore
import Poincare.Global.HeatDuhamelHeatEquation
import Poincare.Global.HeatDuhamelHessianDifferentiation
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelSpatialHolderHessian
import Poincare.Global.HeatKernelHessianMoments
import Poincare.Global.IntrinsicLaplacianCoordinateForm
import Poincare.Global.MovingLimitLeibniz
import Poincare.Global.NearIdentityParabolicRightInverse
import Poincare.Global.NormalizedFlowInitialPinchingPreservation
import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.ParabolicHolderSpace
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ParametrixNeumannCorrection
import Poincare.Global.RiemannianMetricInstanceTransport
import Poincare.Global.RiemannianMetricInstanceTransportGeometric
import Poincare.Global.SelectedFiniteNerveSmoothingStatements
import Poincare.Global.Statement
import Poincare.Global.Alignment
import Poincare.Global.RiemannianContext
import Poincare.Global.LeviCivita
import Poincare.Global.LeviCivitaExistence
import Poincare.Global.LeviCivitaTransport
import Poincare.Global.LeviCivitaRegularity
import Poincare.Global.Curvature
import Poincare.Global.RicciNorm
import Poincare.Global.Laplacian
import Poincare.Global.RicciFlow
import Poincare.Global.BumpExtend
import Poincare.Global.AnchoredExtendRegularity
import Poincare.Global.MetricVariation
import Poincare.Global.ScalarEvolution
import Poincare.Global.ParabolicMinimumContinuousOn
import Poincare.Global.ParabolicExponentialMaximum
import Poincare.Global.ClosedRiemannianParabolicExponentialMaximum
import Poincare.Global.MetricFlowJointRegularity
import Poincare.Global.MetricFlowJointConnectionRegularity
import Poincare.Global.MetricFlowJointIteratedConnectionRegularity
import Poincare.Global.MetricFlowJointCurvatureRegularity
import Poincare.Global.MetricFlowJointScalarTraceBridge
import Poincare.Global.MetricFlowJointScalarTraceZoneBridge
import Poincare.Global.MetricFlowJointScalarContinuity
import Poincare.Global.ScalarVariation
import Poincare.Global.CovRicciNormBasis
import Poincare.Global.MetricRaiseTimeDerivative
import Poincare.Global.DeltaGammaFieldRegularity
import Poincare.Global.RicciFlowScalarRegularity
import Poincare.Global.MetricFlowJointRicciTensorEvolution
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.MetricFlowJointCovRicciEntryRegularity
import Poincare.Global.MetricFlowJointCovRicciNormContinuity
import Poincare.Global.MetricFamilyCovRicciNormContinuity
import Poincare.Global.MetricFamilyCovRicciEntryContinuity
import Poincare.Global.MetricFamilyCovRicciQuotientContinuity
import Poincare.Global.MetricFamilyThirdJetCovRicciContinuity
import Poincare.Global.MetricFamilyEntryThirdJetCovRicciContinuity
import Poincare.Global.ClosedMetricThirdJetTopology
import Poincare.Global.ClosedMetricThirdJetOrbitCompactness
import Poincare.Global.MetricEntryThirdJetProfileCompactness
import Poincare.Global.MetricEntryThirdJetProfileLimitAlgebra
import Poincare.Global.MetricEntryThirdJetFormalInverse
import Poincare.Global.MetricEntryThirdJetFormalRawCoordinates
import Poincare.Global.MetricEntryThirdJetFormalChristoffel
import Poincare.Global.MetricEntryThirdJetFormalRicci
import Poincare.Global.MetricEntryThirdJetFormalInvertibility
import Poincare.Global.MetricEntryThirdJetAnchorLowerComparison
import Poincare.Global.MetricEntryThirdJetFormalRicciBound
import Poincare.Global.ContinuousWithDensityOrder
import Poincare.Global.CompactReferenceMetricTensorFamilyLowerComparison
import Poincare.Global.ClosedMetricThirdJetAscoliOrbitCompactness
import Poincare.Global.SphereTheorem
import Poincare.Global.ScalarRegularity
import Poincare.Global.PinchedLimitInterface
import Poincare.Global.PinchedLimitCore
import Poincare.Global.PinchedLimitPositiveEinstein
import Poincare.Global.MetricCompleteness
import Poincare.Global.EinsteinNormalization
import Poincare.Global.GeodesicChart
import Poincare.Global.GeodesicTransport
import Poincare.Global.GeodesicGerm
import Poincare.Global.ExponentialGerm
import Poincare.Global.ExponentialDomain
import Poincare.Global.ExponentialMap
import Poincare.Global.ExponentialMapDef
import Poincare.Global.GeodesicOverlap
import Poincare.Global.ExponentialFixedTime
import Poincare.Global.ConformalCurvature
import Poincare.Global.GeodesicReanchor
import Poincare.Global.GeodesicReanchorLaw
import Poincare.Global.RoundSphereCurvature
import Poincare.Global.ExponentialRayLaw
import Poincare.Global.SuccessorEqualityRadiusPersistence
import Poincare.Global.UniversalUnitRecognition
import Poincare.Global.VolumeDensity
import Poincare.Global.CoordinateVolumeDensityVariation
import Poincare.Global.CoordinateChartFrameDensityVariation
import Poincare.Global.HausdorffCoordinateDensityVariation
import Poincare.Global.HausdorffVolumeFirstVariation
import Poincare.Global.HausdorffTotalScalarFirstVariation
import Poincare.Global.HausdorffChartFrameFirstVariation
import Poincare.Global.HausdorffPullbackAreaFormulaReduction
import Poincare.Global.HausdorffLinearPullbackAreaFormula
import Poincare.Global.HausdorffFrozenInverseChartAreaFormula
import Poincare.Global.HausdorffInverseChartGramContinuity
import Poincare.Global.HausdorffInverseChartGramQuadraticComparison
import Poincare.Global.HausdorffInverseChartLocalPathLengthComparison
import Poincare.Global.HausdorffRiemannianShortPathConfinement
import Poincare.Global.HausdorffInverseChartFrozenMetricBridge
import Poincare.Global.HausdorffInverseChartLocalFrozenUpper
import Poincare.Global.HausdorffInverseChartLocalFrozenHausdorffUpper
import Poincare.Global.HausdorffInverseChartLocalFrozenLower
import Poincare.Global.HausdorffInverseChartLocalFrozenBilipschitz
import Poincare.Global.HausdorffInverseChartLocalAreaSandwich
import Poincare.Global.HausdorffCoordinateDensityComparison
import Poincare.Global.HausdorffInverseChartLocalVariableDensitySqueeze
import Poincare.Global.HausdorffInverseChartMeasureTransport
import Poincare.Global.HausdorffInverseChartLocalRestrictionSqueeze
import Poincare.Global.HausdorffMeasureCountableLocalization
import Poincare.Global.HausdorffMeasureScalarLimitSqueeze
import Poincare.Global.HausdorffInverseChartGlobalEpsilonSqueeze
import Poincare.Global.HausdorffInverseChartAreaFormula
import Poincare.Global.HausdorffFiniteAtlasChartFrameReduction
import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.HausdorffScalarVarianceContinuity
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarVariationJointContinuityReduction
import Poincare.Global.HausdorffScalarDensityDomination
import Poincare.Global.VolumeMeasure
import Poincare.Global.VolumeFiniteness
import Poincare.Global.GeodesicSpeed
import Poincare.Global.VolumeFinitenessComparison
import Poincare.Global.ScalarIntegral
import Poincare.Global.ScalarMeanLowerBound
import Poincare.Global.NormalizedFlow
import Poincare.Global.NormalizedFlowRescaling
import Poincare.Global.GaussLemmaRadial
import Poincare.Global.GaussLemmaTransverse
import Poincare.Global.GeodesicDependence
import Poincare.Global.GeodesicLinearized
import Poincare.Global.GeodesicDerivative
import Poincare.Global.GeodesicDerivativeFinal
import Poincare.Global.GeodesicFlowDerivative
import Poincare.Global.GaussLemmaIntegrated
import Poincare.Global.ExponentialDerivativeZero
import Poincare.Global.ExponentialFrechet
import Poincare.Global.ExponentialLocalHomeo
import Poincare.Global.GeodesicDistance
import Poincare.Global.GeodesicPathLength
import Poincare.Global.GeodesicLength
import Poincare.Global.GeodesicLengthFinal
import Poincare.Global.GeodesicDistanceLower
import Poincare.Global.AntilipschitzBall
import Poincare.Global.AntilipschitzBallFinal
import Poincare.Global.AntilipschitzClose
import Poincare.Global.AntilipschitzMathlib
import Poincare.Global.NormalizedFlowStationaryLimit
import Poincare.Global.NormalizedFlowConvergenceEndpoint
import Poincare.Global.NormalizedFlowPointwiseConvergence
import Poincare.Global.NormalizedFlowVolumeVariation
import Poincare.Global.VolumeMeasureOpenPositivity
import Poincare.Global.RicciEnergyRegularity
import Poincare.Global.NormalizedFlowScalarIntegralVariation
import Poincare.Global.NormalizedFlowStokesBoundaryReduction
import Poincare.Global.NormalizedFlowEnergyCriticality
import Poincare.Global.NormalizedFlowFiniteDissipationLimit
import Poincare.Global.NormalizedFlowAbsoluteDissipation
import Poincare.Global.NormalizedFlowEnergyConcentration
import Poincare.Global.ClosedRiemannianBallVolumeLower
import Poincare.Global.ClosedRiemannianDistanceComparison
import Poincare.Global.NormalizedFlowEnergyConcentrationLipschitzBridge
import Poincare.Global.NormalizedFlowEnergyConcentrationCurvatureDerivative
import Poincare.Global.NormalizedFlowEnergyConcentrationSequentialCompactness
import Poincare.Global.NormalizedFlowFiniteTimePositiveRicci
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeCurvatureCompactness
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinstein
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarJointContinuity
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradient
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarGradientSphere
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarSphere
import Poincare.Global.NormalizedFlowMeanScalarTopologicalSphereBridge
import Poincare.Global.NormalizedFlowMeanScalarCanonicalRootedSphereBridge
import Poincare.Global.NormalizedFlowMeanScalarSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinScalarProfile
import Poincare.Global.NormalizedFlowTopologicalSphereBridge
import Poincare.Global.NormalizedFlowForwardAbsoluteDissipation
import Poincare.Global.NormalizedFlowForwardFiniteDissipationReduction
import Poincare.Global.ForwardTailIntegrability
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalar
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarGradient
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergy
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint
import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyClosedInvariantRangeEndpoint
import Poincare.Global.NormalizedFlowForwardTracelessEnergyDecay
import Poincare.Global.NormalizedFlowForwardTracelessEnergyDifferentialDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyMaximumDifferentialDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyReactionDecay
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.DifferentialSuccessorEqualityStabilityReduction
import Poincare.Global.DifferentialSuccessorCoordinateRigidityReduction
import Poincare.Global.DifferentialSuccessorCoordinateRigidityWitnessIndependence
import Poincare.Global.NormalizedFlowCompactMeanEnergySelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity
import Poincare.Global.NormalizedFlowCompactScalarVarianceContinuity
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureComparedUniformRadiusSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasurePointwiseDecayComparedUniformRadiusSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureParabolicDecayDirectUniformSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureQuantitativeNearRoundTail
import Poincare.Global.NormalizedFlowQuantitativeNearRoundTailFromDecay
import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTimePositiveEinstein
import Poincare.Global.NormalizedFlowFiniteDissipationCoerciveGap
import Poincare.Global.NormalizedFlowCompactFiniteDissipationBoundedVariation
import Poincare.Global.NormalizedFlowCompactFixedTargetCoerciveGapPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetEventualCoerciveGapPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetFiniteTracelessEnergyPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinstein
import Poincare.Global.NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein
import Poincare.Global.NormalizedFlowFormalProfilePositiveEinstein
import Poincare.Global.PoincareFiniteSmoothingFiniteTimeEinsteinDirectGenericBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayDirectUniformBoundary
import Poincare.Global.PoincareFiniteSmoothingFiniteTracelessEnergyPointwiseCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayPositiveEinsteinPointwiseCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffPositiveEinsteinPointwiseCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinPointwiseCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareFiniteSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareFiniteTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundary
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundary
import Poincare.Global.PoincareAutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundary
import Poincare.Global.NormalizedFlowClosedMeanEnergyRangeComparedUniformRadiusSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowClosedMeanEnergyRangePointwiseDecayComparedUniformRadiusSelectedSmoothAtlasPoincare
import Poincare.Global.NormalizedFlowMeanScalarLimit
import Poincare.Global.NormalizedFlowHausdorffDissipationEndpoint
import Poincare.Global.NormalizedFlowLowerSemicontinuousCompactness
import Poincare.Global.NormalizedFlowAbsoluteDissipationDecay
import Poincare.Global.NormalizedFlowHausdorffLichnerowiczEndpoint
import Poincare.Global.NormalizedFlowScalarRegularity
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.NormalizedFlowScalarVarianceConcentration
import Poincare.Global.NormalizedFlowHausdorffClosedRangeEndpoint
import Poincare.Global.NormalizedFlowHausdorffSpatialMixedRegularity
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowHausdorffAutomaticStokes
import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
import Poincare.Global.NormalizedFlowInvariantCompactness
import Poincare.Global.NormalizedFlowInvariantRangeClosure
import Poincare.Global.NormalizedFlowDissipationDifferentialDecay
import Poincare.Global.NormalizedFlowFullyAssembledEnergyEndpoint
import Poincare.Global.NormalizedFlowFiniteAtlasAutomaticAreaEndpoint
import Poincare.Global.NormalizedFlowPartitionFullyAssembledEnergyEndpoint
import Poincare.Global.NormalizedFlowPartitionCompactOrbitEndpoint
import Poincare.Global.NormalizedFlowChartFramePartitionCompactOrbitEndpoint
import Poincare.Global.NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint
import Poincare.Global.ForwardRescalingChartFramePartitionEndToEnd
import Poincare.Global.ProofBearingEndToEndCompletion
import Poincare.Global.CartanAtlasTargetCoherence
import Poincare.Global.CartanAtlasAutomaticAnchorAlignment
import Poincare.Global.ProofBearingEndToEndCanonicalTransport
import Poincare.Global.ProofBearingPartitionEndToEndCompletion
import Poincare.Global.UniformNormalRadius
import Poincare.Global.CartanMap
import Poincare.Global.TangentAlignmentExists
import Poincare.Global.TangentAlignmentFiberCompactness
import Poincare.Global.RoundSphereTargetAnchorUniformity
import Poincare.Global.TangentAlignmentUniformCutoffRadius
import Poincare.Global.RoundSphereCanonicalExponential
import Poincare.Global.RoundSphereGenericExponentialAnchorIndependence
import Poincare.Global.JacobiConstantCurvature
import Poincare.Global.JacobiInstantiate
import Poincare.Global.ChartCurvatureBridgeZone
import Poincare.Global.ChartCurvatureBridgeZoneClose
import Poincare.Global.JacobiOscillator
import Poincare.Global.CartanIsometry
import Poincare.Global.CartanPullback
import Poincare.Global.CartanDifferential
import Poincare.Global.CartanLocalIsometry
import Poincare.Global.CartanIsometryFinal
import Poincare.Global.CartanExpansionBridge
import Poincare.Global.CartanSourceExpansion
import Poincare.Global.CartanPunctured
import Poincare.Global.CartanSourceFinal
import Poincare.Global.SmoothDependenceDischarge
import Poincare.Global.CartanAssembly
import Poincare.Global.CoefficientEvolution
import Poincare.Global.CartanSourceOwned
import Poincare.Global.CartanNormalCoords
import Poincare.Global.JacobiNormSystem
import Poincare.Global.JacobiNormClose
import Poincare.Global.JacobiIntegrated
import Poincare.Global.CartanIsometryTheorem
import Poincare.Global.CartanIsometryPackage
import Poincare.Global.CartanCoefficientBridge
import Poincare.Global.CartanBlocksInstantiate
import Poincare.Global.CartanDomainShrink
import Poincare.Global.CartanHomogeneity
import Poincare.Global.CartanBlocksFinal
import Poincare.Global.CartanScaleGeneric
import Poincare.Global.LinearizedCLM
import Poincare.Global.ExponentialStrictAtV
import Poincare.Global.ExponentialStrictClose
import Poincare.Global.CartanIsometryClose
import Poincare.Global.CartanActionEquations
import Poincare.Global.LinearizedFamilyExport
import Poincare.Global.LinearizedRescale
import Poincare.Global.LinearizedAdditivity
import Poincare.Global.CartanCascade
import Poincare.Global.CartanEquivUpgrade
import Poincare.Global.CartanFinalComposition
import Poincare.Global.CartanEndpointUnique
import Poincare.Global.CartanIsometryDone
import Poincare.Global.HarmonicHosted
import Poincare.Global.AccelerationIdentity
import Poincare.Global.CartanTheIsometry
import Poincare.Global.ChristoffelCollapse
import Poincare.Global.CollapseOnRay
import Poincare.Global.PositionRoute
import Poincare.Global.PositionBridge
import Poincare.Global.PairingRoute
import Poincare.Global.PairingFeed
import Poincare.Global.EqualityChain
import Poincare.Global.CascadePinned
import Poincare.Global.TargetPackage
import Poincare.Global.UnscaledFeed
import Poincare.Global.SourcePackage
import Poincare.Global.IsometryInstantiate
import Poincare.Global.SpeedPackage
import Poincare.Global.NormalizedHosting
import Poincare.Global.SpeedGeneric
import Poincare.Global.TheLocalIsometry
import Poincare.Global.OrthogonalityFeed
import Poincare.Global.DecomposedAssembly
import Poincare.Global.BlocksDischarge
import Poincare.Global.RadialBlock
import Poincare.Global.CorrectedRadial
import Poincare.Global.RayIdentification
import Poincare.Global.IsometryFinal
import Poincare.Global.SpeedReconcile
import Poincare.Global.CombinedFeed
import Poincare.Global.HostedPayload
import Poincare.Global.OneSidedPayload
import Poincare.Global.BundleDischarge
import Poincare.Global.PLNormFeed
import Poincare.Global.UniformPL
import Poincare.Global.BoundedPackage
import Poincare.Global.TheIsometry
import Poincare.Global.SolutionsFeed
import Poincare.Global.IsometryAssembly
import Poincare.Global.EnrichedCascade
import Poincare.Global.IsometryComplete
import Poincare.Global.MembershipBound
import Poincare.Global.GronwallMembership
import Poincare.Global.AssemblyDone
import Poincare.Global.CommonTime
import Poincare.Global.MasterBundle
import Poincare.Global.PLPackages
import Poincare.Global.IntervalAlign
import Poincare.Global.SmallTCommon
import Poincare.Global.UniformShrink
import Poincare.Global.UniformFlowExport
import Poincare.Global.LocalIsometryTheorem
import Poincare.Global.PairingUpgrade
import Poincare.Global.PullbackFeed
import Poincare.Global.ScalarPin
import Poincare.Global.ScaledUpgrade
import Poincare.Global.SinSqInstantiate
import Poincare.Global.BlockDiagonal
import Poincare.Global.TransverseExport
import Poincare.Global.RadiusTuple
import Poincare.Global.CoefficientShrink
import Poincare.Global.ThreeBounds
import Poincare.Global.FinalSelector
import Poincare.Global.AopBound
import Poincare.Global.RigidityComplete
import Poincare.Global.UniformTangentAlignmentRigidity
import Poincare.Global.UniformTangentAlignmentDifferentialField
import Poincare.Global.UniformTangentAlignmentFTransition
import Poincare.Global.UniformTangentAlignmentC2
import Poincare.Global.RoundSphereCanonicalExponentialC2
import Poincare.Global.UniformTangentAlignmentGeodesicTransition
import Poincare.Global.UniformTangentAlignmentGeodesicTransitionFiniteFamily
import Poincare.Global.UniformTangentAlignmentFiniteFamily
import Poincare.Global.IsometryConsumers
import Poincare.Global.GermDeterminacy
import Poincare.Global.InducedAlignment
import Poincare.Global.ExpNaturality
import Poincare.Global.GeodesicPreservation
import Poincare.Global.OffAnchorNaturality
import Poincare.Global.ReanchorLawFinal
import Poincare.Global.ChristoffelTransition
import Poincare.Global.KoszulNaturality
import Poincare.Global.TransitionLaw
import Poincare.Global.TransportedCompatibility
import Poincare.Global.DifferentiatedCompat
import Poincare.Global.PullbackDifferentiate
import Poincare.Global.HdiffInstantiate
import Poincare.Global.TransitionLawFires
import Poincare.Global.SideConditions
import Poincare.Global.ChainRuleInput
import Poincare.Global.NaturalityCascade
import Poincare.Global.RaysToBall
import Poincare.Global.RayCoverInputs
import Poincare.Global.TwoBridges
import Poincare.Global.TargetRayIdentity
import Poincare.Global.LCNaturality
import Poincare.Global.DifferentialField
import Poincare.Global.FTransition
import Poincare.Global.GermAndField
import Poincare.Global.SecondVariation
import Poincare.Global.SecondFlowDerivative
import Poincare.Global.SecondDischarge
import Poincare.Global.SecondFrechet
import Poincare.Global.DFrechetUpgrade
import Poincare.Global.ConcreteResidual
import Poincare.Global.DerivativeUnique
import Poincare.Global.ResidualExport
import Poincare.Global.CongruenceStep
import Poincare.Global.FTransitionDone
import Poincare.Global.EndpointBridge
import Poincare.Global.ContDiffTwo
import Poincare.Global.ExpChartC2
import Poincare.Global.AugmentedC1
import Poincare.Global.AugmentedDependence
import Poincare.Global.AugmentedPackage
import Poincare.Global.PackageLands
import Poincare.Global.FieldProducer
import Poincare.Global.FlowSmoothness
import Poincare.Global.ThirdVariation
import Poincare.Global.FieldC1
import Poincare.Global.TowerCloses
import Poincare.Global.LevelThreeFeed
import Poincare.Global.CanonicalC1
import Poincare.Global.DoublyResidual
import Poincare.Global.TowerClosed
import Poincare.Global.ThirdFamily
import Poincare.Global.EndpointContinuity
import Poincare.Global.OmegaGronwall
import Poincare.Global.TransitionLands
import Poincare.Global.HostedCLM
import Poincare.Global.ContinuityPackages
import Poincare.Global.IndexedSelection
import Poincare.Global.TheSelector
import Poincare.Global.TwoConnectors
import Poincare.Global.OmegaRescale
import Poincare.Global.CenteredMembership
import Poincare.Global.SelectorAssembly
import Poincare.Global.AnchoredEndpointIdentity
import Poincare.Global.EndpointCurry
import Poincare.Global.LinearEndpointGronwall
import Poincare.Global.UniformFirstVariationGronwall
import Poincare.Global.BasisEndpointAssembly
import Poincare.Global.AnchoredSecondDerivativeAssembly
import Poincare.Global.ProjectedAugmentedEndpoint
import Poincare.Global.ParameterizedFlowDerivative
import Poincare.Global.PrescribedLinearODE
import Poincare.Global.AnchoredRestrictedSecondDerivativeAssembly
import Poincare.Global.UniformAnchoredAugmentedFamily
import Poincare.Global.SecondVariationRescale
import Poincare.Global.SecondVariationEndpointGronwall
import Poincare.Global.UniformAnchoredSecondVariation
import Poincare.Global.UniformAnchoredFTransition
import Poincare.Global.UniformAnchoredGeodesicTransition
import Poincare.Global.CartanWeightInvariant
import Poincare.Global.CoveringSkeleton
import Poincare.Global.CartanContinuation
import Poincare.Global.CartanChain
import Poincare.Global.GeodesicReanchorClose
import Poincare.Global.ExponentialRayLawFull
import Poincare.Global.ChartCurvatureBridge
import Poincare.Global.ChartCurvatureBridge2
import Poincare.Global.ChartCurvatureBridge3
import Poincare.Global.ChartCurvatureBridge4
import Poincare.Global.ChartCurvatureBridge5
import Poincare.Global.ChartCurvatureBridge6
import Poincare.Global.RoundSphereWitness
import Poincare.Global.UnitRecognitionNext
import Poincare.Global.CartanOverlapCompatibility
import Poincare.Global.CartanRestrictedOverlapCompatibility
import Poincare.Global.CartanOverlapContinuation
import Poincare.Global.CartanLocalRigidity
import Poincare.Global.CartanAdjacentContinuation
import Poincare.Global.CartanChainRigidity
import Poincare.Global.DifferentialInducedSuccessor
import Poincare.Global.DifferentialSuccessorNaturality
import Poincare.Global.DifferentialSuccessorNaturalityFiniteFamily
import Poincare.Global.DifferentialSuccessorZero
import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.DifferentialSuccessorIntervalNaturalityFiniteFamily
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.DifferentialSuccessorReachableChainRefinement
import Poincare.Global.DifferentialSuccessorFiniteSubdivisionRefinement
import Poincare.Global.DifferentialSuccessorFiniteInsertionRefinement
import Poincare.Global.DifferentialSuccessorStrictFactorInsertionTransport
import Poincare.Global.DifferentialSuccessorStrictFactorCurvatureTransport
import Poincare.Global.DifferentialSuccessorAdaptiveGridRefinement
import Poincare.Global.DifferentialSuccessorAdaptiveFeedbackIteration
import Poincare.Global.DifferentialHomotopyGridFiniteMaximaRefinement
import Poincare.Global.CartanCanonicalRootedAdaptiveGenericBridgeRecognition
import Poincare.Global.CartanAtlasRealizedEndpointTransport
import Poincare.Global.CartanAtlasRootedReachableEndpointTransport
import Poincare.Global.CartanAtlasRootedAdaptiveClosenessTransport
import Poincare.Global.CartanAtlasRootedPathSkeleton
import Poincare.Global.CartanAtlasRootedPathAdaptiveMeshRealization
import Poincare.Global.CartanAtlasRootedPathCurvatureSuccessorRadius
import Poincare.Global.CartanTargetExponentialFamily
import Poincare.Global.CartanCanonicalFamilyLocalDataTransfer
import Poincare.Global.CartanSourceExponentialFamily
import Poincare.Global.CartanSourceExponentialLocalChartSelector
import Poincare.Global.CartanSourceExponentialLocalChartStationary
import Poincare.Global.CartanSourceExponentialLocalChartInverse
import Poincare.Global.CartanSourceExponentialLocalFamilyTransport
import Poincare.Global.CartanSourceExponentialLocalFamilyTransitionAgreement
import Poincare.Global.CartanCanonicalFamilyLocalUniformData
import Poincare.Global.CartanCanonicalFamilyTransitionAgreementAssembly
import Poincare.Global.CartanCanonicalFamilyGermComparison
import Poincare.Global.CartanCanonicalRootedRealizationTransfer
import Poincare.Global.CartanCanonicalFamilySuccessorProvenance
import Poincare.Global.CartanCanonicalFamilyProvenanceLocalUniformData
import Poincare.Global.CartanCanonicalFamilyProvenanceRootedAssembly
import Poincare.Global.CartanCanonicalRootedEndpointAssembly
import Poincare.Global.CartanCanonicalRootedRestrictedEndpointAssembly
import Poincare.Global.CartanRootedOverlapHomotopyGrid
import Poincare.Global.CartanCanonicalRootedHomotopyGridEndpointAssembly
import Poincare.Global.CartanTerminalShortPathScheduleFree
import Poincare.Global.CartanTerminalShortPathDiameter
import Poincare.Global.CartanRootedOverlapDirectBoundarySubdivision
import Poincare.Global.CartanCanonicalRootedDerivedTerminalHomotopyGridAssembly
import Poincare.Global.FiniteUnitIntervalInterpolation
import Poincare.Global.CartanRootedOverlapReparameterizedBoundary
import Poincare.Global.CartanRootedOverlapReparameterizedBoundaryState
import Poincare.Global.CartanRootedOverlapReparameterizedHomotopyGrid
import Poincare.Global.CartanCanonicalRootedReparameterizedDerivedTerminalHomotopyGridAssembly
import Poincare.Global.CartanRootedOverlapReparameterizedGridRealization
import Poincare.Global.CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
import Poincare.Global.CartanCanonicalFamilyComparedToGenericSuccessorRadius
import Poincare.Global.CartanCanonicalFamilyComparedNeighborhood
import Poincare.Global.CartanCanonicalFamilyComparedForwardNormalRegularity
import Poincare.Global.CartanCanonicalFamilyComparedLocallyUniformRadiusEnvelope
import Poincare.Global.CartanCanonicalFamilyComparedCanonicalContinuation
import Poincare.Global.CartanCanonicalFamilyLocalSourceDataCover
import Poincare.Global.CartanCanonicalFamilyComparedWholeCellRealization
import Poincare.Global.CartanCanonicalRootedUniformSuccessorMeshRecognition
import Poincare.Global.DifferentialSuccessorAdaptiveHomotopyGrid
import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates
import Poincare.Global.DifferentialUniformSuccessorMesh
import Poincare.Global.DifferentialSuccessorJointEqualityNeighborhood
import Poincare.Global.DifferentialUniformSuccessorStrictFactorGeometry
import Poincare.Global.DifferentialUniformSuccessorPathStrictFactorGeometry
import Poincare.Global.CartanCanonicalJointNeighborhoodUniformMeshRecognition
import Poincare.Global.CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition
import Poincare.Global.CartanGenericSuccessorDataLocalCover
import Poincare.Global.CartanGenericSuccessorDataMovingPersistenceReduction
import Poincare.Global.CartanFixedChartTransitionAgreementSubordination
import Poincare.Global.CartanFixedChartTransitionAgreementContinuityReduction
import Poincare.Global.CartanFixedChartGenericInverseEndpointReduction
import Poincare.Global.CartanFixedChartGenericInverseEndpointODEComparison
import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPrimitive
import Poincare.Global.CartanFixedChartGenericInverseEndpointODEOverlapReduction
import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction
import Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction
import Poincare.Global.CartanPreferredBudgetLocusReduction
import Poincare.Global.CartanTwoNeighborhoodDevelopment
import Poincare.Global.CartanUniformMovingPreferredChartFlow
import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.RoundSphereGenericCanonicalAgreementLocusReduction
import Poincare.Global.CartanGenericRootedAdaptiveFiniteGridRecognition
import Poincare.Global.CartanFixedTargetMovingAdaptiveRecognitionBoundary
import Poincare.Global.CartanGenericPostRealizationCompactHistoryReduction
import Poincare.Global.CartanFixedTargetMovingPrimitiveProviderReduction
import Poincare.Global.CartanFixedTargetMovingPointwisePrimitiveProviderReduction
import Poincare.Global.CartanFixedTargetMovingContinuityEndpointPrimitiveProviderReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointPrimitiveProviderReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPrimitiveProviderReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODEPositiveTimeOverlapProviderReduction
import Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
import Poincare.Global.DifferentialSuccessorFiniteAnchorRadius
import Poincare.Global.DifferentialSuccessorFiniteRealizedHomotopyGrid
import Poincare.Global.DifferentialSuccessorFiniteRealizedGridCommonRadius
import Poincare.Global.DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization
import Poincare.Global.CartanRootedOverlapRefinedGridFiniteMaximaBridge
import Poincare.Global.CartanRootedOverlapRefinedInsertionCompactHistoryReduction
import Poincare.Global.DifferentialSuccessorPostRealizationMeshCertificate
import Poincare.Global.DifferentialSuccessorPostRealizationRefiningCandidate
import Poincare.Global.FTransitionGeodesicMap
import Poincare.Global.ChartTransitionGeodesicMap
import Poincare.Global.RoundSphereSimpleConnected
import Poincare.Global.TopologicalCompletionBridge
import Poincare.Global.SmoothabilityExistenceBridge
import Poincare.Global.SmoothabilityProofBearingAtlasUpgrade
import Poincare.Global.SmoothabilityFiniteTopologicalAtlasReduction
import Poincare.Global.SmoothabilityFinitePrecompactTopologicalAtlasReduction
import Poincare.Global.SmoothabilityFiniteAtlasNerveReduction
import Poincare.Global.SmoothabilityFiniteTransitionSmoothingBoundary
import Poincare.Global.SmoothabilityFiniteSmoothTransitionExtension
import Poincare.Global.SmoothabilityFiniteLocalAffineTransitionModels
import Poincare.Global.SmoothabilityLocalSmoothTransitionGerms
import Poincare.Global.SmoothabilitySimultaneousLocalConjugacy
import Poincare.Global.SmoothabilityPLCompatibleAffineConjugacy
import Poincare.Global.SmoothabilityRawAffineNerveIdentityConjugacy
import Poincare.Global.SmoothabilityAffineGermInvertibilityReduction
import Poincare.Global.SmoothabilityFiniteTetrahedralStarReduction
import Poincare.Global.ConstantCurvatureEinstein
import Poincare.Global.ShortTimeInterface
import Poincare.Global.HeatKernel
import Poincare.Global.HeatKernelPDE
import Poincare.Global.HeatKernelPDEn
import Poincare.Global.HeatKernelIntegral
import Poincare.Global.HeatApproxIdentity
import Poincare.Global.HeatCauchy
import Poincare.Global.HeatCauchyClose
import Poincare.Global.HeatEnvelopes
import Poincare.Global.HeatCauchyFinal
import Poincare.Global.HeatCauchyTheorem
import Poincare.Global.HeatCauchyDirectional
import Poincare.Global.HeatCauchyFrechet
import Poincare.Global.HeatCauchyUniform
import Poincare.Global.HeatCauchyNext2
import Poincare.Global.VectorHeatCauchy
import Poincare.Global.DuhamelContraction
import Poincare.Global.DuhamelLocalContraction
import Poincare.Global.QuadraticNonlinearity
import Poincare.Global.PointwiseBUCBilinear
import Poincare.Global.HeatSemigroupOperator
import Poincare.Global.HeatKernelSemigroup
import Poincare.Global.HeatRegularizedPicard
import Poincare.Global.BoundedUniformContinuousHeat
import Poincare.Global.HeatSemigroupBUCStrongContinuity
import Poincare.Global.HamiltonFrontStatements
import Poincare.Global.HamiltonScalarNegativeBarrier
import Poincare.Global.HamiltonScalarInteriorNegativeBarrier
import Poincare.Global.HeatSemigroupBUCOperator
import Poincare.Global.HeatSemigroupBUCC0
import Poincare.Global.SemilinearHeatBUC
import Poincare.Global.SemilinearHeatBUCRegularity
import Poincare.Global.SemilinearHeatBUCFixedPointRegularity
import Poincare.Global.HeatSemigroupBUCGeneratorCore
import Poincare.Global.HeatSemigroupBUCGeneratorEvolution
import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Poincare.Global.HeatDuhamelBUCGeneratorDini
import Poincare.Global.HeatDuhamelBUCGeneratorHolderContinuity
import Poincare.Global.SemilinearHeatBUCHolderClassical
import Poincare.Global.HeatMildBUCPositiveHolder
import Poincare.Global.SemilinearHeatBUCAutomaticClassical
import Poincare.Global.SemilinearHeatBUCLocalAutomaticClassical
import Poincare.Global.SemilinearHeatBUCAutomaticContDiff
import Poincare.Global.HeatSemigroupPositiveContinuity
import Poincare.Global.HeatDuhamelPicard
import Poincare.Global.HeatDuhamelBUCPicard
import Poincare.Global.HeatDuhamelBUCIntrinsic
import Poincare.Global.QuadraticHeatDuhamel
import Poincare.Global.QuadraticHeatLocalExistence
import Poincare.Global.QuadraticSemilinearHeatBUC
import Poincare.Global.PointwiseQuadraticSemilinearHeatBUC
import Poincare.Global.QuadraticSemilinearHeatBUCUniform
import Poincare.Global.SemilinearHeatBUCRestart
import Poincare.Global.SemilinearHeatBUCRestrictionGluing
import Poincare.Global.QuadraticSemilinearHeatBUCContinuation
import Poincare.Global.QuadraticSemilinearHeatBUCMaximal
import Poincare.Global.PointwiseQuadraticSemilinearHeatBUCMaximal
import Poincare.Global.SemilinearHeatBUCLocalUniform
import Poincare.Global.SemilinearHeatBUCLocalContinuation
import Poincare.Global.SemilinearHeatBUCLocalMaximal
import Poincare.Global.SemilinearHeatBUCLocalDataOperations
import Poincare.Global.SemilinearHeatBUCPolynomialLocalData
import Poincare.Global.RecenteredDeTurckSemilinearHeatBUC
import Poincare.Global.AffineRecenteredDeTurckSemilinearHeatBUC
import Poincare.Global.AffineRecenteredDeTurckBUCAutomaticClassical
import Poincare.Global.AffineRecenteredDeTurckBUCClassicalCoreAutomatic
import Poincare.Global.DeTurckBUCMetricReconstruction
import Poincare.Global.SemilinearHeatBUCInteriorRegularity
import Poincare.Global.SemilinearHeatBUCTwoSidedInteriorRegularity
import Poincare.Global.DeTurck
import Poincare.Global.DeTurckField
import Poincare.Global.DeTurckFieldRegularity
import Poincare.Global.DeTurckSummandRegularity
import Poincare.Global.DeTurckLocalFrameRegularity
import Poincare.Global.DeTurckGaugedFlowClosure
import Poincare.Global.DeTurckGaugePullbackDerivative
import Poincare.Global.DeTurckInverseGaugeODE
import Poincare.Global.DeTurckFlowVariationalIdentification
import Poincare.Global.DeTurckFlowSymmetricVariationalIdentification
import Poincare.Global.DeTurckFlowSymmetricPhysicalTime
import Poincare.Global.DeTurckFlowSymmetricPhysicalEndpoint
import Poincare.Global.RicciTraceConjugacy
import Poincare.Global.ConnectionCurvatureNaturality
import Poincare.Global.DeTurckRicciTracePullback
import Poincare.Global.DeTurckChartOverlapCovariance
import Poincare.Global.DeTurckFlowSpatialEndpointGerm
import Poincare.Global.DeTurckChartIndependentPullback
import Poincare.Global.DeTurckBUCChartCovariance
import Poincare.Global.DeTurckBUCCoefficientIdentification
import Poincare.Global.DeTurckBUCGeneratorLaplacian
import Poincare.Global.HeatLaplacianZeroTime
import Poincare.Global.HeatGeneratorLocality
import Poincare.Global.DeTurckBUCGeneratorLocality
import Poincare.Global.DeTurckBUCClassicalCoreIdentification
import Poincare.Global.MovingBUCEvaluation
import Poincare.Global.DeTurckBUCMovingEvaluation
import Poincare.Global.DeTurckCoordinateJointRegularity
import Poincare.Global.DeTurckCoordinateJointRegularityThree
import Poincare.Global.DeTurckCoordinateJointRegularityFour
import Poincare.Global.DeTurckCoordinateJointRegularityOverlap
import Poincare.Global.DeTurckBUCInverseGaugeEvolution
import Poincare.Global.DeTurckBUCReconstructedPathInteriorRegularity
import Poincare.Global.DeTurckBUCInteriorCoefficientIdentification
import Poincare.Global.DeTurckBUCInteriorInverseGaugeEvolution
import Poincare.Global.DeTurckBUCInteriorGlobalRicciData
import Poincare.Global.DeTurckBUCInteriorTimeGermAssembly
import Poincare.Global.DeTurckBUCJointSpacetimeGermRestriction
import Poincare.Global.DeTurckBUCJointSpacetimeMetricAssembly
import Poincare.Global.DeTurckBUCJointSpacetimeChartCovariance
import Poincare.Global.DeTurckBUCUniformSolutionEquivariance
import Poincare.Global.DeTurckBUCOverlapParabolicUniqueness
import Poincare.Global.DeTurckBUCQuasilinearDifferenceEnergy
import Poincare.Global.DeTurckBUCFlatHilbertSchmidtEnergy
import Poincare.Global.DeTurckBUCFlatHSEnergyUniqueness
import Poincare.Global.DeTurckBUCJointSpacetimeRealizationGerm
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowInteriorAssembly
import Poincare.Global.DeTurckBUCCurvatureRateLocality
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowCurvatureAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowMetricPullbackAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowChartMetricRegularityAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowChristoffelRegularityAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowSpatialC3Assembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowTimeVariationalAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowLocalInverseAssembly
import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowTwoRestartAssembly
import Poincare.Global.PicardLindelofControlledContinuousSelector
import Poincare.Global.DeTurckBUCTwoRestartPointFlowCore
import Poincare.Global.NonautonomousTwoRestartPointFlowCore
import Poincare.Global.DeTurckBUCSpatialVariationalTwoRestartPackage
import Poincare.Global.DeTurckBUCNonautonomousSpatialVariationalHierarchy
import Poincare.Global.DeTurckBUCRegularSelectorTwoRestartPointFlowCore
import Poincare.Global.DeTurckBUCPointFlowSelectorSmoothDependence
import Poincare.Global.DeTurckBUCPointFlowVariationalSmoothDependence
import Poincare.Global.DeTurckPointFlowVariationalFields
import Poincare.Global.DeTurckPointFlowMetricVariationalFields
import Poincare.Global.DeTurckPointFlowMetricTwoRestartPackage
import Poincare.Global.DeTurckBUCReconstructedMetricJointFiveBoundary
import Poincare.Global.PointFlowVariationalSelectorTower
import Poincare.Global.InverseGaugePointVariationalSelectorTower
import Poincare.Global.PointFlowCoherentVariationalSelectorTower
import Poincare.Global.LocalUniformTaylorRemainder
import Poincare.Global.ParameterizedFlowDerivativeNestedBalls
import Poincare.Global.PicardLindelofRegularControlledSelector
import Poincare.Global.PicardLindelofRegularSelectorProjection
import Poincare.Global.PointFlowRegularCoherentVariationalSelectorTower
import Poincare.Global.RegularVariationalSelectorEndpointDerivative
import Poincare.Global.PicardLindelofRegularSelectorTimeReversal
import Poincare.Global.RegularVariationalSelectorSymmetricEndpointDerivative
import Poincare.Global.RegularVariationalSelectorJointC1
import Poincare.Global.RegularVariationalSelectorJointC3
import Poincare.Global.PointFlowVariationalExtractionIdentities
import Poincare.Global.RegularCoherentVariationalEndpointTower
import Poincare.Global.RegularCoherentVariationalTwoRestartBridge
import Poincare.Global.RegularCoherentVariationalTwoRestartPackage
import Poincare.Global.PointFlowVariationalEndpointTower
import Poincare.Global.DeTurckBUCSymmetricPointFlowGermAssembly
import Poincare.Global.DeTurckBUCInteriorRicciAssembly
import Poincare.Global.DeTurckBUCInteriorHamiltonAssembly
import Poincare.Global.DeTurckBUCScalarEvolutionBridge
import Poincare.Global.DeTurckBUCScalarEvolutionJointMetricEntries
import Poincare.Global.CoordinateRicciFlowHamiltonScalarBridge
import Poincare.Global.ConformalChristoffel
import Poincare.Global.MetricRescale
import Poincare.Global.MetricRescaleCurvature
import Poincare.Global.MetricRescaleFiniteAtlasIntegrals
import Poincare.Global.MetricRescaleFiniteAtlasForwardFlow
import Poincare.Global.FiniteExtinctionIntegratingFactor
import Poincare.Global.FiniteExtinctionInitialScale
import Poincare.Global.FiniteExtinctionSurgerySchedule
import Poincare.Global.ThreeDimensionalRicciTraceInequality
import Poincare.Global.ScalarCurvatureBarrier
import Poincare.Global.FiniteExtinctionScalarWidth
import Poincare.Global.FiniteExtinctionGeometricScalarWidth
import Poincare.Global.FiniteExtinctionGeometricScalarWidthInterior
import Poincare.Global.FiniteExtinctionGeometricScalarWidthInteriorContinuousOn
import Poincare.Global.FiniteExtinctionRicciFlowScalarEvolutionInterior
import Poincare.Global.FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn
import Poincare.Global.FiniteExtinctionRicciFlowJointMetricEntries
import Poincare.Global.FiniteExtinctionPerelmanWidth
import Poincare.Global.RoundSphereMetric
import Poincare.Global.RoundSphereChart
import Poincare.Global.RoundSphereChartMetric
import Poincare.Global.EinsteinInterface
import Poincare.Milestones
import Poincare.Assembly
import Poincare.CanonicalBridges
import Poincare.RicciFlowInterface
import Poincare.RicciFlow
import Poincare.AnalyticFoundation
import Poincare.Surgery
import Poincare.Smoothability
import Poincare.TopologyExtraction
import Poincare.ProofProgress.OnePointSingleComplementTopology
import Poincare.ProofProgress.OnePointTwoPointComplementTopology
import Poincare.ProofProgress.OnePointThreeSphereTwoPoint
import Poincare.ProofProgress.ThreeSphereTwoPointPiOne
import Poincare.ProofProgress.SmoothabilityOnePointRecognition
import Poincare.ProofProgress.MoiseSmoothabilityTarget
import Poincare.ProofProgress.MoiseSmoothabilityAfterTopologyExtraction
import Poincare.ProofProgress.SmoothabilityProductionPackageBlocker
import Poincare.ProofProgress.SmoothabilityProductionPackageBridge
import Poincare.ProofProgress.SmoothabilityProductionPackageMoiseLocalBlocker
import Poincare.ProofProgress.AnalyticThreeManifoldStationary
import Poincare.ProofProgress.SurgeryPerelmanPackageLayer
import Poincare.ProofProgress.SingularityModelBlowupCoverage
import Poincare.ProofProgress.GroundedPerelmanSingularityControl
import Poincare.ProofProgress.ExtinctionSurgeryTraceAncestry
import Poincare.ProofProgress.FiniteExtinctionPackage
import Poincare.ProofProgress.TopologyExtractionPunctureTransport
import Poincare.ProofProgress.AnalyticLeviCivitaBlocker
import Poincare.ProofProgress.AnalyticProductionPackageLeviCivita
import Poincare.ProofProgress.AnalyticLeviCivitaInterface
import Poincare.ProofProgress.FiniteExtinctionSweepoutBoundary
import Poincare.ProofProgress.FiniteExtinctionSweepoutInterfaceBundle
import Poincare.ProofProgress.FiniteExtinctionProductionPackageBridge
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterWidth
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterCurvature
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolume
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterSurgeryVolume
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterScalarCurvature
import Poincare.ProofProgress.FiniteExtinctionProductionPackageAfterVolumeDifferential
import Poincare.ProofProgress.GroundedFiniteExtinctionCertificate
import Poincare.ProofProgress.GroundedPerelmanFiniteExtinctionBridge
import Poincare.ProofProgress.TopologyPackageFields
import Poincare.ProofProgress.TopologyDecompositionInterface
import Poincare.ProofProgress.TopologyProductionPackageNextField
import Poincare.ProofProgress.ExtinctionThreeSphereCoveringProjection
import Poincare.ProofProgress.GroundedPerelmanPoincareBoundary
import Poincare.ProofProgress.GroundedTopologyStatements
import Poincare.ProofProgress.GroundedTopologyAssembly
import Poincare.ProofProgress.CompletionBlockerLedger
import Poincare.ProofProgress.FullAssemblyClosure
import Poincare.ProofProgress.FinalCertificateBoundary
import Poincare.ProofProgress.ResearcherStepLedger
import Poincare.ProofProgress.SemanticSurfaceContractBridge
import Poincare.FullAssembly
import Poincare.Dependencies
import Poincare.DependencyProjections
import Poincare.DependencyCrosswalk
import Poincare.CompletionTarget
```

</details>

<details>
<summary>run.py</summary>

```python
import subprocess, pathlib, sys, json, os
root=pathlib.Path('/private/tmp/near-frozen-evidence')
label=sys.argv[1]
args=sys.argv[2:]
if not args: args=['lake','env','lean','Poincare/Global/NearFrozenParabolicRightInverse.lean']
for arg in args:
 p=pathlib.Path(arg)
 if p.suffix=='.lean' and p.exists(): (root/(label+'_'+p.name)).write_bytes(p.read_bytes())
r=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env={**os.environ,'LEAN_NUM_THREADS':'1','DEVELOPER_DIR':'/Library/Developer/CommandLineTools'})
(root/(label+'.json')).write_text(json.dumps({'cmd':args,'exit_code':r.returncode,'output':r.stdout},ensure_ascii=False,indent=2))
print(r.stdout,end=''); print('EXIT_CODE='+str(r.returncode))
sys.exit(r.returncode)
```

</details>

<details>
<summary>check.py</summary>

```python
import pathlib, subprocess, sys, os
root=pathlib.Path('/private/tmp/near-frozen-evidence'); label=sys.argv[1]
src=pathlib.Path('Poincare/Global/NearFrozenParabolicRightInverse.lean')
probe=root/(label+'-audit.lean')
probe.write_text(src.read_text()+'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.NearFrozenParabolicRightInverse).isPrefixOf n then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_NAMESPACE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
''')
commands=[['lake','env','lean',str(probe)],['rg','-n',r'\b(sorry|admit|axiom|opaque)\b|native_decide',str(src)],['git','diff','--check']]
for i,c in enumerate(commands):
 r=subprocess.run(['python3',str(root/'run.py'),label+'-'+str(i)]+c)
 if r.returncode != (1 if i==1 else 0): sys.exit(r.returncode or 2)
```

</details>

<details>
<summary>name-grep.py</summary>

```python
import pathlib, subprocess, re, sys
root=pathlib.Path('/private/tmp/near-frozen-evidence')
names=[]
for p in ['dependencies.lean','mathlib-statements.lean']:
 names += re.findall(r'^#print (\S+)',(root/p).read_text(),re.M)
names += ['Poincare.NearFrozenParabolicRightInverse.'+n for n in re.findall(r'^(?:def|theorem) (\w+)',pathlib.Path('Poincare/Global/NearFrozenParabolicRightInverse.lean').read_text(),re.M)]
base=list(dict.fromkeys(n.rsplit('.',1)[-1] for n in names))
pattern=r'\b(?:'+ '|'.join(re.escape(n) for n in base)+r')\b'
prefix=subprocess.check_output(['lean','--print-prefix'],text=True).strip()
cmd=['rg','-n',pattern,'Poincare/Global/FrozenEllipticHeatOperator.lean','Poincare/Global/NearIdentityParabolicRightInverse.lean','Poincare/Global/DuhamelSolutionOperatorCLM.lean','Poincare/Global/ParabolicHolderMultiplier.lean','Poincare/Global/ParabolicHolderSpace.lean','Poincare/Global/ParabolicSolutionGraph.lean','Poincare/Global/ParametrixNeumannCorrection.lean','Poincare/Global/NearFrozenParabolicRightInverse.lean','.lake/packages/mathlib/Mathlib',prefix+'/src/lean/Init',prefix+'/src/lean/Lean']
r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print('rg -n <all printed declaration basenames> <project context, Mathlib, Lean source>')
lines=r.stdout.splitlines()
for name in names:
 b=name.rsplit('.',1)[-1]
 hits=[line for line in lines if re.search(r'\b'+re.escape(b)+r'\b',line)]
 if not hits: print('MISSING '+name);sys.exit(1)
 decls=[line for line in hits if re.search(r'(?:theorem|lemma|def|abbrev)\s+(?:\w+\.)*'+re.escape(b)+r'\b',line)]
 print(name+': '+(decls or hits)[0])
print('VERIFIED_NAMES='+str(len(names)))
```

</details>

<details>
<summary>receipt.py</summary>

```python
import subprocess,os,hashlib,pathlib
cmds=[['git','status','--short','--branch'],['git','rev-parse','HEAD'],['git','worktree','list','--porcelain'],['lean','--version'],['git','-C','.lake/packages/mathlib','rev-parse','HEAD'],['git','-C','.lake/packages/mathlib','remote','get-url','origin']]
for cmd in cmds:
 r=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print('$ '+' '.join(cmd));print(r.stdout,end='');print('exit='+str(r.returncode))
 assert r.returncode==0
p=pathlib.Path('Poincare/Global/NearFrozenParabolicRightInverse.lean')
print('SOURCE_SHA256='+hashlib.sha256(p.read_bytes()).hexdigest())
```

</details>

## Final proof diff

```diff
diff --git a/Poincare/Global/NearFrozenParabolicRightInverse.lean b/Poincare/Global/NearFrozenParabolicRightInverse.lean
new file mode 100644
index 00000000..eba95635
--- /dev/null
+++ b/Poincare/Global/NearFrozenParabolicRightInverse.lean
@@ -0,0 +1,273 @@
+import Poincare.Global.FrozenEllipticHeatOperator
+import Poincare.Global.NearIdentityParabolicRightInverse
+
+noncomputable section
+
+set_option synthInstance.maxHeartbeats 200000
+set_option maxHeartbeats 800000
+set_option maxRecDepth 2000
+set_option backward.isDefEq.respectTransparency false
+
+namespace Poincare.NearFrozenParabolicRightInverse
+
+open Set ParabolicHolder ParabolicSolutionGraph FrozenEllipticHeatOperator
+open DuhamelSolutionOperatorCLM
+
+variable {α T : ℝ}
+
+/-- Spatial substitution on scalar forcing is a bounded linear map. -/
+def holderPullback (hα : 0 ≤ α) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
+    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ :=
+  ({ toFun := mapHolder hα S (ContinuousLinearMap.id ℝ ℝ)
+     map_add' := fun f g => by
+       apply ParabolicHolder.ext
+       intro p _
+       rfl
+     map_smul' := fun c f => by
+       apply ParabolicHolder.ext
+       intro p _
+       rfl } : Y («E» := (ClosedSmoothModel 3)) α T ℝ →ₗ[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ).mkContinuous
+    (max 1 (‖S‖ ^ α)) (norm_forcing_pullback_le hα S)
+
+/-- Pullback preserves the linear structure of genuine derivative graphs. -/
+def graphPullback (hα : 0 ≤ α) (hT : 0 < T) (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) :
+    Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
+  ({ toFun := mapGraph hα S
+     map_add' := fun G H => by
+       apply Graph.ext_of_u hT
+       apply ParabolicHolder.ext
+       intro p _
+       rfl
+     map_smul' := fun c G => by
+       apply Graph.ext_of_u hT
+       apply ParabolicHolder.ext
+       intro p _
+       rfl } : Graph («E» := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T).mkContinuous
+    (max 1 (‖S‖ ^ 2) * max 1 (‖S‖ ^ α)) (norm_mapGraph_le hα S)
+
+/-- The heat inverse conjugated by the symmetric elliptic factor. -/
+def frozenInverse (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3)) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) :
+    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
+  (graphPullback hα.le hT (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))).comp
+    ((duhamelOperator α T hα hα1 hT hT1).comp
+      (holderPullback hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))))
+
+/-- The conjugated inverse solves the frozen equation on the closed cylinder. -/
+theorem frozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
+    (hS : ∀ v w : (ClosedSmoothModel 3), inner ℝ (S v) w = inner ℝ v (S w))
+    (hA : ∀ v w : (ClosedSmoothModel 3), A v w = inner ℝ (S v) (S w))
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
+    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
+      (frozenInverse S hα hα1 hT hT1 f).ut (t, x) = f (t, x) +
+        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
+          (frozenInverse S hα hα1 hT hT1 f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
+  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
+  let H := duhamelOperator α T hα hα1 hT hT1 g
+  intro t ht x
+  have heq := duhamelOperator_solves α T hα hα1 hT hT1 g t ht (S.symm x)
+  change H.ut (t, S.symm x) = f (t, x) +
+    ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) *
+      H.ddu (t, S.symm x) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) (S.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
+  simp_rw [hA]
+  rw [trace_pullback S hS]
+  simpa only [g, mapHolder, ofFunction_apply, ContinuousLinearMap.id_apply,
+    ContinuousLinearEquiv.coe_coe, S.apply_symm_apply] using heq
+
+/-- The conjugated norm records only the heat bound and spatial distortions. -/
+theorem frozenInverse_norm_le (S : (ClosedSmoothModel 3) ≃L[ℝ] (ClosedSmoothModel 3))
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖frozenInverse S hα hα1 hT hT1‖ ≤
+      (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
+        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
+        boundConstant α hα hα1 * max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) := by
+  have hC := (boundConstant_spec α hα hα1).1
+  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+  intro f
+  let g := mapHolder hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) (ContinuousLinearMap.id ℝ ℝ) f
+  let H := duhamelOperator α T hα hα1 hT hT1 g
+  have hg := norm_forcing_pullback_le hα.le (S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) f
+  have hH : ‖H‖ ≤ boundConstant α hα hα1 * ‖g‖ :=
+    ((duhamelOperator α T hα hα1 hT hT1).le_opNorm g).trans
+      (mul_le_mul_of_nonneg_right
+        (NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant hα hα1 hT hT1)
+        (norm_nonneg g))
+  change ‖mapGraph hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H‖ ≤ _
+  apply (norm_mapGraph_le hα.le (S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3)) H).trans
+  calc
+    _ ≤ (max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) *
+        max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α)) *
+        (boundConstant α hα hα1 * (max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) * ‖f‖)) :=
+      mul_le_mul_of_nonneg_left
+        (hH.trans (mul_le_mul_of_nonneg_left hg hC.le)) (by positivity)
+    _ = _ := by ring
+
+/-- Ellipticity supplies a uniform family of frozen bounded linear inverses. -/
+theorem exists_frozen_operator_bound :
+    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
+    ∃ D : ℝ, 0 < D ∧ ∀ (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A v w = A w v) →
+      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A v v) → (∀ v, A v v ≤ Λ * ‖v‖ ^ 2) →
+    ∀ (T : ℝ), 0 < T → T ≤ 1 →
+      ∃ P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
+          (P f).ut (t, x) = f (t, x) +
+            ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
+        ‖P‖ ≤ D := by
+  intro α hα hα1 μ Λ hμ hμΛ
+  let q := 1 / Real.sqrt μ
+  let D := (max 1 (q ^ 2) * max 1 (q ^ α)) *
+    boundConstant α hα hα1 * max 1 ((Real.sqrt Λ) ^ α)
+  have hC := (boundConstant_spec α hα hα1).1
+  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
+  intro A hSym hlo hhi T hT hT1
+  obtain ⟨S, hS, hA⟩ := exists_symmetric_factor A hμ hSym hlo
+  refine ⟨frozenInverse S hα hα1 hT hT1,
+    frozenInverse_solves A S hS hA hα hα1 hT hT1, ?_⟩
+  apply (frozenInverse_norm_le S hα hα1 hT hT1).trans
+  obtain ⟨hSn, hSin⟩ := factor_norm_bounds A S hμ hμΛ (fun v => hA v v) hlo hhi
+  have hI2 : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ 2) ≤ max 1 (q ^ 2) :=
+    max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hSin 2)
+  have hIa : max 1 (‖(S.symm : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 (q ^ α) :=
+    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSin hα.le)
+  have hSa : max 1 (‖(S : (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3))‖ ^ α) ≤ max 1 ((Real.sqrt Λ) ^ α) :=
+    max_le_max le_rfl (Real.rpow_le_rpow (norm_nonneg _) hSn hα.le)
+  apply mul_le_mul _ hSa (by positivity) (by positivity)
+  exact mul_le_mul_of_nonneg_right
+    (mul_le_mul hI2 hIa (by positivity) (by positivity)) hC.le
+
+/-- Correct a frozen inverse using the original coefficient multiplier. -/
+def nearFrozenInverse
+    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1) :
+    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T :=
+  ParametrixNeumannCorrection.correctedInverse P
+    ((NearIdentityParabolicRightInverse.multiplier b).comp P) hR
+
+/-- The correction adds the perturbation to the frozen coefficients exactly. -/
+theorem nearFrozenInverse_solves (A : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ))
+    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (hP : ∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
+      (P f).ut (t, x) = f (t, x) +
+        ∑ i, ∑ j, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (P f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
+    (f : Y («E» := (ClosedSmoothModel 3)) α T ℝ) :
+    ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
+      (nearFrozenInverse P b hR f).ut (t, x) = f (t, x) +
+        ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
+          (nearFrozenInverse P b hR f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
+  let R := (NearIdentityParabolicRightInverse.multiplier b).comp P
+  let g := (↑((Units.oneSub R hR)⁻¹) :
+    Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Y («E» := (ClosedSmoothModel 3)) α T ℝ) f
+  intro t ht x
+  have hg := congrArg (fun v : Y («E» := (ClosedSmoothModel 3)) α T ℝ => v (t, x))
+    (NearIdentityParabolicRightInverse.neumann_data_eq R hR f)
+  change g (t, x) = f (t, x) +
+    ParabolicHolderMultiplier.forcing b (P g) (t, x) at hg
+  change (P g).ut (t, x) = f (t, x) +
+    ∑ i, ∑ j, (A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
+      (P g).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
+  rw [hP g t ht x, hg]
+  simp only [ParabolicHolderMultiplier.forcing_apply, add_mul, Finset.sum_add_distrib]
+  ring
+
+/-- A half-size multiplier error increases the frozen bound by at most two. -/
+theorem nearFrozenInverse_norm_le
+    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hR : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1)
+    (hhalf : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2)
+    {D : ℝ} (hP : ‖P‖ ≤ D) :
+    ‖nearFrozenInverse P b hR‖ ≤ 2 * D := by
+  have hD : 0 ≤ D := (norm_nonneg P).trans hP
+  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
+  calc
+    _ ≤ D * 2 := mul_le_mul hP
+      (NearIdentityParabolicRightInverse.neumann_norm_le_two _ hR hhalf)
+      (norm_nonneg _) hD
+    _ = _ := mul_comm _ _
+
+/-- The original split Hölder bound controls the frozen error uniformly. -/
+theorem frozen_error_small
+    (P : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hα : 0 < α) (hT : 0 < T) {D ε Λb : ℝ}
+    (hP : ‖P‖ ≤ D)
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb)
+    (hε : 9 * D * ε ≤ 1 / 4)
+    (hΛ : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4) :
+    ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤ 1 / 2 ∧
+      ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ < 1 := by
+  have hD := (norm_nonneg P).trans hP
+  have hε0 := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
+  have hΛ0 := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
+  have hn : ‖(NearIdentityParabolicRightInverse.multiplier b).comp P‖ ≤
+      9 * D * (ε + Λb * T ^ (α / 2)) := by
+    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+    intro f
+    exact ParabolicHolderMultiplier.norm_error_le b P hα hT hb hbα hP f
+  constructor <;> nlinarith only [hn, hε, hΛ]
+
+/-- The perturbed inverse is linear in forcing, with constants chosen before the coefficients. -/
+theorem exists_nearFrozen_operator :
+    ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
+    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
+    ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
+      (∀ v, «λ» * ‖v‖ ^ 2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖ ^ 2) →
+    ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
+    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
+      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
+      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
+      Λb * T ^ (α / 2) ≤ ε₀ →
+      ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+        (∀ f, ∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3),
+          (S f).ut (t, x) = f (t, x) +
+            ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) *
+              (S f).ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧ ‖S‖ ≤ C := by
+  intro α hα hα1 μ Λ hμ hμΛ
+  obtain ⟨D, hD, hInv⟩ := exists_frozen_operator_bound α hα hα1 μ Λ hμ hμΛ
+  refine ⟨2 * D, 1 / (36 * D), 1, by positivity, by positivity, by norm_num, ?_⟩
+  intro A hSym hlo hhi T hT hT1 b Λb hb hbα hΛ
+  obtain ⟨P, hP, hPN⟩ := hInv A hSym hlo hhi T hT hT1
+  have hε : 9 * D * (1 / (36 * D)) ≤ 1 / 4 := by
+    apply le_of_eq
+    field_simp
+    ring
+  have hΛ' : 9 * D * Λb * T ^ (α / 2) ≤ 1 / 4 := by
+    calc
+      _ = 9 * D * (Λb * T ^ (α / 2)) := by ring
+      _ ≤ 9 * D * (1 / (36 * D)) := mul_le_mul_of_nonneg_left hΛ (by positivity)
+      _ ≤ _ := hε
+  obtain ⟨hhalf, hR⟩ := frozen_error_small P b hα hT hPN hb hbα hε hΛ'
+  exact ⟨nearFrozenInverse P b hR, nearFrozenInverse_solves A P hP b hR,
+    nearFrozenInverse_norm_le P b hR hhalf hPN⟩
+
+/-- Every forcing has a zero-trace solution under the uniform perturbation bounds. -/
+theorem exists_nearFrozen_solution :
+  ∀ α : ℝ, 0 < α → α < 1 → ∀ «λ» Λ : ℝ, 0 < «λ» → «λ» ≤ Λ →
+  ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
+  ∀ (A₀ : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), (∀ v w, A₀ v w = A₀ w v) →
+    (∀ v, «λ» * ‖v‖^2 ≤ A₀ v v) → (∀ v, A₀ v v ≤ Λ * ‖v‖^2) →
+  ∀ (T : ℝ), 0 < T → T ≤ τ₀ →
+  ∀ (b : Fin 3 → Fin 3 → ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
+    (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ ε₀) →
+    (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder («E» := (ClosedSmoothModel 3)) T) (b i j) ≤ Λb) →
+    Λb * T ^ (α/2) ≤ ε₀ →
+  ∀ f : ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+    ∃ G : ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T,
+      (∀ t ∈ Icc 0 T, ∀ x : (ClosedSmoothModel 3), G.ut (t, x) = f (t, x) +
+        ∑ i, ∑ j, (A₀ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) + b i j (t, x)) * G.ddu (t, x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
+      ‖G‖ ≤ C * ‖f‖ := by
+  intro α hα hα1 μ Λ hμ hμΛ
+  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hInv⟩ :=
+    exists_nearFrozen_operator α hα hα1 μ Λ hμ hμΛ
+  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
+  intro A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ f
+  obtain ⟨S, hS, hSN⟩ := hInv A hSym hlo hhi T hT hTτ b Λb hb hbα hΛ
+  exact ⟨S f, hS f, (S.le_opNorm f).trans
+    (mul_le_mul_of_nonneg_right hSN (norm_nonneg f))⟩
+
+end Poincare.NearFrozenParabolicRightInverse
```
