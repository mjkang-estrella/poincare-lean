# Buffered frozen parabolic solver: blocked at the single-cutoff cancellation

Date: 2026-09-15. Base: `555d87240530db1e37d895910aec95c5c5e05963`.
Branch: `worker/buffered-frozen-parabolic-solver`.

## Result

Items 1 and 2 are proved and committed. Item 3 is blocked because its required
coefficient cancellation is false with the same cutoff used for the coefficient
extension and the solution product. The numerical norm estimate has not been
proved or disproved. Four additional proved identities isolate the missing term.
This is a worker result awaiting independent review, with no merge or acceptance.
No existing Lean file, root import, or frozen task was modified.

- Item 1: `4cde61a0`, 14 declarations at that checkpoint.
- Item 2: `890859f6`, 60 declarations at that checkpoint, including generated declarations.
- Item 3: `118bd164`, four partial identities. Final proof head: `118bd164d00f4c63985d2c9befa782459fa49f2f`.

## Item 1: coefficient extension and uniform Hölder bounds

`Poincare.BufferedFrozenParabolicSolver.exists_spatial_carrier_split` constructs the
cylinder carrier explicitly with `Poincare.ParabolicHolder.ofFunction`. For a
smooth compactly supported scalar with sup bound ε and a spatial Lipschitz
constant B, the separate carrier bounds are ε and 2ε+B. The proof uses the
near/far interpolation at spatial distance one and monotonicity from spatial to
parabolic distance. It never bounds all of Euclidean space by the diameter of
the support. Its constants are quantified before time, and it works for every
real T, hence for all requested short positive intervals.

`Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries` applies
this construction to all nine globally smooth cutoff products. Its single
constant is Λ = ΣᵢΣⱼ(2ε+Bᵢⱼ), where Bᵢⱼ is a global Lipschitz constant for
x ↦ ξ(x)(aᵢⱼ(x)−aᵢⱼ(anchor)). The smooth cutoff-extension argument uses
`Poincare.ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul`.

`Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal` has the exact
Appendix A bilinear-field statement. Its literal type assignment was checked
against the reproduced `FiniteAtlasSurvey.oscillationExtensionGoal`.

`Poincare.BufferedFrozenParabolicSolver.patchOscillation` is the supremum of
the maximum absolute entry difference over the closed cutoff support, with zero
inserted to handle empty support. It is the finite-product sup norm, not a
bilinear operator norm. `Poincare.BufferedFrozenParabolicSolver.patchOscillation_bounds`
proves nonnegativity and the entry bounds from compactness and continuity;
`Poincare.BufferedFrozenParabolicSolver.oscillation_extension_supremum` uses
this actual supremum for the carrier sup bound.

`Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius` and
`Poincare.BufferedFrozenParabolicSolver.patchOscillation_le` give the requested
ε-radius statement for every cutoff supported in the chosen ball.
`Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_extension`
and `Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_radius`
specialize to the genuine matrix inverse using
`Poincare.ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn`.

`Poincare.BufferedFrozenParabolicSolver.exists_buffered_cutoff` first chooses an
open intermediate set with compact closure. This supplies actual compact support,
which the bare cutoff existence theorem does not promise.
`Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff` applies this to the
landed coordinate supports in their actual host targets.

## Item 2: genuine transported equation

`Poincare.BufferedFrozenParabolicSolver.matrixBilin` turns the actual coordinate
matrix into a continuous bilinear form in the Euclidean host frame. The entry,
pairing, symmetry, and positivity proofs check the conversion.
`Poincare.BufferedFrozenParabolicSolver.matrixBilin_ellipticity` obtains the lower
bound using `Poincare.CompactCoefficientEllipticity.exists_uniform_coercivity`
on the singleton parameter family at the freezing point. This is a one-chart,
one-anchor result; no radius-uniform bound over a refined atlas is claimed.
Its upper bound is max(lam, ‖A₀‖).

`Poincare.BufferedFrozenParabolicSolver.inverse_metric_ellipticity` derives
positive definiteness from the genuine inverse pullback Gram matrix.
`Poincare.BufferedFrozenParabolicSolver.exists_chart_operator` uses
`Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator`, retains its
smallness hypotheses, proves the perturbed equation on the whole closed
cylinder, and proves the genuine equation where ξ=1.
`Poincare.BufferedFrozenParabolicSolver.exists_inverse_metric_chart_operator`
assembles the genuine inverse-metric extension with this solver.

The inherited constants are C=2D, ε₀=1/(36D), τ₀=1, where, for q=1/√lam,

D = (max(1,q²) max(1,q^α))
    · Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1
    · max(1,(√Λell)^α).

These choices come from the actual proof of
`Poincare.NearFrozenParabolicRightInverse.exists_nearFrozen_operator` and
`Poincare.NearFrozenParabolicRightInverse.exists_frozen_operator_bound`.
The new existence statements inherit them without changing their hypotheses.

`Poincare.BufferedFrozenParabolicSolver.FrozenSolver` separately preserves the
survey's constant-coefficient interface. It is not used to mislabel a
variable-coefficient solver. `Poincare.BufferedFrozenParabolicSolver.frozenCLMGoal`
and `Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal` prove the corresponding
survey interfaces, including exactly 9 C_S (ε+Λ T^(α/2)) ‖f‖. Target adapters to
`FiniteAtlasSurvey.frozenCLMGoal` and `FiniteAtlasSurvey.frozenErrorGoal` compile.

## Item 3: exact blocking shape and strongest partial result

The frozen task defines b=ψ(a−A₀), then requires a−A₀−b to vanish on supp ψ.
The exact algebraic identity is instead

    a − A₀ − b = (1−ψ)(a−A₀).

For 0<ψ<1 and a≠A₀ this is nonzero. For example, ψ=1/2, A₀=1, a=2 leaves
1/2. The one-locus agreement proved in item 2 does not extend to the whole
support. Forcing supported on the one-locus does not make the solution vanish
on the cutoff transition region.

`Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap` proves the exact
identity and `Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap_ne_zero`
proves the nonvanishing implication. `Poincare.BufferedFrozenParabolicSolver.nearFrozen_chart_residual`
retains the resulting principal residual in the actual near-frozen equation.

`Poincare.BufferedFrozenParabolicSolver.exists_cutoff_chart_residual` uses the
actual product jets returned by
`Poincare.ParabolicCutoffCommutator.exists_cutoff_operator`. Assuming ψ f=f,
it proves pointwise on the closed cylinder

    L_chart(ψ Sf) − f
      = −ψ Σᵢⱼ (1−ψ)(aᵢⱼ−A₀ᵢⱼ) DᵢDⱼ(Sf)
        −Σᵢⱼ aᵢⱼ (Dᵢψ Dⱼ(Sf) + Dᵢ(Sf) Dⱼψ + DᵢDⱼψ Sf).

Thus a principal transition term remains in addition to the commutator. This is
a proved partial identity, not a replacement for the frozen norm target. No
C_osc or C_ψ is claimed for the unproved bound, and no Y-valued global chart
operator is claimed from the pointwise identity alone.

The survey's section 2.4 already specifies the repair: use a separate coefficient
cutoff ξ with ξ=1 on supp ψ and b=ξ(a−A₀). Alternatively retain and estimate the
extra principal term under a revised contract. Neither change was silently
made to the frozen task. The worker contract explicitly requires a blocked
report when a frozen assertion is wrong.

Exact next first action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Then review the two-cutoff contract before attempting the single-chart norm
estimate and its genuine coefficient/commutator carriers.

## Preparation and evidence

Initial git status was clean, and HEAD and the worktree inventory were checked.
README, HANDOFF's top section, PROJECT_MAP, the task, worker contract including
its 2026-09-15 update, and the required survey sections and landed definitions
were read. Appendix A was extracted unchanged to
`/tmp/buffered-frozen-parabolic-solver/ReportProbe.lean`; its focused Lean command
exited 0 with empty output.

The prescribed catalog search was attempted first. The catalog is absent at
this base; actual output was:

```text
theorem registry: [Errno 2] No such file or directory: 'harness/v2/catalog/latest.json'
```

Direct source reads were used after that failure. No catalog or frozen contract
was created or edited. Failed diagnostics, target probes, final gate results,
and the actual source diff follow. Root integration audits are the orchestrator's
responsibility and were not run by this worker.

## Final verification

Final source SHA-256: `2552b7c7993478aaeb0983d715eae1827dc5b50f1aa48e08b6a0594bef241f49`.

All 64 emitted declarations, including generated declarations and declarations outside the public namespace, have exactly `[propext, Classical.choice, Quot.sound]`. The focused source check had no diagnostics. Lake replayed pre-existing dependency warnings and finished successfully.

### lean

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Exit code: `0`.

```text
(empty stdout and stderr)
```

### tokens

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/BufferedFrozenParabolicSolver.lean
```

Exit code: `1`.

```text
(empty stdout and stderr)
```

### whitespace

```sh
git diff --check
```

Exit code: `0`.

```text
(empty stdout and stderr)
```

### build

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.BufferedFrozenParabolicSolver
```

Exit code: `0`.

Output excerpt: last three lines; full dependency replay output remains in `/tmp/buffered-frozen-parabolic-solver/final-build.log`.

```text
Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
✔ [3888/3888] Built Poincare.Global.BufferedFrozenParabolicSolver (39s)
Build completed successfully (3888 jobs).
```

### audit

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/buffered-frozen-parabolic-solver/ModuleAudit.lean
```

Exit code: `0`.

```text
'Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius._simp_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_supremum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_cutoff_chart_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.solves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.S' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_coefficient_gap_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.nearFrozen_chart_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.frozenCLMGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_spatial_carrier_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_inverse_metric_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_buffered_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_MODULE_AUDIT declarations=64; every declaration has exactly the required three dependencies
```

### targets

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/buffered-frozen-parabolic-solver/TargetProbe.lean
```

Exit code: `0`.

```text
(empty stdout and stderr)
```

The token search exits 1 because it found no matches, which is the required result.

## Exact resisting probe

```lean
import Poincare.Global.BufferedFrozenParabolicSolver
example (psi a A : ℝ) (hpsi : 0 < psi ∧ psi < 1) (hchange : a ≠ A) :
    a - A - psi * (a - A) = 0 := by
  ring_nf
```

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/buffered-frozen-parabolic-solver/ResistingGoal.lean`. Exit code: `1`.

```text
/tmp/buffered-frozen-parabolic-solver/ResistingGoal.lean:3:33: error: unsolved goals
psi a A : ℝ
hpsi : 0 < psi ∧ psi < 1
hchange : a ≠ A
⊢ a - a * psi - A + A * psi = 0
```

## Audit and literal target probes

### Complete module audit source

```lean
import Poincare.Global.BufferedFrozenParabolicSolver
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.BufferedFrozenParabolicSolver
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

### Appendix reproduction and target assignments

The complete Appendix A is already preserved in `harness/reports/finite-atlas-parametrix-survey_done.md`. Reproduction used this exact extraction:

```python
from pathlib import Path
s = Path("harness/reports/finite-atlas-parametrix-survey_done.md").read_text()
s = s.split("<!-- BEGIN FINAL LEAN PROBE -->")[1].split("```lean\n")[1].split("```")[0]
Path("/tmp/buffered-frozen-parabolic-solver/ReportProbe.lean").write_text(s)
```

`LEAN_NUM_THREADS=1 lake env lean /tmp/buffered-frozen-parabolic-solver/ReportProbe.lean` exited 0 with empty output. The final target probe prepended `import Poincare.Global.BufferedFrozenParabolicSolver` to this unchanged appendix and appended:

```lean
example : FiniteAtlasSurvey.oscillationExtensionGoal :=
  Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal
example {α T C_S ε Λ : ℝ} {A0 : FiniteAtlasSurvey.Bilin}
    (S : FiniteAtlasSurvey.FrozenSolver α T C_S A0)
    (b : Fin 3 → Fin 3 → FiniteAtlasSurvey.Scalar α T) :
    FiniteAtlasSurvey.frozenErrorGoal (ε := ε) (Λ := Λ) S b := by
  exact Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal
    ⟨S.S, S.bound, S.solves⟩ b
example : FiniteAtlasSurvey.frozenCLMGoal := by
  intro α hα hα1 lam Λ hlam hlamΛ
  obtain ⟨C, hC, hS⟩ := Poincare.BufferedFrozenParabolicSolver.frozenCLMGoal
    α hα hα1 lam Λ hlam hlamΛ
  refine ⟨C, hC, ?_⟩
  intro A0 hsym hlo hhi T hT hT1
  obtain ⟨S⟩ := hS A0 hsym hlo hhi T hT hT1
  exact ⟨⟨S.S, S.bound, S.solves⟩⟩
```

## Preserved failed compiler outputs

These are diagnostic probes, not committed declarations. Each log below came from a nonzero focused Lean command. The first module audit also exposed generated notation declarations with no foundational dependencies; those notations were removed before the item 1 commit.

<details>
<summary>check.log</summary>

```text
ContDiffOn.clm_apply.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {s : Set E} {n : WithTop ℕ∞} {f : E → F →L[𝕜] G} {g : E → F}
  (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s
ContinuousLinearMap.contDiff.{u_1, u_2, u_3} {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞} (f : E →L[𝕜] F) :
  ContDiff 𝕜 n ⇑f
HasCompactSupport.mul_right.{u_2, u_4} {α : Type u_2} {β : Type u_4} [TopologicalSpace α] [MulZeroClass β]
  {f f' : α → β} (hf : HasCompactSupport f) : HasCompactSupport (f * f')
ContDiff.lipschitzWith_of_hasCompactSupport.{u_1, u_2, u_3} {n : WithTop ℕ∞} {𝕂 : Type u_1} [RCLike 𝕂] {E' : Type u_2}
  [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type u_3} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'}
  (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : n ≠ 0) : ∃ C, LipschitzWith C f
Finset.single_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f : ι → N} {s : Finset ι}
  [AddLeftMono N] (hf : ∀ i ∈ s, 0 ≤ f i) {a : ι} (h : a ∈ s) : f a ≤ ∑ x ∈ s, f x
Metric.continuousAt_iff.{u, v} {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}
  {a : α} : ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) (f a) < ε
Metric.continuousAt_iff'.{u, v} {α : Type u} {β : Type v} [PseudoMetricSpace α] [TopologicalSpace β] {f : β → α}
  {b : β} : ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ (x : β) in nhds b, dist (f x) (f b) < ε
/tmp/buffered-frozen-parabolic-solver/Check.lean:10:7: error(lean.unknownIdentifier): Unknown constant `IsCompact.exists_isOpen_superset_and_isCompact_closure`
/tmp/buffered-frozen-parabolic-solver/Check.lean:11:7: error(lean.unknownIdentifier): Unknown identifier `exists_isOpen_isCompact_closure`
/tmp/buffered-frozen-parabolic-solver/Check.lean:12:7: error(lean.unknownIdentifier): Unknown identifier `ParabolicHolder.supNorm_eq`
theorem Poincare.ParabolicHolder.holderSeminorm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) = ‖WithLp.snd ↑f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  le_antisymm
    (csSup_le
      (Set.insert_nonempty 0
        (Set.range fun i =>
          ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ /
            Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α))
      fun r a =>
      Or.casesOn a (fun h => Eq.symm h ▸ norm_nonneg (WithLp.snd ↑f)) fun h =>
        Exists.casesOn h fun i h =>
          h ▸
            id
              (Eq.mpr
                (id (congrArg (fun _a => _a ≤ ‖WithLp.snd ↑f‖) (Eq.symm (Poincare.ParabolicHolder.increment_norm f i))))
                (lp.norm_apply_le_norm
                  (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true)) (WithLp.snd ↑f)
                  i)))
    (lp.norm_le_of_forall_le
      (le_csSup (Poincare.ParabolicHolder.holderSeminorm_bddAbove f)
        (Set.mem_insert 0
          (Set.range fun i =>
            ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ /
              Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)))
      fun i =>
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a ≤ Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
            (Poincare.ParabolicHolder.increment_norm f i)))
        (le_csSup (Poincare.ParabolicHolder.holderSeminorm_bddAbove f)
          (Set.mem_insert_of_mem 0 (Set.mem_range_self i))))
```

</details>

<details>
<summary>check2.log</summary>

```text
Matrix.toEuclideanLin.{u_3, u_7, u_8} {𝕜 : Type u_3} [RCLike 𝕜] {m : Type u_7} {n : Type u_8} [Fintype n]
  [DecidableEq n] : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m
LinearMap.toContinuousLinearMap.{u, v, x} {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F' : Type x} [AddCommGroup F']
  [Module 𝕜 F'] [TopologicalSpace F'] [IsTopologicalAddGroup F'] [ContinuousSMul 𝕜 F'] [CompleteSpace 𝕜] [T2Space E]
  [FiniteDimensional 𝕜 E] : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F'
/tmp/buffered-frozen-parabolic-solver/Check2.lean:4:7: error(lean.unknownIdentifier): Unknown constant `ContinuousLinearMap.innerSL`
innerSL.{u_1, u_2} (𝕜 : Type u_1) {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
  E →L⋆[𝕜] E →L[𝕜] 𝕜
innerSL_apply_apply.{u_1, u_2} (𝕜 : Type u_1) {E : Type u_2} [RCLike 𝕜] [SeminormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (v w : E) : ((innerSL 𝕜) v) w = inner 𝕜 v w
Matrix.PosDef.isHermitian.{u_2, u_3} {n : Type u_2} {R : Type u_3} [Ring R] [PartialOrder R] [StarRing R]
  {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian
Matrix.PosDef.dotProduct_mulVec_pos.{u_2, u_3} {n : Type u_2} {R : Type u_3} [Ring R] [PartialOrder R] [StarRing R]
  [Fintype n] {M : Matrix n n R} (hM : M.PosDef) {x : n → R} (hx : x ≠ 0) : 0 < star x ⬝ᵥ M.mulVec x
/tmp/buffered-frozen-parabolic-solver/Check2.lean:9:7: error(lean.unknownIdentifier): Unknown constant `Matrix.PosDef.pos`
EuclideanSpace.proj.{u_1, u_3} {ι : Type u_1} {𝕜 : Type u_3} [RCLike 𝕜] (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι)
Matrix.toEuclideanLin_apply.{u_3, u_7, u_8} {𝕜 : Type u_3} [RCLike 𝕜] {m : Type u_7} {n : Type u_8} [Fintype n]
  [DecidableEq n] (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
  (Matrix.toEuclideanLin M) v = WithLp.toLp 2 (M.mulVec v.ofLp)
ContinuousLinearMap.flip.{u_1, u_2, u_3, u_4, u_6, u_8} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {𝕜₃ : Type u_3} {E : Type u_4}
  {F : Type u_6} {G : Type u_8} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
  (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G
Poincare.inverseChartPullbackGramMatrix_posDef.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M) (x₀ : M)
  (z : ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x₀).target) :
  (Poincare.inverseChartPullbackGramMatrix g x₀ z).PosDef
Poincare.inverseChartPullbackGramMatrix_eq_field.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M) (x₀ : M)
  (z : ↑(extChartAt (Poincare.closedSmoothModelWithCorners n) x₀).target) :
  Poincare.inverseChartPullbackGramMatrix g x₀ z = Poincare.inverseChartPullbackGramMatrixField g x₀ ↑z
```

</details>

<details>
<summary>item1-01.log</summary>

```text
Poincare/Global/BufferedFrozenParabolicSolver.lean:22:40: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/BufferedFrozenParabolicSolver.lean:87:32: error: unexpected token ':='; expected ')', ',' or ':'
```

</details>

<details>
<summary>item1-03.log</summary>

```text
Poincare/Global/BufferedFrozenParabolicSolver.lean:158:42: error(lean.unknownIdentifier): Unknown identifier `MeasureTheory.BorelSpace`
Poincare/Global/BufferedFrozenParabolicSolver.lean:163:40: error(lean.unknownIdentifier): Unknown identifier `M`

Note: It is not possible to treat `M` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
Poincare/Global/BufferedFrozenParabolicSolver.lean:163:48: error(lean.unknownIdentifier): Unknown identifier `M`

Note: It is not possible to treat `M` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```

</details>

<details>
<summary>item1-04.log</summary>

```text
Poincare/Global/BufferedFrozenParabolicSolver.lean:180:4: error: Application type mismatch: The argument
  ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p
has type
  ∀ (i j : Fin 3),
    ContDiffOn ℝ ∞
      (fun z => @Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv (inverseChartPullbackGramMatrixField g p z) i j)
      (extChartAt (closedSmoothModelWithCorners 3) p).target
but is expected to have type
  ∀ (i j : Fin 3),
    ContDiffOn ℝ ∞ (fun x => @Inv.inv (Fin 3 → Fin 3 → ℝ) Pi.instInv (inverseChartPullbackGramMatrixField g p x) i j)
      (extChartAt ?m.210 p).target
in the application
  oscillation_extension_entries hα hα1 (isOpen_extChartAt_target p)
    (fun x => (inverseChartPullbackGramMatrixField g p x)⁻¹)
    (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p)
Poincare/Global/BufferedFrozenParabolicSolver.lean:195:20: error(lean.invalidField): Invalid field `continuousAt`: The environment does not contain `Function.continuousAt`, so it is not possible to project the field `continuousAt` from an expression
  ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j anchor hanchor
of type
  ∀ (m : ℕ),
    ↑m ≤ ⊤ →
      ∃ u ∈ 𝓝[insert anchor (extChartAt (closedSmoothModelWithCorners 3) p).target] anchor,
        ∃ p_1, HasFTaylorSeriesUpToOn (↑m) (fun z => (inverseChartPullbackGramMatrixField g p z)⁻¹ i j) p_1 u
Poincare/Global/BufferedFrozenParabolicSolver.lean:198:0: warning: automatically included section variable(s) unused in theorem `Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff`:
  [T2Space M]
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

</details>

<details>
<summary>item1-audit.log</summary>

```text
'_private.Poincare.Global.BufferedFrozenParabolicSolver.0.Poincare.BufferedFrozenParabolicSolver._aux_Poincare_Global_BufferedFrozenParabolicSolver___macroRules__private_Poincare_Global_BufferedFrozenParabolicSolver_0_Poincare_BufferedFrozenParabolicSolver_termE_1' does not depend on any axioms
/tmp/buffered-frozen-parabolic-solver/ModuleAudit.lean:3:0: error: Unexpected foundational dependencies for _private.Poincare.Global.BufferedFrozenParabolicSolver.0.Poincare.BufferedFrozenParabolicSolver._aux_Poincare_Global_BufferedFrozenParabolicSolver___macroRules__private_Poincare_Global_BufferedFrozenParabolicSolver_0_Poincare_BufferedFrozenParabolicSolver_termE_1: []
```

</details>

<details>
<summary>item2-01.log</summary>

```text
/tmp/buffered-frozen-parabolic-solver/Item2.lean:19:26: warning: `Matrix.toEuclideanLin_apply` has been deprecated: Use `Matrix.toLpLin_apply` instead

Note: The updated constant has a different type:
  ∀ {m : Type u_1} {n : Type u_2} {R : Type u_4} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]
    (p q : ENNReal) (M : Matrix m n R) (v : WithLp p (n → R)),
    ((Matrix.toLpLin p q) M) v = WithLp.toLp q (M.mulVec v.ofLp)
instead of
  ∀ {𝕜 : Type u_3} [inst : RCLike 𝕜] {m : Type u_7} {n : Type u_8} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
    (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n), (Matrix.toEuclideanLin M) v = WithLp.toLp 2 (M.mulVec v.ofLp)
/tmp/buffered-frozen-parabolic-solver/Item2.lean:16:76: error: unsolved goals
A : Matrix (Fin 3) (Fin 3) ℝ
v w : E
⊢ ∑ x, A.mulVec w.ofLp x * v.ofLp x = ∑ x, v.ofLp x * A.mulVec w.ofLp x
/tmp/buffered-frozen-parabolic-solver/Item2.lean:22:41: error: unsolved goals
A : Matrix (Fin 3) (Fin 3) ℝ
i j : Fin 3
⊢ ∑ x, Pi.single i 1 x * A x j = A i j
/tmp/buffered-frozen-parabolic-solver/Item2.lean:46:30: error: Application type mismatch: The argument
  h
has type
  v.ofLp = 0
of sort `Prop` but is expected to have type
  ENNReal
of sort `Type` in the application
  @WithLp.ofLp_injective h
```

</details>

<details>
<summary>item3-02.log</summary>

```text
/tmp/buffered-frozen-parabolic-solver/Item3.lean:42:21: error: expected token
```

</details>

<details>
<summary>item3-03.log</summary>

```text
/tmp/buffered-frozen-parabolic-solver/Item3.lean:40:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

</details>

## Earlier checkpoint audits

<details>
<summary>item1-audit2.log</summary>

```text
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius._simp_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_supremum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_spatial_carrier_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_buffered_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=14; every declaration has exactly the required three dependencies
```

</details>

<details>
<summary>item2-audit.log</summary>

```text
'Poincare.BufferedFrozenParabolicSolver.frozenErrorGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_15' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius._simp_1_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_supremum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.solves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillationExtensionGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.oscillation_extension_entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.cutoff_entry_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_atlas_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.S' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_ellipticity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.inverse_metric_oscillation_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_oscillation_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.frozenCLMGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_spatial_carrier_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.matrixBilin._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.patchOscillation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_inverse_metric_chart_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.exists_buffered_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.BufferedFrozenParabolicSolver.FrozenSolver.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_MODULE_AUDIT declarations=60; every declaration has exactly the required three dependencies
```

</details>

## Final proof diff from the recorded base

<details>
<summary>Verified Lean source diff</summary>

```diff
diff --git a/Poincare/Global/BufferedFrozenParabolicSolver.lean b/Poincare/Global/BufferedFrozenParabolicSolver.lean
new file mode 100644
index 00000000..314a94ca
--- /dev/null
+++ b/Poincare/Global/BufferedFrozenParabolicSolver.lean
@@ -0,0 +1,506 @@
+import Poincare.Global.NearFrozenParabolicRightInverse
+import Poincare.Global.ParabolicCutoffCommutator
+import Poincare.Global.FiniteAtlasParabolicTensorSpace
+
+noncomputable section
+set_option autoImplicit false
+open Set
+open scoped Manifold ContDiff Topology
+
+namespace Poincare.BufferedFrozenParabolicSolver
+
+open ParabolicHolder ParabolicSolutionGraph
+
+/-- A bounded smooth spatial function has separate, time-uniform carrier bounds. -/
+theorem exists_spatial_carrier_split {v : (ClosedSmoothModel 3) → ℝ}
+    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
+    {ε α : ℝ} (hε : 0 ≤ ε) (hb : ∀ x, ‖v x‖ ≤ ε)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, ∃ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+      (∀ p ∈ cylinder T, f p = v p.2) ∧
+      supNorm (cylinder T) f ≤ ε ∧ holderSeminorm α (cylinder T) f ≤ Λ := by
+  classical
+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
+  have hh (x y : (ClosedSmoothModel 3)) : ‖v x - v y‖ ≤ (2 * ε + B) * ‖x-y‖ ^ α := by
+    have h := ParabolicCutoffCommutator.scale_interpolation (L := 2*ε+B) (R := 1)
+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
+      ((norm_sub_le (v x) (v y)).trans (by linarith [hb x, hb y, B.coe_nonneg]))
+    simpa using h
+  refine ⟨2*ε+B, by positivity, ?_⟩
+  intro T
+  let f : ℝ × (ClosedSmoothModel 3) → ℝ := fun p => if p ∈ cylinder T then v p.2 else 0
+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
+    intro p hp; simp [f, hp]
+  have hbound : ∀ p ∈ cylinder T, ‖f p‖ ≤ ε := by
+    intro p hp; simpa [f, hp] using hb p.2
+  have hholder : HasHolderBound α (cylinder T) f (2*ε+B) := by
+    intro p hp q hq
+    simp only [f, if_pos hp, if_pos hq]
+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow (norm_nonneg _) (by
+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le)
+      (by positivity))
+  let fY := ofFunction f hoff ⟨ε, hbound⟩ ⟨2*ε+B, hholder⟩
+  refine ⟨fY, ?_, ?_, ?_⟩
+  · intro p hp
+    change f p = v p.2
+    simp [f, hp]
+  · rw [supNorm_eq]
+    apply lp.norm_le_of_forall_le hε
+    intro p
+    change ‖f p‖ ≤ ε
+    by_cases hp : p ∈ cylinder T
+    · exact hbound p hp
+    · simpa [hoff p hp] using hε
+  · rw [holderSeminorm_eq]
+    apply lp.norm_le_of_forall_le (by positivity)
+    intro i
+    rw [increment_norm]
+    exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos i.2.2.2) α)).2
+      (hholder _ i.2.1 _ i.2.2.1)
+
+/-- Cutoff multiplication preserves the local oscillation bound globally. -/
+theorem cutoff_entry_bound {ξ a : (ClosedSmoothModel 3) → ℝ} {A ε : ℝ}
+    (hξ : ∀ x, ξ x ∈ Icc 0 1) (hε : 0 ≤ ε)
+    (ha : ∀ x ∈ tsupport ξ, |a x - A| ≤ ε) (x : (ClosedSmoothModel 3)) :
+    ‖ξ x * (a x - A)‖ ≤ ε := by
+  by_cases hx : x ∈ tsupport ξ
+  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hξ x).1]
+    exact (mul_le_mul_of_nonneg_left (ha x hx) (hξ x).1).trans
+      (by nlinarith [(hξ x).2])
+  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
+    exact hε
+
+/-- Nine smooth coordinate entries extend with one constant chosen before time. -/
+theorem oscillation_extension_entries {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U) (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (anchor : (ClosedSmoothModel 3))
+    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
+    (hξU : tsupport ξ ⊆ U) (hξ01 : ∀ x, ξ x ∈ Icc 0 1)
+    {ε : ℝ} (hε : 0 ≤ ε)
+    (hosc : ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε) :
+    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
+      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+        (∀ t ∈ Icc 0 T, ∀ x i j,
+          b i j (t,x) = ξ x * (a x i j - a anchor i j)) ∧
+        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
+        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
+  classical
+  have hex (i j : Fin 3) := exists_spatial_carrier_split
+    (ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul hU hξ hξU
+      ((ha i j).sub contDiffOn_const)) hc.mul_right hε
+    (cutoff_entry_bound hξ01 hε (fun x hx => hosc x hx i j)) hα hα1
+  choose L hL b hb using hex
+  refine ⟨∑ i, ∑ j, L i j, Finset.sum_nonneg (fun i _ =>
+    Finset.sum_nonneg (fun j _ => hL i j)), ?_⟩
+  intro T
+  refine ⟨fun i j => b i j T, ?_, fun i j => (hb i j T).2.1, ?_⟩
+  · intro t ht x i j
+    exact (hb i j T).1 (t,x) ⟨ht, mem_univ x⟩
+  · intro i j
+    apply (hb i j T).2.2.trans
+    exact (Finset.single_le_sum (fun j _ => hL i j) (Finset.mem_univ j)).trans
+      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hL i j))
+        (Finset.mem_univ i))
+
+/-- The bilinear-field extension target, with its original short-time quantifiers. -/
+theorem oscillationExtensionGoal :
+    ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set (ClosedSmoothModel 3)), IsOpen U →
+    ∀ (a : (ClosedSmoothModel 3) → (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)), ContDiffOn ℝ ∞ a U → ∀ (anchor : (ClosedSmoothModel 3)), anchor ∈ U →
+    ∀ (ξ : (ClosedSmoothModel 3) → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
+    (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
+    (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
+      |a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) - a anchor ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)| ≤ ε) →
+    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+        (∀ t ∈ Icc 0 T, ∀ x i j,
+          b i j (t,x) = ξ x * (a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) - a anchor ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) ∧
+        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
+        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
+  intro α hα hα1 U hU a ha anchor _ ξ hξ hc hξU hξ01 ε hε hosc
+  obtain ⟨Λ, hΛ, hb⟩ := oscillation_extension_entries hα hα1 hU
+    (fun x i j => a x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
+    (fun i j => (ha.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
+    anchor hξ hc hξU hξ01 hε hosc
+  exact ⟨Λ, hΛ, fun T _ _ => hb T⟩
+
+/-- Compact coordinate sets have genuinely compactly supported smooth cutoffs. -/
+theorem exists_buffered_cutoff {K U : Set (ClosedSmoothModel 3)} (hK : IsCompact K)
+    (hU : IsOpen U) (hKU : K ⊆ U) :
+    ∃ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ U ∧
+      (∀ x ∈ K, ∀ᶠ y in 𝓝 x, ξ y = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) := by
+  obtain ⟨V, hV, hKV, hVU, hcV⟩ :=
+    exists_open_between_and_isCompact_closure hK hU hKU
+  obtain ⟨ξ, hξ, hξV, hone, hξ01⟩ :=
+    ClosedLaplacianStokesGlobalCoefficients.exists_cutoff_of_isCompact hK hV hKV
+  exact ⟨ξ, hξ, hcV.of_isClosed_subset (isClosed_tsupport ξ)
+    (hξV.trans subset_closure), hξV.trans (subset_closure.trans hVU), hone, hξ01⟩
+
+/-- Continuity at the freezing point controls every entry on any sufficiently small patch. -/
+theorem exists_oscillation_radius (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
+    (ha : ∀ i j, ContinuousAt (fun x => a x i j) anchor)
+    {ε : ℝ} (hε : 0 < ε) :
+    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : (ClosedSmoothModel 3) → ℝ, tsupport ξ ⊆ Metric.ball anchor ρ →
+      ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε := by
+  have hev : ∀ᶠ x in 𝓝 anchor, ∀ i j, |a x i j - a anchor i j| < ε := by
+    simp only [Filter.eventually_all]
+    intro i j
+    simpa only [Real.dist_eq] using (Metric.continuousAt_iff'.mp (ha i j) ε hε)
+  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hev
+  exact ⟨ρ, hρ, fun ξ hξ x hx i j => (hball (hξ hx) i j).le⟩
+
+/-- The maximum entry oscillation on the closed cutoff support, including the empty case. -/
+def patchOscillation (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) (ξ : (ClosedSmoothModel 3) → ℝ) : ℝ :=
+  sSup (insert 0 ((fun x => ‖a x - a anchor‖) '' tsupport ξ))
+
+/-- Compactness and continuity make the oscillation supremum a genuine bound. -/
+theorem patchOscillation_bounds (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
+    {ξ : (ClosedSmoothModel 3) → ℝ} (hc : HasCompactSupport ξ) (ha : ContinuousOn a (tsupport ξ)) :
+    0 ≤ patchOscillation a anchor ξ ∧ ∀ x ∈ tsupport ξ, ∀ i j,
+      |a x i j - a anchor i j| ≤ patchOscillation a anchor ξ := by
+  have hbd : BddAbove (insert 0 ((fun x => ‖a x - a anchor‖) '' tsupport ξ)) :=
+    ((hc.image_of_continuousOn (ha.sub continuousOn_const).norm).insert 0).bddAbove
+  refine ⟨le_csSup hbd (mem_insert _ _), ?_⟩
+  intro x hx i j
+  have he : ‖(a x - a anchor) i j‖ ≤ ‖a x - a anchor‖ :=
+    (norm_le_pi_norm ((a x - a anchor) i) j).trans (norm_le_pi_norm (a x - a anchor) i)
+  exact he.trans (le_csSup hbd (mem_insert_of_mem _ (mem_image_of_mem _ hx)))
+
+/-- A bound for all nine entries bounds the actual oscillation supremum. -/
+theorem patchOscillation_le (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3))
+    (ξ : (ClosedSmoothModel 3) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
+    (ha : ∀ x ∈ tsupport ξ, ∀ i j, |a x i j - a anchor i j| ≤ ε) :
+    patchOscillation a anchor ξ ≤ ε := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨x, hx, rfl⟩)
+  · exact hε
+  · exact (pi_norm_le_iff_of_nonneg hε).mpr fun i =>
+      (pi_norm_le_iff_of_nonneg hε).mpr fun j => ha x hx i j
+
+/-- The extension has sup bound equal to the actual patch oscillation. -/
+theorem oscillation_extension_supremum {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    {U : Set (ClosedSmoothModel 3)} (hU : IsOpen U) (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ)
+    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (anchor : (ClosedSmoothModel 3))
+    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
+    (hξU : tsupport ξ ⊆ U) (hξ01 : ∀ x, ξ x ∈ Icc 0 1) :
+    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
+      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+        (∀ t ∈ Icc 0 T, ∀ x i j,
+          b i j (t,x) = ξ x * (a x i j - a anchor i j)) ∧
+        (∀ i j, supNorm (cylinder T) (b i j) ≤ patchOscillation a anchor ξ) ∧
+        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
+  have hcont : ContinuousOn a (tsupport ξ) :=
+    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j =>
+      (ha i j).continuousOn.mono hξU
+  obtain ⟨hω, hbound⟩ := patchOscillation_bounds a anchor hc hcont
+  exact oscillation_extension_entries hα hα1 hU a ha anchor hξ hc hξU hξ01 hω hbound
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
+  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+
+/-- The extended entries are those of the genuine inverse metric in the host chart. -/
+theorem inverse_metric_oscillation_extension
+    (g : ClosedSmoothRiemannianMetric 3 M) (p : M)
+    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (anchor : (ClosedSmoothModel 3))
+    {ξ : (ClosedSmoothModel 3) → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ)
+    (hξU : tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).target)
+    (hξ01 : ∀ x, ξ x ∈ Icc 0 1) {ε : ℝ} (hε : 0 ≤ ε)
+    (hosc : ∀ x ∈ tsupport ξ, ∀ i j,
+      |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
+        (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε) :
+    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ,
+      ∃ b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ,
+        (∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x *
+          ((inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
+            (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j)) ∧
+        (∀ i j, supNorm (cylinder T) (b i j) ≤ ε) ∧
+        (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) := by
+  exact oscillation_extension_entries hα hα1 (isOpen_extChartAt_target p)
+    (fun x i j => (inverseChartPullbackGramMatrixField g p x)⁻¹ i j)
+    (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p)
+    anchor hξ hc hξU hξ01 hε hosc
+
+/-- The genuine inverse entries have arbitrarily small oscillation at each target point. -/
+theorem inverse_metric_oscillation_radius
+    (g : ClosedSmoothRiemannianMetric 3 M) (p : M) (anchor : (ClosedSmoothModel 3))
+    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
+    {ε : ℝ} (hε : 0 < ε) :
+    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ : (ClosedSmoothModel 3) → ℝ, tsupport ξ ⊆ Metric.ball anchor ρ →
+      ∀ x ∈ tsupport ξ, ∀ i j,
+        |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
+          (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε := by
+  apply exists_oscillation_radius _ anchor _ hε
+  intro i j
+  exact ((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
+    anchor hanchor).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hanchor) |>.continuousAt
+
+omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
+/-- Each landed coordinate support has a compact buffer in its actual chart target. -/
+theorem exists_atlas_cutoff (A : FiniteAtlasParabolicTensorSpace.AtlasData M)
+    (i : Fin A.cover.chartCount) :
+    ∃ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧
+      tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)).target ∧
+      (∀ x ∈ FiniteAtlasParabolicTensorSpace.coordSupport A i,
+        ∀ᶠ y in 𝓝 x, ξ y = 1) ∧ (∀ x, ξ x ∈ Icc 0 1) := by
+  exact exists_buffered_cutoff (FiniteAtlasParabolicTensorSpace.isCompact_coordSupport A i)
+    (isOpen_extChartAt_target (A.cover.anchor i))
+    (FiniteAtlasParabolicTensorSpace.coordSupport_subset_target A i)
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped Manifold ContDiff Topology
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph
+
+/-- The matrix coefficients act in the actual Euclidean host frame. -/
+def matrixBilin (A : Matrix (Fin 3) (Fin 3) ℝ) : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ) :=
+  ((innerSL ℝ).comp (Matrix.toEuclideanLin A).toContinuousLinearMap).flip
+
+theorem matrixBilin_pairing (A : Matrix (Fin 3) (Fin 3) ℝ) (v w : (ClosedSmoothModel 3)) :
+    matrixBilin A v w = star (WithLp.ofLp v) ⬝ᵥ A.mulVec (WithLp.ofLp w) := by
+  change inner ℝ (Matrix.toEuclideanLin A w) v = _
+  rw [real_inner_comm]
+  simp [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, RCLike.inner_apply, mul_comm]
+
+theorem matrixBilin_entry (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
+    matrixBilin A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) = A i j := by
+  rw [matrixBilin_pairing]
+  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
+
+theorem matrixBilin_symm {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian)
+    (v w : (ClosedSmoothModel 3)) : matrixBilin A v w = matrixBilin A w v := by
+  rw [FrozenEllipticHeatOperator.bilinear_expansion (matrixBilin A) v w,
+    FrozenEllipticHeatOperator.bilinear_expansion (matrixBilin A) w v]
+  simp_rw [matrixBilin_entry]
+  rw [Finset.sum_comm]
+  apply Finset.sum_congr rfl
+  intro i _
+  apply Finset.sum_congr rfl
+  intro j _
+  have hij : A j i = A i j := by simpa using congrFun (congrFun hA i) j
+  rw [hij]
+  ring
+
+theorem matrixBilin_pos {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef)
+    (v : (ClosedSmoothModel 3)) (hv : v ≠ 0) : 0 < matrixBilin A v v := by
+  rw [matrixBilin_pairing]
+  apply hA.dotProduct_mulVec_pos
+  intro h
+  apply hv
+  exact WithLp.ofLp_injective 2 h
+
+theorem matrixBilin_ellipticity {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) :
+    ∃ lam Λ : ℝ, 0 < lam ∧ lam ≤ Λ ∧
+      (∀ v, lam * ‖v‖^2 ≤ matrixBilin A v v) ∧
+      (∀ v, matrixBilin A v v ≤ Λ * ‖v‖^2) := by
+  obtain ⟨lam, hlam, hlo⟩ := CompactCoefficientEllipticity.exists_uniform_coercivity
+    (fun _ : Unit => matrixBilin A) continuous_const (fun _ => matrixBilin_pos hA)
+  refine ⟨lam, max lam ‖matrixBilin A‖, hlam, le_max_left _ _, hlo (), ?_⟩
+  intro v
+  calc
+    _ ≤ ‖matrixBilin A v v‖ := le_abs_self _
+    _ ≤ ‖matrixBilin A‖ * ‖v‖ * ‖v‖ := (matrixBilin A).le_opNorm₂ v v
+    _ ≤ max lam ‖matrixBilin A‖ * ‖v‖^2 := by
+      nlinarith [mul_le_mul_of_nonneg_right (le_max_right lam ‖matrixBilin A‖) (sq_nonneg ‖v‖)]
+
+
+
+/-- A bounded frozen inverse with its equation on the closed cylinder. -/
+structure FrozenSolver (α T C_S : ℝ) (A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)) where
+  S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T
+  bound : ‖S‖ ≤ C_S
+  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
+    (S f).ut (t,x) = f (t,x) + ∑ i : Fin 3, ∑ j : Fin 3,
+      A0 ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
+
+/-- The landed conjugated heat inverse supplies the survey's frozen interface. -/
+theorem frozenCLMGoal :
+    ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
+    ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ), (∀ v w, A0 v w = A0 w v) →
+    (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
+    ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0) := by
+  intro α hα hα1 lam Λ hlam hlamΛ
+  obtain ⟨D, hD, hP⟩ := NearFrozenParabolicRightInverse.exists_frozen_operator_bound
+    α hα hα1 lam Λ hlam hlamΛ
+  refine ⟨D, hD, ?_⟩
+  intro A0 hsym hlo hhi T hT hT1
+  obtain ⟨P, hsolves, hbound⟩ := hP A0 hsym hlo hhi T hT hT1
+  exact ⟨⟨P, hbound, hsolves⟩⟩
+
+/-- The frozen solver and the constructed entry bounds give the exact multiplier estimate. -/
+theorem frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : (ClosedSmoothModel 3 →L[ℝ] ClosedSmoothModel 3 →L[ℝ] ℝ)}
+    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (hα : 0 < α) (hT : 0 < T)
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
+    ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
+      9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ := by
+  exact ParabolicHolderMultiplier.norm_error_le b S.S hα hT hb hbα S.bound
+
+/-- Near-frozen inversion yields the genuine coordinate equation on the cutoff one-locus. -/
+theorem exists_chart_operator :
+    ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λell : ℝ, 0 < lam → lam ≤ Λell →
+    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
+    ∀ (a : (ClosedSmoothModel 3) → Matrix (Fin 3) (Fin 3) ℝ) (anchor : (ClosedSmoothModel 3)) (ξ : (ClosedSmoothModel 3) → ℝ),
+      (a anchor).IsHermitian →
+      (∀ v, lam * ‖v‖^2 ≤ matrixBilin (a anchor) v v) →
+      (∀ v, matrixBilin (a anchor) v v ≤ Λell * ‖v‖^2) →
+    ∀ T : ℝ, 0 < T → T ≤ τ₀ →
+    ∀ (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ) (Λb : ℝ),
+      (∀ i j, supNorm (cylinder T) (b i j) ≤ ε₀) →
+      (∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λb) →
+      Λb * T ^ (α / 2) ≤ ε₀ →
+      (∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ξ x * (a x i j - a anchor i j)) →
+      ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+        ‖S‖ ≤ C ∧
+        (∀ f t, t ∈ Icc 0 T → ∀ x,
+          (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+            (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
+        (∀ f t, t ∈ Icc 0 T → ∀ x, ξ x = 1 →
+          (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+            a x i j * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) := by
+  intro α hα hα1 lam Λell hlam hlamΛ
+  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hS⟩ :=
+    NearFrozenParabolicRightInverse.exists_nearFrozen_operator α hα hα1 lam Λell hlam hlamΛ
+  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
+  intro a anchor ξ hsym hlo hhi T hT hTτ b Λb hb hbα hΛb heq
+  obtain ⟨S, hsolves, hbound⟩ := hS (matrixBilin (a anchor))
+    (matrixBilin_symm hsym) hlo hhi T hT hTτ b Λb hb hbα hΛb
+  simp_rw [matrixBilin_entry] at hsolves
+  refine ⟨S, hbound, hsolves, ?_⟩
+  intro f t ht x hx
+  simpa only [heq t ht x, hx, one_mul, add_sub_cancel] using hsolves f t ht x
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
+  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+
+/-- Positivity of the genuine inverse matrix supplies the frozen ellipticity parameters. -/
+theorem inverse_metric_ellipticity (g : ClosedSmoothRiemannianMetric 3 M)
+    (p : M) (anchor : (ClosedSmoothModel 3))
+    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target) :
+    let A := (inverseChartPullbackGramMatrixField g p anchor)⁻¹
+    A.IsHermitian ∧ ∃ lam Λ : ℝ, 0 < lam ∧ lam ≤ Λ ∧
+      (∀ v, lam * ‖v‖^2 ≤ matrixBilin A v v) ∧
+      (∀ v, matrixBilin A v v ≤ Λ * ‖v‖^2) := by
+  have hpos := inverseChartPullbackGramMatrix_posDef g p ⟨anchor, hanchor⟩
+  rw [inverseChartPullbackGramMatrix_eq_field] at hpos
+  exact ⟨hpos.inv.isHermitian, matrixBilin_ellipticity hpos.inv⟩
+
+
+
+/-- Smooth genuine inverse entries and the frozen solver assemble on a buffered chart. -/
+theorem exists_inverse_metric_chart_operator
+    (g : ClosedSmoothRiemannianMetric 3 M) (p : M) (anchor : (ClosedSmoothModel 3))
+    (hanchor : anchor ∈ (extChartAt (closedSmoothModelWithCorners 3) p).target)
+    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C ε₀ τ₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ 0 < τ₀ ∧
+    ∀ ξ : (ClosedSmoothModel 3) → ℝ, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
+      tsupport ξ ⊆ (extChartAt (closedSmoothModelWithCorners 3) p).target →
+      (∀ x, ξ x ∈ Icc 0 1) →
+      (∀ x ∈ tsupport ξ, ∀ i j,
+        |(inverseChartPullbackGramMatrixField g p x)⁻¹ i j -
+          (inverseChartPullbackGramMatrixField g p anchor)⁻¹ i j| ≤ ε₀) →
+      ∃ Λb : ℝ, 0 ≤ Λb ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → T ≤ τ₀ →
+        Λb * T ^ (α / 2) ≤ ε₀ →
+        ∃ S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+          ‖S‖ ≤ C ∧ ∀ f t, t ∈ Icc 0 T → ∀ x, ξ x = 1 →
+            (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+              (inverseChartPullbackGramMatrixField g p x)⁻¹ i j *
+                (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) := by
+  obtain ⟨hsym, lam, Λell, hlam, hlamΛ, hlo, hhi⟩ :=
+    inverse_metric_ellipticity g p anchor hanchor
+  obtain ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, hS⟩ :=
+    exists_chart_operator α hα hα1 lam Λell hlam hlamΛ
+  refine ⟨C, ε₀, τ₀, hC, hε₀, hτ₀, ?_⟩
+  intro ξ hξ hc hξU hξ01 hosc
+  obtain ⟨Λb, hΛb, hb⟩ := inverse_metric_oscillation_extension g p hα hα1
+    anchor hξ hc hξU hξ01 hε₀.le hosc
+  refine ⟨Λb, hΛb, ?_⟩
+  intro T hT _ hTτ hsmall
+  obtain ⟨b, heq, hsup, hholder⟩ := hb T
+  obtain ⟨S, hbound, _, hsolves⟩ := hS
+    (fun x => (inverseChartPullbackGramMatrixField g p x)⁻¹) anchor ξ
+    hsym hlo hhi T hT hTτ b Λb hsup hholder hsmall heq
+  exact ⟨S, hbound, hsolves⟩
+
+end Poincare.BufferedFrozenParabolicSolver
+
+noncomputable section
+open Set
+open scoped ContDiff
+namespace Poincare.BufferedFrozenParabolicSolver
+open ParabolicHolder ParabolicSolutionGraph
+
+/-- The coefficient extension leaves a transition-region gap. -/
+theorem cutoff_coefficient_gap (ψ a A : ℝ) :
+    a - A - ψ * (a - A) = (1 - ψ) * (a - A) := by ring
+
+/-- Agreement fails in a transition region whenever the coefficient has changed. -/
+theorem cutoff_coefficient_gap_ne_zero {ψ a A : ℝ} (hψ : ψ ≠ 1) (ha : a ≠ A) :
+    a - A - ψ * (a - A) ≠ 0 := by
+  rw [cutoff_coefficient_gap]
+  exact mul_ne_zero (sub_ne_zero.mpr hψ.symm) (sub_ne_zero.mpr ha)
+
+/-- The exact remaining principal residual retains the transition-region term. -/
+theorem nearFrozen_chart_residual {α T : ℝ}
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) (ψ : (ClosedSmoothModel 3) → ℝ)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ψ x * (a x i j - a anchor i j))
+    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
+      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∀ f t, t ∈ Icc 0 T → ∀ x,
+      (S f).ut (t,x) - (∑ i, ∑ j, a x i j * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
+        -(∑ i, ∑ j, (1 - ψ x) * (a x i j - a anchor i j) *
+          (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) := by
+  intro f t ht x
+  rw [hS f t ht x]
+  simp only [heq t ht x, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+
+
+set_option maxHeartbeats 1600000 in
+/-- The actual cutoff graph has both the principal transition error and the commutator. -/
+theorem exists_cutoff_chart_residual {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
+    (a : (ClosedSmoothModel 3) → Fin 3 → Fin 3 → ℝ) (anchor : (ClosedSmoothModel 3)) {ψ : (ClosedSmoothModel 3) → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (b : Fin 3 → Fin 3 → Y («E» := (ClosedSmoothModel 3)) α T ℝ)
+    (S : Y («E» := (ClosedSmoothModel 3)) α T ℝ →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T)
+    (heq : ∀ t ∈ Icc 0 T, ∀ x i j, b i j (t,x) = ψ x * (a x i j - a anchor i j))
+    (hS : ∀ f t, t ∈ Icc 0 T → ∀ x,
+      (S f).ut (t,x) = f (t,x) + ∑ i, ∑ j,
+        (a anchor i j + b i j (t,x)) * (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∃ C : Graph («E» := (ClosedSmoothModel 3)) α T →L[ℝ] Graph («E» := (ClosedSmoothModel 3)) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      ∀ f : Y («E» := (ClosedSmoothModel 3)) α T ℝ, (∀ p, ψ p.2 * f p = f p) →
+      ∀ t ∈ Icc 0 T, ∀ x,
+        (C (S f)).ut (t,x) -
+          (∑ i, ∑ j, a x i j * (C (S f)).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) - f (t,x) =
+        -ψ x * (∑ i, ∑ j, (1 - ψ x) * (a x i j - a anchor i j) *
+          (S f).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+        (∑ i, ∑ j, a x i j *
+          (fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+            (S f).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) +
+            (S f).u (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))) := by
+  obtain ⟨C, hu, hjets⟩ := ParabolicCutoffCommutator.exists_cutoff_operator hψ hc hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro f hf t ht x
+  obtain ⟨hut, _, hddu⟩ := hjets (S f) t ht x
+  rw [hut, hddu, hS f t ht x]
+  simp only [heq t ht x, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  have hf' := hf (t,x)
+  dsimp only at hf'
+  linear_combination hf'
+
+end Poincare.BufferedFrozenParabolicSolver
```

</details>
