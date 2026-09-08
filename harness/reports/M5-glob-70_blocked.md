# M5-glob-70 blocked: preferred-chart source membership obstructs H1

Date: 2026-09-07.
Base: `d08f4a5252b0d14788d4558afb669b6f3ed8d19d`.
Branch: `worker/M5-glob-70`.
Worktree: `/private/tmp/poincare-workers/M5-glob-70`.

## Result and stop classification

The frozen theorem
`fixedChartLocalGenericDataPersistence_of_constantCurvature` is **not proved**
and is not declared. H1 remains open. This attempt invokes Worker Contract
rule 2, the instruction to stop and report a suspected invalid frozen
statement. It does not claim the positive partial-result stop condition.

The new module contains ten verified theorems. They prove a necessary
preferred-chart source condition and construct a compatible smooth chart
selection on which the persistence conclusion fails for every metric. This
is a statement-validity obstruction, before any derivative or target-anchor
estimate is considered.

The module does **not** formally transport a constant-curvature metric to the
reselected charted structure. It therefore does not claim a completed Lean
counterexample to the frozen curvature implication. No substitute target,
extra assumption on the frozen theorem, or `target_of_...` wrapper was added.
The next step is to resolve this statement issue, not to move the whole
positive conclusion into a premise.

Only this new Lean file and this report are changed. `HANDOFF.md`, every
existing Lean file, root imports, and mission records remain at the base.
The dated handoff is recorded below because the task's file scope excludes
editing `HANDOFF.md`.

## Verified obstruction

The exact necessary condition is the new Lean definition:

```lean
def PreferredChartSourcePersistence (x₀ : M) : Prop :=
  {y : M | x₀ ∈ (extChartAt I y).source} ∈ 𝓝 x₀
```

`preferredChartSourcePersistence_of_universalSuccessorDataNeighborhood`
pulls the H1 neighborhood back along the continuous map
`y ↦ ((y, p₀), x₀)`. At every point in that pullback, it obtains an actual
alignment using `CartanMap.tangentAlignment_nonempty`, obtains an actual
`DifferentialInducedSuccessor.Data`, and uses its
`source_mem_oldChart` field. This is not a vacuous universal-alignment
argument. Through the existing fixed-chart-to-H1 theorem, failure of this
source condition rules out the frozen conclusion.

The chart construction is explicit. For a fixed center `x₀`, let

```text
U_y = univ          if y = x₀,
U_y = {x₀}ᶜ         otherwise,
c_y = (chartAt E y).restr U_y.
```

In a T1 space, each `U_y` is open and contains `y`. Each `c_y` therefore is a
valid chart containing its own anchor, and each is in the original smooth
maximal atlas. `centerAvoidingChartedSpace` keeps that maximal atlas and
selects `c_y` at `y`; `centerAvoidingChartedSpace_isManifold` verifies the
smooth manifold instance from compatibility of the original maximal atlas.
No topology changes.

Lean proves

```lean
{y : M | x₀ ∈ (centerAvoidingChart x₀ y).source} = {x₀}
```

At a nonisolated center, the singleton is not a neighborhood. The strongest
new theorem is:

```lean
theorem not_fixedChartLocalGenericDataPersistence_centerAvoiding
    (x₀ : M) [(𝓝[≠] x₀).NeBot] (p₀ : RoundSphere3) :
    let smooth := centerAvoidingChartedSpace_isManifold x₀
    letI := centerAvoidingChartedSpace x₀
    letI := smooth
    ∀ g : ClosedSmoothRiemannianMetric 3 M,
      ¬ FixedChartLocalGenericDataPersistence g
```

The general context is exactly the existing smooth three-dimensional model,
with `T1Space M` for the open chart restrictions. The nonisolated hypothesis
is used to exclude an open singleton. Compactness and connectedness are not
needed for the obstruction. They persist when the original topology is kept.
A separate checked probe below establishes nonisolation on `RoundSphere3`.

Mathematically, restricting charts inside the same smooth maximal atlas
preserves the smooth structure, so the round metric should transport to this
reselection of the sphere. Proving the repository's metric and curvature
transport statements is the one missing step for a full formal counterexample.

## Why the proposed open-set proof stops

The frozen task says every `Data` field is open or moves continuously with
`(y, q, z)`. `source_mem_oldChart` is already a counterexample to that
inference. For each fixed `y`, `(extChartAt I y).source` is open in `z`, but
the selected chart source has no joint regularity in `y`.

Mathlib's `ChartedSpace` definition in
`.lake/packages/mathlib/Mathlib/Geometry/Manifold/ChartedSpace.lean:139`
requires only an atlas, a selected chart at each point, membership of that
point in its selected source, and membership of that chart in the atlas.
`IsManifold` imposes compatibility of chart transitions, not continuity of
that selection. The construction above satisfies both requirements.

The required fixed-anchor facts were checked against the actual source and
with `#check`:

- `exists_open_fixedChartCenter_genericSuccessorDataPatch_of_curvature` has
  fixed `(x₀, p₀)` before the endpoint patch and alignment quantifiers.
- `exists_open_vertical_genericSuccessorDataPatch_of_curvature` supplies an
  open endpoint patch for fixed source and target anchors.
- `DifferentialInducedSuccessor.exists_data_on_punctured_ball` and
  `DifferentialSuccessorZero.exists_data_on_ball` keep membership in the
  predecessor's strict source as a hypothesis.
- `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`
  quantifies fixed `(x₀, p₀)` before its radius and time; it is uniform over
  alignment, not over moving preferred charts.
- `CartanSourceExponentialLocalFamilyTransitionAgreement.lean` explicitly
  retains moving-anchor continuity and endpoint-agreement premises.

The fixed-chart product inverse does not remove the preferred-chart source
field from `Data`. No choice of a positive controlled radius can repair the
obstruction: any successful controlled locus would imply H1 and hence the
neighborhood condition contradicted above. The existing center and vertical
patch results are consistent with this counterexample to joint openness.

## Acceptance commands and actual outputs

Final module SHA-256: `41e47ca4c4f91d4ad4c668865bc7ea56219ecb0a74e1df26efebf7a51bcf2b0c`.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartSuccessorDataPersistence
```

Exit `0`. Final lines, after replayed warnings from unchanged dependencies:

```text
✔ [3585/3585] Built Poincare.Global.FixedChartSuccessorDataPersistence (12s)
Build completed successfully (3585 jobs).
```

The new module has no warnings. Full build output is preserved in
`/tmp/M5-glob-70-build-2.log`.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartSuccessorDataPersistence.lean
```

Exit `0`, empty stdout/stderr, preserved in
`/tmp/M5-glob-70-lean-final.log`.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartSuccessorDataPersistence.lean
grep -nE '\b(sorry|admit)\b|^\s*axiom\b|native_decide' Poincare/Global/FixedChartSuccessorDataPersistence.lean
```

Both have empty output and exit `1`, the expected no-match status.

Every new theorem was probed, using a task-specific `/tmp` filename to avoid
colliding with the other workers' probes:

```lean
import Poincare.Global.FixedChartSuccessorDataPersistence
#print axioms Poincare.FixedChartSuccessorDataPersistence.preferredChartSourcePersistence_of_universalSuccessorDataNeighborhood
#print axioms Poincare.FixedChartSuccessorDataPersistence.not_fixedChartLocalGenericDataPersistence_of_not_preferredChartSourcePersistence
#print axioms Poincare.FixedChartSuccessorDataPersistence.isOpen_centerAvoidingSet
#print axioms Poincare.FixedChartSuccessorDataPersistence.self_mem_centerAvoidingChart_source
#print axioms Poincare.FixedChartSuccessorDataPersistence.center_mem_centerAvoidingChart_source_iff
#print axioms Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChart_mem_maximalAtlas
#print axioms Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChartedSpace_isManifold
#print axioms Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChart_source_slice
#print axioms Poincare.FixedChartSuccessorDataPersistence.not_preferredChartSourcePersistence_centerAvoiding
#print axioms Poincare.FixedChartSuccessorDataPersistence.not_fixedChartLocalGenericDataPersistence_centerAvoiding
```

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/M5-glob-70-ax.lean
```

Exit `0`. Actual output:

```text
'Poincare.FixedChartSuccessorDataPersistence.preferredChartSourcePersistence_of_universalSuccessorDataNeighborhood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.not_fixedChartLocalGenericDataPersistence_of_not_preferredChartSourcePersistence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.isOpen_centerAvoidingSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.self_mem_centerAvoidingChart_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.center_mem_centerAvoidingChart_source_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChart_mem_maximalAtlas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChartedSpace_isManifold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChart_source_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.not_preferredChartSourcePersistence_centerAvoiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartSuccessorDataPersistence.not_fixedChartLocalGenericDataPersistence_centerAvoiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Every footprint is exactly `[propext, Classical.choice, Quot.sound]`.

The concrete sphere nonisolation probe was:

```lean
import Poincare.Global.FixedChartSuccessorDataPersistence
open Poincare Filter
open scoped Topology Manifold ContDiff
#check ne_neg_of_mem_unit_sphere
example (p : RoundSphere3) : (𝓝[≠] p).NeBot := by
  letI : Nontrivial RoundSphere3 := ⟨⟨p, -p, ne_neg_of_mem_unit_sphere ℝ p⟩⟩
  infer_instance
```

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/M5-glob-70-sphere-probe-2.lean
```

Exit `0`. Actual output:

```text
ne_neg_of_mem_unit_sphere.{u_1, u_3} (𝕜 : Type u_1) {E : Type u_3} [NormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CharZero 𝕜] (x : ↑(Metric.sphere 0 1)) : x ≠ -x
```

`git diff --check` returned `0` with empty output. The staged diff is checked
again before commit. No root integration or mission-acceptance gate is claimed.

## Failed attempts and retained evidence

Direct Lean attempt 1 exited `1`: the set-valued conditional needed a local
classical decidability instance, and the reselected `IsManifold` proof needed
explicit separation of old and new charted-space instances.

Direct Lean attempt 2 exited `1`: the remaining smooth-instance constructor
used the ambient charted-space instance, and `intro` encountered the outer
`let` before the metric quantifier. These were fixed by installing the new
charted structure after capturing the original compatibility proof and by
reducing the statement's local definitions before introducing the metric.

Direct Lean attempt 3 exited `0` with two unused-section-variable warnings.
Removing those variables was followed by an initially failed Lake build:
the `omit` directive had been placed after a declaration doc comment. That
syntax error was fixed, and the final Lake build and direct Lean check above
both exited `0`.

An initial sphere probe exited `1` because the imported instance graph did not
supply `Nontrivial RoundSphere3`. The passing probe above constructs that
instance from a point and its antipode. This was a probe failure, not evidence
that the sphere has isolated points.

Full scratch outputs are retained under `/tmp/M5-glob-70-*`. Complete failed
changed-module compiler outputs are copied below. The proof diff is retained
at `/tmp/M5-glob-70-proof.patch`, and the committed diff is recoverable with:

```sh
git diff d08f4a5252b0d14788d4558afb669b6f3ed8d19d worker/M5-glob-70 -- Poincare/Global/FixedChartSuccessorDataPersistence.lean
```

## Handoff

The target has not been weakened or silently reinterpreted. Do not mark
`successor-data-neighborhood` accepted from this module.

Exact first action: freeze and prove a transport task constructing
`g : ClosedSmoothRiemannianMetric 3 RoundSphere3` with
`HasConstantSectionalCurvature3 g 1` under
`centerAvoidingChartedSpace p`, using the smooth instance proved here.
Together with `not_fixedChartLocalGenericDataPersistence_centerAvoiding` and
the checked sphere nonisolation argument, that yields a full Lean refutation
of the universally charted frozen claim. Any change to H1 or to the permitted
chart-selection hypotheses must then be an explicit orchestrator-reviewed
statement correction.

## Direct Lean attempt 1 output

```text
Poincare/Global/FixedChartSuccessorDataPersistence.lean:78:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (y = x₀)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FixedChartSuccessorDataPersistence.lean:81:39: error: unsolved goals
case pos
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ y : M
h : y = x₀
⊢ IsOpen (sorry ())

case neg
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ y : M
h : ¬y = x₀
⊢ IsOpen (sorry ())
Poincare/Global/FixedChartSuccessorDataPersistence.lean:84:10: warning: declaration uses `sorry`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:84:29: warning: This simp argument is unused:
  h

Hint: Omit it from the simp argument list.
  simp [centerAvoidingSet, h̵,̵ ̵isOpen_compl_singleton]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:84:32: warning: This simp argument is unused:
  isOpen_compl_singleton

Hint: Omit it from the simp argument list.
  simp [centerAvoidingSet, h,̵ ̵i̵s̵O̵p̵e̵n̵_̵c̵o̵m̵p̵l̵_̵s̵i̵n̵g̵l̵e̵t̵o̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:91:45: error: unsolved goals
case pos
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ y : M
h : y = x₀
⊢ x₀ ∈ sorry ()

case neg
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ y : M
h : ¬y = x₀
⊢ y ∈ sorry ()
Poincare/Global/FixedChartSuccessorDataPersistence.lean:96:32: warning: declaration uses `sorry`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:104:2: error: unsolved goals
case pos
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ : M
⊢ x₀ ∈ sorry ()
Poincare/Global/FixedChartSuccessorDataPersistence.lean:106:2: error: unsolved goals
case neg
M : Type u
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : T1Space M
x₀ y : M
h : ¬y = x₀
⊢ x₀ ∈ (chartAt E y).source → x₀ ∉ sorry ()
Poincare/Global/FixedChartSuccessorDataPersistence.lean:105:10: warning: declaration uses `sorry`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:114:0: warning: Definition `Poincare.FixedChartSuccessorDataPersistence.centerAvoidingChartedSpace` of class type must be marked with `@[reducible]` or `@[implicit_reducible]`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:129:4: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this
inferred
  inst✝²
Poincare/Global/FixedChartSuccessorDataPersistence.lean:142:12: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FixedChartSuccessorDataPersistence.lean:144:2: error: 'change' tactic failed, pattern
  {y | x₀ ∈ (centerAvoidingChart x₀ y).source} ∉ 𝓝 x₀
is not definitionally equal to target
  ¬PreferredChartSourcePersistence x₀
Poincare/Global/FixedChartSuccessorDataPersistence.lean:158:12: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FixedChartSuccessorDataPersistence.lean:159:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FixedChartSuccessorDataPersistence.lean:162:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/FixedChartSuccessorDataPersistence.lean:165:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

## Direct Lean attempt 2 output

```text
Poincare/Global/FixedChartSuccessorDataPersistence.lean:81:0: warning: automatically included section variable(s) unused in theorem `Poincare.FixedChartSuccessorDataPersistence.isOpen_centerAvoidingSet`:
  [ChartedSpace E M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ChartedSpace E M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:85:32: warning: This simp argument is unused:
  isOpen_compl_singleton

Hint: Omit it from the simp argument list.
  simp [centerAvoidingSet, h,̵ ̵i̵s̵O̵p̵e̵n̵_̵c̵o̵m̵p̵l̵_̵s̵i̵n̵g̵l̵e̵t̵o̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FixedChartSuccessorDataPersistence.lean:134:8: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  inst✝²
inferred
  centerAvoidingChartedSpace x₀
Poincare/Global/FixedChartSuccessorDataPersistence.lean:173:4: error: Application type mismatch: The argument
  g
has type
  IsManifold I ∞ M
of sort `Prop` but is expected to have type
  ClosedSmoothRiemannianMetric 3 ?m.80
of sort `Type ?u.18928.353` in the application
  not_fixedChartLocalGenericDataPersistence_of_not_preferredChartSourcePersistence g
```

## Initial sphere probe output

```text
Metric.sphere.compactSpace 0 1
PathConnectedSpace.connectedSpace
Subtype.t1Space
/tmp/M5-glob-70-sphere-probe.lean:7:47: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  (𝓝[≠] p).NeBot

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare.FixedChartSuccessorDataPersistence.not_fixedChartLocalGenericDataPersistence_centerAvoiding.{u} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [T1Space M] (x₀ : M) [(𝓝[≠] x₀).NeBot] (p₀ : RoundSphere3) :
  have smooth := ⋯;
  ∀ (g : ClosedSmoothRiemannianMetric 3 M),
    ¬CartanGenericSuccessorDataLocalCover.FixedChartLocalGenericDataPersistence g
Poincare.FixedChartSuccessorDataPersistence.PreferredChartSourcePersistence.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] (x₀ : M) : Prop
```

## First Lake build failure output

```text
✖ [3585/3585] Building Poincare.Global.FixedChartSuccessorDataPersistence (11s)
trace: .> LEAN_PATH=/private/tmp/poincare-workers/M5-glob-70/.lake/packages/Cli/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/batteries/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/Qq/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/aesop/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/proofwidgets/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/importGraph/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/plausible/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/packages/mathlib/.lake/build/lib/lean:/private/tmp/poincare-workers/M5-glob-70/.lake/build/lib/lean /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean /private/tmp/poincare-workers/M5-glob-70/Poincare/Global/FixedChartSuccessorDataPersistence.lean -o /private/tmp/poincare-workers/M5-glob-70/.lake/build/lib/lean/Poincare/Global/FixedChartSuccessorDataPersistence.olean -i /private/tmp/poincare-workers/M5-glob-70/.lake/build/lib/lean/Poincare/Global/FixedChartSuccessorDataPersistence.ilean -c /private/tmp/poincare-workers/M5-glob-70/.lake/build/ir/Poincare/Global/FixedChartSuccessorDataPersistence.c --setup /private/tmp/poincare-workers/M5-glob-70/.lake/build/ir/Poincare/Global/FixedChartSuccessorDataPersistence.setup.json --json
error: Poincare/Global/FixedChartSuccessorDataPersistence.lean:140:71: unexpected token 'omit'; expected 'lemma'
error: Lean exited with code 1
Some required targets logged failures:
- Poincare.Global.FixedChartSuccessorDataPersistence
error: build failed
```
