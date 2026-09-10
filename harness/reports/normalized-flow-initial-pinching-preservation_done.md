# Normalized-flow initial pinching preservation

Date: 2026-09-10. Base: `cabb4900a2e73ed79c85b6ffc96a52facb64bb77`.
Branch: `worker/normalized-flow-initial-pinching-preservation`.
Verified proof head: `e1b5e62aec9ecf71fd44ac9bba4d2185ebd4f5d1`.

## Result

The exact third target of the survey's Appendix C `targets.lean` is proved as
`Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved`.
For every forward slice it gives

```lean
GlobalRicciEigenvalueFloor3 (gt t) (2 * ε₀ - 1 / 3) ∧
GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2)
```

The hypotheses are exactly the survey's: its manifold instances, all-real-time
joint C³ metric entries, the normalized equation on `Ici 0`, pointwise positive
initial scalar, `ε₀ ≤ 1/3`, and the initial eigenvalue floor. No positivity of
`ε₀`, negative-time scalar positivity, spatial regularity premise, evolution
predicate premise, integral estimate, or uniform scalar lower bound was added.

The optional Appendix C `residuals.lean` target is also proved as
`initial_pinching_improvement`, with exactly `1/6 < ε₀`, `ε₀ ≤ 1/3`,
`0 < δ`, `δ ≤ 1`, and admissibility for `2 * ε₀ - 1/3` in addition to the
same flow, regularity, initial positivity, and initial floor assumptions.
Its conclusion bounds the improved maximum by its initial maximum. It does
not claim convergence or a uniform rate.

All four new declarations compile and each has exactly
`[propext, Classical.choice, Quot.sound]`. Literal target expressions copied
from the survey were used as type ascriptions on both final theorems.
No blocking statement remains for this task.

## Proof and coefficient check

1. `scalarAt_pos_of_initial_scalar_pos` constructs the normalization primitive,
   obtains a positive initial scalar floor by compactness, and applies the
   existing exponential scalar comparison. Its positive comparison function
   proves pointwise positivity at each finite forward time.
2. `contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow` derives spatial C²
   time variation from joint C³ entries, then C² Ricci entries from the
   normalized equation. The existing norm and quotient regularity lemmas
   supply spatial C² of the ordinary quotient. This helper also omits the
   second-countability and simple-connectivity instances it does not use.
3. `initial_pinching_preserved` constructs continuity on `Icc 0 t ×ˢ univ`
   using the landed slab-local continuity theorem. The automatic normalized
   quotient evolution and spatial C² feed `hamilton_pinching_preserved_continuousOn`.
   The initial global eigenfloor bounds the initial maximum by the quadratic
   coefficient. Each later quotient lies below its maximum, which lies below
   the initial maximum. The landed pointwise conversion gives the degraded
   floor while retaining the better initial quotient coefficient.
4. `initial_pinching_improvement` reconstructs slab-local improved quotient
   continuity, spatial C², and the automatic normalized improved evolution.
   The proved degraded floor is positive under `1/6 < ε₀` and is at most
   `1/3`. These inputs feed `hamilton_pinching_improvement_continuousOn`.

The task's step 4 calls the displayed coefficient traceless. The frozen
conjunction and the actual definition of `GlobalPinchingQuotientBound3`
bound the ordinary quotient `|Ric|²/R²`. The landed
`globalPinchingQuotientBound_of_globalRicciEigenvalueFloor` produces exactly
`1 - 4 * ε₀ + 6 * ε₀^2` at time zero. This agrees with the survey's coefficient
calculation and its instruction to retain the initial coefficient. The
corresponding relative traceless bound is smaller by `1/3`; no altered
predicate or recomputation from the degraded coefficient was used.
The output does not preserve `ε₀` undegraded.

## Scope and handoff

Exactly one new production Lean file was added. No existing Lean file,
`Poincare.lean`, frozen contract, audit, mission, or ledger was edited. The
specified worker branch and one-module/report scope take precedence over the
general branch-naming and HANDOFF-edit guidance. This dated report supplies
the handoff; `HANDOFF.md` is unchanged. Worktree and base were checked live
before editing. No work was merged or marked accepted.

Each lemma was committed only after its focused compilation, dependency probe,
empty forbidden-token scan, and whitespace check. Proof commits are recorded
below. The only initial diagnostic was an unused-section-variable warning for
the spatial lemma; explicitly omitting those two instances removed it. No Lean
probe failed. The final file compiles without output.

First action for the orchestrator:

```sh
git diff cabb4900a2e73ed79c85b6ffc96a52facb64bb77..e1b5e62aec9ecf71fd44ac9bba4d2185ebd4f5d1 -- Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Independently rerun the focused gate and exact target/dependency probe, then
choose acceptance and import wiring. Root builds and integration audits were
not run by this worker.

## Exact target and dependency probe

The temporary probes concatenate the current new module source with commands;
they do not import a potentially stale compiled copy of the new module.
The scalar and spatial probes appended only the respective `#print axioms`
command to the source at that stage. The preservation probe appended its
literal survey target and all then-present dependency commands. The final
probe appends the following to the final file, with the module's ambient
variables redeclared as shown. Every invocation and its actual output is
recorded in the next section.

```lean
open Poincare
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]


#check (Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved (M := M) :
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon : ℝ),
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) → epsilon ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
  ∀ t ∈ Ici (0 : ℝ),
    GlobalRicciEigenvalueFloor3 (gt t) (2 * epsilon - 1/3) ∧
    GlobalPinchingQuotientBound3 (gt t) (1 - 4 * epsilon + 6 * epsilon^2))

#check (Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement (M := M) :
∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (epsilon0 delta : ℝ),
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) →
  1/6 < epsilon0 → epsilon0 ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon0 →
  0 < delta → delta ≤ 1 →
  delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon0 - 1/3) →
  ∀ t ∈ Ici (0 : ℝ), tracelessPinchingMaximumTrack gt 0 delta t ≤
    tracelessPinchingMaximumTrack gt 0 delta 0)
#print axioms Poincare.NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
#print axioms Poincare.NormalizedFlowInitialPinchingPreservation.contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
#print axioms Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
#print axioms Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement
```

## Command evidence

An empty output block means the command emitted no output. Ripgrep exit 1
with empty output is the required no-match result. Commands below were run
from the task worktree. Raw JSON records and temporary probe files remain in
`/tmp/normalized-flow-initial-pinching-preservation-evidence/`.

### 01-scalar-lean

```sh
env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
```

### 02-scalar-dependencies

```sh
env LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-initial-pinching-preservation-evidence/scalar-probe.lean
```

Exit code: `0`. Actual output:

```text
'Poincare.NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### 03-source-names

```sh
rg -n '^((protected |private |noncomputable )?theorem |noncomputable def |def |structure |class )?(.*\.)?(exists_normalizationPrimitive_of_normalizedRicciFlow|exists_pos_scalar_floor_of_forall_scalarAt_pos|globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree|satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three|normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three|ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow|contMDiffAt_two_ricciNormSqAt_of_ricci_entries|contMDiffAt_two_pinchingQuotientAt|continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three|satisfiesPinchingQuotientEvolutionAt|hamilton_pinching_preserved_continuousOn|exists_pinchingQuotientAt_isMaxOn|pinchingMaximumAt_eq_of_isMaxOn|pinchingQuotientAt_le_pinchingMaximumAt|globalPinchingQuotientBound_of_globalRicciEigenvalueFloor|eigenvalue_pinched_of_pinchingQuotientAt_le|hamilton_pinching_improvement_continuousOn|continuousOn_tracelessPinchingAt_timeShift_of_metricEntriesJointContDiffAt_three|contMDiffAt_two_tracelessPinchingAt_of_normalizedRicciFlow_joint_metric_entries_three|satisfiesTracelessPinchingImprovementEvolutionAt|GlobalRicciEigenvalueFloor3|GlobalPinchingQuotientBound3|pinchingMaximumTrack|tracelessPinchingMaximumTrack)( |$)' Poincare/Global
```

Exit code: `0`. Actual output:

```text
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay.lean:139:    (data.gt t).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:52:theorem satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:75:theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:257:theorem normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:153:def globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:101:theorem contMDiffAt_two_tracelessPinchingAt_of_normalizedRicciFlow_joint_metric_entries_three
Poincare/Global/MetricFlowJointRegularity.lean:320:theorem timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:179:    (data.gt t).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
Poincare/Global/ScalarEvolution.lean:4081:theorem exists_pinchingQuotientAt_isMaxOn
Poincare/Global/ScalarEvolution.lean:4098:noncomputable def pinchingMaximumTrack
Poincare/Global/ScalarEvolution.lean:4103:theorem pinchingMaximumAt_eq_of_isMaxOn
Poincare/Global/ScalarEvolution.lean:4119:theorem pinchingQuotientAt_le_pinchingMaximumAt
Poincare/Global/ScalarEvolution.lean:4216:noncomputable def tracelessPinchingMaximumTrack
Poincare/Global/ScalarEvolution.lean:5117:  exact (gt (t₀ + τ)).eigenvalue_pinched_of_pinchingQuotientAt_le
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:97:def GlobalRicciEigenvalueFloor3
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:111:def GlobalPinchingQuotientBound3
Poincare/Global/NormalizedFlowHamiltonPinchingQuotientFromEigenFloor.lean:39:    ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
Poincare/Global/ScalarVariation.lean:25135:theorem eigenvalue_pinched_of_pinchingQuotientAt_le
Poincare/Global/MetricFlowJointScalarTraceZoneBridge.lean:396:theorem continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowScalarRegularity.lean:44:theorem ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowScalarRegularity.lean:91:theorem scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/MetricFlowJointPinchingEvolution.lean:35:theorem contMDiffAt_two_ricciNormSqAt_of_ricci_entries
Poincare/Global/MetricFlowJointPinchingEvolution.lean:132:theorem contMDiffAt_two_pinchingQuotientAt
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1335:theorem continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1358:theorem continuousOn_tracelessPinchingAt_timeShift_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1552:theorem hamilton_pinching_preserved_continuousOn
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1851:theorem hamilton_pinching_improvement_continuousOn
Poincare/Global/HamiltonMeanFloorReduction.lean:66:theorem exists_normalizationPrimitive_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:27:theorem satisfiesPinchingQuotientEvolutionAt
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:160:theorem satisfiesTracelessPinchingImprovementEvolutionAt
```

### 04-scalar-scan

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `1`. Actual output:

```text
```

### 05-scalar-diff

```sh
git diff --check
```

Exit code: `0`. Actual output:

```text
```

### 06-spatial-lean

```sh
env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:59:0: warning: automatically included section variable(s) unused in theorem `Poincare.NormalizedFlowInitialPinchingPreservation.contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### 07-spatial-dependencies

```sh
env LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-initial-pinching-preservation-evidence/spatial-probe-2.lean
```

Exit code: `0`. Actual output:

```text
'Poincare.NormalizedFlowInitialPinchingPreservation.contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### 08-spatial-final-lean

```sh
env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
```

### 09-spatial-scan

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `1`. Actual output:

```text
```

### 10-spatial-diff

```sh
git diff --check
```

Exit code: `0`. Actual output:

```text
```

### 11-preservation-lean

```sh
env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
```

### 12-preservation-exact-dependencies

```sh
env LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-initial-pinching-preservation-evidence/preservation-exact-probe.lean
```

Exit code: `0`. Actual output:

```text
NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved : ∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (ε₀ : ℝ),
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt 0).scalarAt x) →
        ε₀ ≤ 1 / 3 →
          GlobalRicciEigenvalueFloor3 (gt 0) ε₀ →
            ∀ t ∈ Ici 0,
              GlobalRicciEigenvalueFloor3 (gt t) (2 * ε₀ - 1 / 3) ∧
                GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2)
'Poincare.NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NormalizedFlowInitialPinchingPreservation.contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### 13-foundation-names

```sh
rg -n '^(protected )?(theorem|lemma) (exp_pos|mul_pos|div_pos|continuous_iff_continuousAt|zero_add|LT.lt.trans|LE.le.trans|lt_of_lt_of_le|lt_of_le_of_lt|ne_of_gt|ne_of_lt)( |\[|\()' .lake/packages/mathlib/Mathlib
```

Exit code: `0`. Actual output:

```text
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:92:lemma lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:96:lemma lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:103:lemma ne_of_lt (h : a < b) : a ≠ b := fun he => absurd h (he ▸ lt_irrefl a)
.lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:464:lemma div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b ≠ ⊤) : 0 < a / b :=
.lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:656:protected lemma mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean:81:protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ ↦ rfl
.lake/packages/mathlib/Mathlib/Order/Basic.lean:938:protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 ≤ y.2) : x < y := by simp [lt_iff, *]
.lake/packages/mathlib/Mathlib/Order/Basic.lean:941:protected lemma lt_of_le_of_lt (h₁ : x.1 ≤ y.1) (h₂ : x.2 < y.2) : x < y := by simp [lt_iff, *]
.lake/packages/mathlib/Mathlib/Data/ENNReal/Inv.lean:221:protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
.lake/packages/mathlib/Mathlib/Data/ENNReal/Operations.lean:235:theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Notation.lean:382:theorem zero_add (o : ONote) : 0 + o = o :=
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/Arithmetic.lean:770:theorem div_pos {b c : Ordinal} (h : c ≠ 0) : 0 < b / c ↔ c ≤ b := by simp [lt_div h]
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:835:protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := fun ab =>
.lake/packages/mathlib/Mathlib/Topology/Continuous.lean:152:theorem continuous_iff_continuousAt : Continuous f ↔ ∀ x, ContinuousAt f x :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Canonical.lean:68:protected theorem mul_pos [NoZeroDivisors R] {a b : R} :
.lake/packages/mathlib/Mathlib/Data/Num/ZNum.lean:138:theorem zero_add (n : ZNum) : 0 + n = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Data/Num/Lemmas.lean:187:theorem zero_add (n : Num) : 0 + n = n := by cases n <;> rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:869:lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:599:protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f * g)
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:280:theorem exp_pos (x : ℝ) : 0 < exp x :=
.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/Basic.lean:198:protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
```

### 14-preservation-scan

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `1`. Actual output:

```text
```

### 15-preservation-diff

```sh
git diff --check
```

Exit code: `0`. Actual output:

```text
```

### 16-improvement-lean

```sh
env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
```

### 17-final-exact-dependencies

```sh
env LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-initial-pinching-preservation-evidence/final-exact-probe.lean
```

Exit code: `0`. Actual output:

```text
NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved : ∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (ε₀ : ℝ),
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt 0).scalarAt x) →
        ε₀ ≤ 1 / 3 →
          GlobalRicciEigenvalueFloor3 (gt 0) ε₀ →
            ∀ t ∈ Ici 0,
              GlobalRicciEigenvalueFloor3 (gt t) (2 * ε₀ - 1 / 3) ∧
                GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2)
NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement : ∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (ε₀ δ : ℝ),
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ t ∈ Ici 0, ∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t x) →
      (∀ (x : M), 0 < (gt 0).scalarAt x) →
        1 / 6 < ε₀ →
          ε₀ ≤ 1 / 3 →
            GlobalRicciEigenvalueFloor3 (gt 0) ε₀ →
              0 < δ →
                δ ≤ 1 →
                  δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * ε₀ - 1 / 3) →
                    ∀ t ∈ Ici 0, tracelessPinchingMaximumTrack gt 0 δ t ≤ tracelessPinchingMaximumTrack gt 0 δ 0
'Poincare.NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NormalizedFlowInitialPinchingPreservation.contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### 18-additional-names

```sh
rg -n '^(.*(def|structure|class|theorem|lemma) (ClosedSmoothRiemannianMetric|MetricEntriesJointContDiffAt|TimeVariationExtContMDiffAt|ricciVariationField|pinchedTracelessAdmissibleDelta3|IsClosedNormalizedRicciFlowSolutionAt|IsManifold|ContMDiffAt|HasDerivAt|ContinuousOn|Continuous|ConnectedSpace|SimplyConnectedSpace|T2Space|SecondCountableTopology|BorelSpace|CompactSpace|ClosedSmoothModel|closedSmoothModelWithCorners|SatisfiesPinchingQuotientEvolutionAt|SatisfiesTracelessPinchingImprovementEvolutionAt|scalarAt|pinchingQuotientAt|tracelessPinchingAt|meanScalar)( |$|\{)|alias mul_pos|  protected zero_add|@\[to_dual ne_of_gt\])' Poincare/Global .lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean .lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean .lake/packages/mathlib/Mathlib/Geometry/Manifold .lake/packages/mathlib/Mathlib/Topology .lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean
```

Exit code: `0`. Actual output:

```text
.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:115:class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:384:  protected zero_add : ∀ a : M, 0 + a = a
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:44:alias mul_pos := Left.mul_pos
.lake/packages/mathlib/Mathlib/Order/Defs/PartialOrder.lean:102:@[to_dual ne_of_gt]
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:785:class IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
.lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean:191:def ContinuousOn (f : X → Y) (s : Set X) : Prop :=
.lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean:282:class CompactSpace : Prop where
.lake/packages/mathlib/Mathlib/Topology/Defs/Basic.lean:149:structure Continuous (f : X → Y) : Prop where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:178:def ContMDiffAt (n : ℕ∞ω) (f : M → M') (x : M) :=
.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean:84:class T2Space (X : Type u) [TopologicalSpace X] : Prop where
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
.lake/packages/mathlib/Mathlib/Topology/Connected/Basic.lean:632:class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
Poincare/Global/Curvature.lean:159:noncomputable def scalarAt (x : M) : ℝ :=
Poincare/Global/RicciNorm.lean:177:noncomputable def pinchingQuotientAt (x : M) : ℝ :=
Poincare/Global/RicciNorm.lean:319:noncomputable def tracelessPinchingAt (x : M) (δ : ℝ) : ℝ :=
Poincare/Global/RicciNorm.lean:1546:noncomputable def pinchedTracelessAdmissibleDelta3 (ε : ℝ) : ℝ :=
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/ScalarVariation.lean:3136:noncomputable def ricciVariationField
Poincare/Global/ScalarVariation.lean:4560:def TimeVariationExtContMDiffAt
Poincare/Global/ScalarVariation.lean:25224:def SatisfiesPinchingQuotientEvolutionAt
Poincare/Global/ScalarVariation.lean:25256:def SatisfiesTracelessPinchingImprovementEvolutionAt
Poincare/Global/ScalarIntegral.lean:65:noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
```

### 19-final-scan

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `1`. Actual output:

```text
```

### 20-final-diff

```sh
git diff --check
```

Exit code: `0`. Actual output:

```text
```

### 21-final-declarations

```sh
rg -n '^theorem ' Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

Exit code: `0`. Actual output:

```text
30:theorem scalarAt_pos_of_initial_scalar_pos
60:theorem contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
76:theorem initial_pinching_preserved
123:theorem initial_pinching_improvement
```

### 22-proof-commits

```sh
git log --oneline cabb4900a2e73ed79c85b6ffc96a52facb64bb77..HEAD
```

Exit code: `0`. Actual output:

```text
e1b5e62a Prove forward improved pinching maximum bound from initial eigenvalue data
60087443 Preserve the initial Ricci quotient bound and degraded eigenvalue floor forward
7075b601 Derive spatial C2 pinching quotient regularity on normalized-flow slices
5ba87310 Prove forward scalar positivity from positive normalized-flow initial data
```

### 23-proof-scope

```sh
git diff --name-status cabb4900a2e73ed79c85b6ffc96a52facb64bb77..HEAD
```

Exit code: `0`. Actual output:

```text
A	Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
```

### 24-base-diff-check

```sh
git diff --check cabb4900a2e73ed79c85b6ffc96a52facb64bb77..HEAD
```

Exit code: `0`. Actual output:

```text
```

### 25-toolchain

```sh
lake env lean --version
```

Exit code: `0`. Actual output:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

## Verified final Lean diff

```diff
diff --git a/Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean b/Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
new file mode 100644
index 00000000..d626f391
--- /dev/null
+++ b/Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean
@@ -0,0 +1,157 @@
+import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
+import Poincare.Global.MetricFlowJointPinchingEvolution
+import Poincare.Global.HamiltonMeanFloorReduction
+import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
+
+/-!
+# Forward normalized-flow pinching from initial data
+
+Positive initial scalar curvature stays positive at every finite forward time.
+The initial Ricci quotient bound is preserved, giving the eigenvalue floor
+with coefficient `2 * ε₀ - 1/3`.
+-/
+
+set_option autoImplicit false
+noncomputable section
+open Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+universe u
+namespace Poincare.NormalizedFlowInitialPinchingPreservation
+
+variable {M : Type u} [TopologicalSpace M] [T2Space M]
+  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+local notation "I" => closedSmoothModelWithCorners 3
+
+/-- The exponential scalar comparison gives positivity on every forward slice. -/
+theorem scalarAt_pos_of_initial_scalar_pos
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
+    ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x := by
+  obtain ⟨P, hP, _, hd⟩ := exists_normalizationPrimitive_of_normalizedRicciFlow gt hflow hjoint
+  obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
+  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
+    continuous_iff_continuousAt.mpr fun p ↦
+      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
+  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
+  have hp := normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
+    (gt := gt) (t0 := 0) hrho (by simpa only [zero_add] using hs)
+    (fun t ht x ↦ by
+      simpa only [zero_add] using
+        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+          (x := x) (hflow t ht) hL)
+    (fun t ht x ↦ by
+      simpa only [zero_add] using scalarAt_contMDiffAt_two_of_normalizedRicciFlow
+        (hflow t ht) (hL.timeVariationEntries t) x)
+    P hP (by simpa only [zero_add] using hd) hlow
+  intro t ht x
+  have hpos : 0 < (rho / 2) * Real.exp (-(P t - P 0)) :=
+    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _)
+  exact hpos.trans (by simpa only [zero_add] using hp t ht x)
+
+omit [SecondCountableTopology M] [SimplyConnectedSpace M] in
+/-- Joint `C³` regularity and the normalized equation give spatial `C²`
+regularity of the ordinary Ricci quotient on a positive-scalar slice. -/
+theorem contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
+    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ}
+    (hjoint : ∀ x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hpos : ∀ x, 0 < (gt t).scalarAt x) (x : M) :
+    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t).pinchingQuotientAt y) x := by
+  have hEntries : ∀ y : M, TimeVariationExtContMDiffAt gt t y 2 := fun y ↦
+    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hjoint y)
+  have hRic := ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
+    hflow hEntries x
+  exact contMDiffAt_two_pinchingQuotientAt (gt t) x
+    (contMDiffAt_two_ricciNormSqAt_of_ricci_entries (gt t) x hRic)
+    (scalarAt_contMDiffAt_two_of_normalizedRicciFlow hflow hEntries x) (hpos x).ne'
+
+/-- Initial eigenvalue pinching preserves its Ricci quotient bound on the whole
+forward ray and yields the explicit degraded eigenvalue floor. -/
+theorem initial_pinching_preserved
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (ε₀ : ℝ)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x) (hεle : ε₀ ≤ 1 / 3)
+    (hfloor : GlobalRicciEigenvalueFloor3 (gt 0) ε₀) :
+    ∀ t ∈ Ici (0 : ℝ),
+      GlobalRicciEigenvalueFloor3 (gt t) (2 * ε₀ - 1 / 3) ∧
+      GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2) := by
+  have hpos := scalarAt_pos_of_initial_scalar_pos gt hjoint hflow hinit
+  have hQ₂ : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
+      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t).pinchingQuotientAt y) x :=
+    fun t ht x ↦ contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
+      (hjoint t) (hflow t ht) (hpos t ht) x
+  have hmax0 : pinchingMaximumTrack gt 0 0 ≤ 1 - 4 * ε₀ + 6 * ε₀ ^ 2 := by
+    obtain ⟨x, hx⟩ := exists_pinchingQuotientAt_isMaxOn (gt 0) (hQ₂ 0 (by simp))
+    have hbound := (gt 0).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
+      hinit hfloor x
+    simpa only [pinchingMaximumTrack, zero_add,
+      pinchingMaximumAt_eq_of_isMaxOn (gt 0) hx] using hbound
+  intro t ht
+  have hcont : ContinuousOn
+      (↿fun τ (x : M) ↦ (gt (0 + τ)).pinchingQuotientAt x)
+      (Icc (0 : ℝ) t ×ˢ (Set.univ : Set M)) :=
+    continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three
+      (fun τ _ x ↦ hjoint (0 + τ) x)
+      (fun τ hτ x ↦ by simpa only [zero_add] using (hpos τ hτ.1 x).ne')
+  have hpres := hamilton_pinching_preserved_continuousOn
+    (gt := gt) (t₀ := 0) (T := t) rfl ht hcont
+    (fun τ hτ x ↦ by simpa only [zero_add] using hQ₂ τ hτ.1 x)
+    (fun τ hτ x ↦ by
+      simpa only [zero_add] using
+        NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt
+          hjoint (hflow τ hτ.1) (hpos τ hτ.1) x)
+  have hbound : GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2) := by
+    intro x
+    have hpoint : (gt t).pinchingQuotientAt x ≤ pinchingMaximumTrack gt 0 t := by
+      simpa only [pinchingMaximumTrack, zero_add] using
+        pinchingQuotientAt_le_pinchingMaximumAt (gt t) (hQ₂ t ht) x
+    exact hpoint.trans ((hpres t ⟨ht, le_rfl⟩).trans hmax0)
+  refine ⟨?_, hbound⟩
+  intro x b μ hEig
+  exact (gt t).eigenvalue_pinched_of_pinchingQuotientAt_le
+    hεle (hpos t ht x) (hbound x) b μ hEig
+
+/-- With a positive degraded floor and admissible exponent, the improved
+traceless quotient maximum stays below its initial maximum. -/
+theorem initial_pinching_improvement
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (ε₀ δ : ℝ)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
+    (hεpos : 1 / 6 < ε₀) (hεle : ε₀ ≤ 1 / 3)
+    (hfloor : GlobalRicciEigenvalueFloor3 (gt 0) ε₀)
+    (hδpos : 0 < δ) (hδle : δ ≤ 1)
+    (hδadm : δ ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * ε₀ - 1 / 3)) :
+    ∀ t ∈ Ici (0 : ℝ), tracelessPinchingMaximumTrack gt 0 δ t ≤
+      tracelessPinchingMaximumTrack gt 0 δ 0 := by
+  have hpos := scalarAt_pos_of_initial_scalar_pos gt hjoint hflow hinit
+  have hpres := initial_pinching_preserved gt ε₀ hjoint hflow hinit hεle hfloor
+  intro t ht
+  have hcont : ContinuousOn
+      (↿fun τ (x : M) ↦ (gt (0 + τ)).tracelessPinchingAt x δ)
+      (Icc (0 : ℝ) t ×ˢ (Set.univ : Set M)) :=
+    continuousOn_tracelessPinchingAt_timeShift_of_metricEntriesJointContDiffAt_three
+      (fun τ _ x ↦ hjoint (0 + τ) x)
+      (fun τ hτ x ↦ by simpa only [zero_add] using hpos τ hτ.1 x)
+  exact hamilton_pinching_improvement_continuousOn
+    (gt := gt) (t₀ := 0) (T := t) (ε := 2 * ε₀ - 1 / 3) (δ := δ)
+    rfl ht (by linarith) (by linarith) hδpos.le hδadm hcont
+    (fun τ hτ x ↦ by
+      simpa only [zero_add] using
+        contMDiffAt_two_tracelessPinchingAt_of_normalizedRicciFlow_joint_metric_entries_three
+          x δ (hflow τ hτ.1) (hjoint τ) (hpos τ hτ.1))
+    (fun τ hτ x ↦ by
+      simpa only [zero_add] using
+        NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt
+          hjoint (hflow τ hτ.1) (hpos τ hτ.1) hδpos hδle x)
+    (fun τ hτ ↦ by simpa only [zero_add] using (hpres τ hτ.1).1)
+    t ⟨ht, le_rfl⟩
+
+end Poincare.NormalizedFlowInitialPinchingPreservation
```
