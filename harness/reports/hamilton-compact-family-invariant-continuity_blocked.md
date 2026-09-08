# Compact-family invariant continuity: verified partial result

Date: 2026-09-08. Base: `b358db205a55844fa09cf253630ec4cc6525d406`.
Branch: `worker/hamilton-compact-family-invariant-continuity`.
Proof head: `cdd5d5ef5623bd57fb546159e749e62a5bcc21dc`.

Two of the three requested conclusions are proved: joint continuity of intrinsic scalar curvature and squared traceless Ricci. The results work in every dimension and for any topological parameter space, so they apply to the task's compact three-dimensional family without extra assumptions. Weak continuity of the finite volume measure remains unproved in this attempt. The full target, jet-form core, its conversion to the original core, and its Hamilton and universal endpoints are not added. This uses the task's explicit two-conclusion partial-result stop condition; it does not assert that the remaining implication is false.

Only the new `Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean` and this report are added. Existing Lean files, root imports, frozen contracts, HANDOFF, tasks, missions and ledgers are unchanged. The task-specific branch and file scope override the general branch-prefix and HANDOFF-edit guidance. The initial git status was clean on the named worker branch at the recorded base; the worktree inventory identified this isolated checkout. The toolchain is `leanprover/lean4:v4.30.0-rc2`; pinned Mathlib is `7175569c842f9164564bd76ff8b207e7b4705522`.

## 1. Proved declarations

All four theorems are in `Poincare.HamiltonCompactFamilyInvariantContinuity`.

- `continuousAt_scalarAt_of_ricciJet` contracts the continuous inverse coefficients and Ricci entries, then transfers the coordinate scalar trace to the intrinsic scalar on a common cutoff-one chart neighborhood.
- `continuousAt_ricciNormSqAt_of_ricciJet` performs the four-index contraction and the corresponding intrinsic squared-norm transfer.
- `curvatureContinuity_of_continuous` derives scalar and squared traceless-Ricci continuity from continuity of the metric family in the already landed scalar third-jet topology.
- `curvatureContinuity_of_thirdJetProfiles_continuous` derives the same pair directly from exactly the task's scalar profile hypothesis.

The first two proofs use the landed coordinate identities on the constant real flow associated with each individual metric. Those identities require no parameter regularity. The continuity proof itself takes place on `K × E` and `K × M`, with no derivative on K, no parameterization by real time, and no extension of the family's domain. The third proof subtracts scalar squared divided by n from the squared Ricci norm. Neither compactness nor connectedness is needed for these curvature conclusions.

The local topology instance uses the existing `closedSmoothRiemannianMetricEntryThirdJetTopology`; it is local to the section, introduces no analytic premise, and changes no measure topology. Its compiler-generated declaration is included in the five-declaration axiom scan.

Here `E` denotes `ClosedSmoothModel n`. Strongest compiled partial theorem, with section variables `[TopologicalSpace M] [T2Space M] [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) ∞ M]`:

```lean
theorem curvatureContinuity_of_thirdJetProfiles_continuous
    (K : Type v) [TopologicalSpace K]
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot n M,
      Continuous (fun p : K × E ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
    Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2) := by
  letI : TopologicalSpace (ClosedSmoothRiemannianMetric n M) :=
    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
  exact curvatureContinuity_of_continuous metric
    (continuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous hjet)

```

The separate `target-partial.lean` probe instantiates this at n = 3 under every original manifold assumption and `[CompactSpace K]`. It compiles with the unchanged hjet and exactly the last two original conclusions.

## 2. Exact remaining target and attempted measure routes

With the task's manifold section variables, the still-unproved implication is:

```lean
(K : Type v) [TopologicalSpace K] [CompactSpace K]
(metric : K → ClosedSmoothRiemannianMetric 3 M)
(hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
  Continuous (fun p : K × ClosedSmoothModel 3 ↦
    metricEntryThirdJetProfile (metric p.1) slot p.2))
⊢ Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
```

The codomain is the original weak topology on `MeasureTheory.FiniteMeasure M`. The scratch measure attempt applies `FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral` and unfolds only the finite-measure coercion. Lean accepts that reduction and stops at the following exact goal for an arbitrary `f : C(M, ℝ)`:

```lean
⊢ Continuous fun k => ∫ (x : M), f x ∂volumeMeasure (metric k)
```

Actual unsolved-goal output, including the retained hjet, is in the appendix. This is a failed proof attempt, not an exported declaration or an additional hypothesis in the new module.

The inspected routes were:

1. The named moving-integral continuity theorem and the mean-energy pair theorem already require continuous finite measures. They consume the missing conclusion and cannot produce it. The real-time curvature theorem supplies the coordinate proof pattern used above, but it supplies no arbitrary-family measure theorem.
2. The finite atlas has a proved area formula and each individual inverse-chart density is integrable. The source cover consists of genuine open chart sources. Its disjointized `coordinateDomain` pieces are measurable subsets of chart targets; the cover record contains no compactness or compact-closure certificate for these pieces. Thus an extreme-value argument on `K × coordinateDomain i` is not justified by the supplied compactness assumptions.
3. The chart-density comparison theorem assumes relative density bounds. It does not construct them for a moving family. A chart-invariant density ratio against a fixed reference metric, or a uniform metric comparison on a compact spatial cover, could supply a useful integrable envelope. This attempt does not prove that comparison or the ensuing parameter-integral continuity. Spatial density continuity for each fixed metric and separate integrability do not alone complete the dominated-convergence argument.

The unresolved step is therefore weak volume-measure continuity from hjet, not either curvature coordinate-to-intrinsic transfer. No density domination assumption has been inserted into the target, and no core with the original three continuity clauses merely renamed has been exported. Existence of a compact family continuous in the jet topology also remains an input to any future Hamilton existence result.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean
```

For continuation, prove the displayed continuous-test-integral implication from hjet. Then combine it with the two verified curvature clauses before defining the requested jet-form core and its endpoint adapters.

## 3. Commits and gates

Each theorem was committed after its direct module compilation and individual axiom probe passed:

```text
c31b9e3e Prove scalar curvature continuity for arbitrary metric parameters
c7b78e1b Prove squared Ricci norm continuity for arbitrary metric parameters
d3662b5e Derive intrinsic curvature continuity in the third-jet topology
cdd5d5ef Prove both curvature clauses from joint scalar third-jet profiles
```

The final direct module check exits 0 with no compiler output. The focused Lake build exits 0, completing 3861 jobs. It replays pre-existing dependency warnings and diagnostic output; the new module builds without warnings. The forbidden-token scan is empty, exit 1 as expected for no rg matches. All five declarations, including the local topology instance, have exactly `[propext, Classical.choice, Quot.sound]`, checked by an exhaustive module scan and actual `#print axioms`. The exact-hypothesis partial-target probe and `git diff --check` pass.

No full root build, root audit, merge, or task acceptance is claimed. Those belong to independent orchestrator review. The final proof diff is preserved at `/tmp/hamilton-compact-family-evidence/final.diff` and durably by the four commits. Probe sources, successful and failed compiler output, and the full focused-build log remain in that directory. The relevant actual outputs are also embedded below.

## Appendix A. Actual proof and gate output

The single-theorem axiom probes concatenate the then-current source with the named `#print axioms` directive. They do not import a stale compiled copy of the new module. The final module scan imports the successfully built module and checks the closure of every noninternal declaration assigned to its module index.

### scalar-03

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 0
```

### scalar-axioms

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/scalar-axioms.lean
'Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_scalarAt_of_ricciJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### ricci-02

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 0
```

### ricci-axioms

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/ricci-axioms.lean
'Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_ricciNormSqAt_of_ricciJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### topology-01

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 0
```

### topology-axioms

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/topology-axioms.lean
'Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### profiles-01

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 0
```

### profiles-axioms

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/profiles-axioms.lean
'Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### target-partial

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/target-partial.lean

EXIT 0
```

### final-token-scan

```text
$ rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 1
```

### profiles-diff

```text
$ git diff --check

EXIT 0
```

### module-scan

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/module-scan.lean
DECL Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_ricciNormSqAt_of_ricciJet
'Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_ricciNormSqAt_of_ricciJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonCompactFamilyInvariantContinuity.instTopologicalSpaceClosedSmoothRiemannianMetric
'Poincare.HamiltonCompactFamilyInvariantContinuity.instTopologicalSpaceClosedSmoothRiemannianMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_continuous
'Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_scalarAt_of_ricciJet
'Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_scalarAt_of_ricciJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous
'Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_CLOSURES_PASS declarations=5
Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_scalarAt_of_ricciJet.{u, v} {n : ℕ} {M : Type u}
  {K : Type v} [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [TopologicalSpace K]
  {metric : K → Poincare.ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
  (h : Poincare.MetricFamilyRicciJetChartContinuousAt metric k₀ x) :
  ContinuousAt (fun p => (metric p.1).scalarAt p.2) (k₀, x)
Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_ricciNormSqAt_of_ricciJet.{u, v} {n : ℕ} {M : Type u}
  {K : Type v} [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [TopologicalSpace K]
  {metric : K → Poincare.ClosedSmoothRiemannianMetric n M} {k₀ : K} {x : M}
  (h : Poincare.MetricFamilyRicciJetChartContinuousAt metric k₀ x) :
  ContinuousAt (fun p => (metric p.1).ricciNormSqAt p.2) (k₀, x)
Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_continuous.{u, v} {n : ℕ} {M : Type u}
  {K : Type v} [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [TopologicalSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric n M) (hmetric : Continuous metric) :
  (Continuous fun p => (metric p.1).scalarAt p.2) ∧ Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2
Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous.{u, v} {n : ℕ}
  {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (K : Type v) [TopologicalSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric n M)
  (hjet :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot n M),
      Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) :
  (Continuous fun p => (metric p.1).scalarAt p.2) ∧ Continuous fun p => (metric p.1).tracelessRicciNormSqAt p.2

EXIT 0
```

### anonymous-instance-source

```text
$ rg -n 'local instance|closedSmoothRiemannianMetricEntryThirdJetTopology' Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean
188:local instance : TopologicalSpace (ClosedSmoothRiemannianMetric n M) :=
189:  closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)
226:    closedSmoothRiemannianMetricEntryThirdJetTopology (n := n) (M := M)

EXIT 0
```

### final-state

```text
$ git status --short --branch; git rev-parse HEAD; git log --oneline b358db205a55844fa09cf253630ec4cc6525d406..HEAD; git diff --stat b358db205a55844fa09cf253630ec4cc6525d406..HEAD; git diff --check b358db205a55844fa09cf253630ec4cc6525d406..HEAD
## worker/hamilton-compact-family-invariant-continuity
cdd5d5ef5623bd57fb546159e749e62a5bcc21dc
cdd5d5ef Prove both curvature clauses from joint scalar third-jet profiles
d3662b5e Derive intrinsic curvature continuity in the third-jet topology
c7b78e1b Prove squared Ricci norm continuity for arbitrary metric parameters
c31b9e3e Prove scalar curvature continuity for arbitrary metric parameters
 .../HamiltonCompactFamilyInvariantContinuity.lean  | 230 +++++++++++++++++++++
 1 file changed, 230 insertions(+)

EXIT 0
```

### Focused build, final output lines

The complete log is `focused-build.txt` in the evidence directory. These are its actual final lines:

```text
$ LEAN_NUM_THREADS=1 lake build Poincare.Global.HamiltonCompactFamilyInvariantContinuity
Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [3861/3861] Built Poincare.Global.HamiltonCompactFamilyInvariantContinuity (2.0s)
Build completed successfully (3861 jobs).

EXIT 0
```

### Module scan source

```lean
import Poincare.Global.HamiltonCompactFamilyInvariantContinuity
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HamiltonCompactFamilyInvariantContinuity
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      count := count + 1
      let axs ← liftCoreM (collectAxioms n)
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "incorrect closure for {n}: {axs}"
      logInfo m!"DECL {n}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"EXACT_CLOSURES_PASS declarations={count}"
#check Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_scalarAt_of_ricciJet
#check Poincare.HamiltonCompactFamilyInvariantContinuity.continuousAt_ricciNormSqAt_of_ricciJet
#check Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_continuous
#check Poincare.HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous
```

### Exact-hypothesis partial-target probe

The probe appends this to the new module source:

```lean
namespace Poincare.HamiltonCompactFamilyInvariantContinuityProbe
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
example
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
    Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2) :=
  HamiltonCompactFamilyInvariantContinuity.curvatureContinuity_of_thirdJetProfiles_continuous
    K metric hjet
end Poincare.HamiltonCompactFamilyInvariantContinuityProbe
```

## Appendix B. Failed compiler attempts and remaining goal

The two initial finite-sum API guesses failed. The pinned Mathlib name used in the successful proof is `tendsto_finsetSum`, generated additively and source-visible through its alias. The Ricci retry removed one leftover reference to the real-time variable from the adapted coordinate composition.

### scalar-01

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:59:10: error(lean.unknownIdentifier): Unknown constant `ContinuousAt.sum`
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:60:10: error: No goals to be solved

EXIT 1
```

### scalar-02

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:59:10: error(lean.unknownIdentifier): Unknown identifier `continuousAt_finsetSum`
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:60:10: error: No goals to be solved

EXIT 1
```

### ricci-01

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:153:57: error(lean.unknownIdentifier): Unknown identifier `gt`
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:154:21: error: Application type mismatch: The argument
  hcoord
has type
  ContinuousAt (fun p => anchorChartRicciNormSqFlow (fun x => metric p.1) x 0 p.2) (k₀, ↑(extChartAt I x) x)
but is expected to have type
  ContinuousAt (Function.uncurry ?m.453) ((k₀, x).1, ↑(extChartAt I x) (k₀, x).2)
in the application
  ContinuousAt.comp' hcoord

EXIT 1
```

### remaining-measure

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-compact-family-evidence/remaining-measure.lean
/tmp/hamilton-compact-family-evidence/remaining-measure.lean:245:71: error: unsolved goals
M : Type u
inst✝¹¹ : TopologicalSpace M
inst✝¹⁰ : T2Space M
inst✝⁹ : SecondCountableTopology M
inst✝⁸ : MeasurableSpace M
inst✝⁷ : BorelSpace M
inst✝⁶ : ChartedSpace (ClosedSmoothModel 3) M
inst✝⁵ : IsManifold (closedSmoothModelWithCorners 3) ∞ M
inst✝⁴ : CompactSpace M
inst✝³ : ConnectedSpace M
inst✝² : SimplyConnectedSpace M
K : Type v
inst✝¹ : TopologicalSpace K
inst✝ : CompactSpace K
metric : K → ClosedSmoothRiemannianMetric 3 M
hjet : ∀ (slot : MetricEntryThirdJetSlot 3 M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
f : C(M, ℝ)
⊢ Continuous fun k => ∫ (x : M), f x ∂volumeMeasure (metric k)
M : Type u
inst✝¹¹ : TopologicalSpace M
inst✝¹⁰ : T2Space M
inst✝⁹ : SecondCountableTopology M
inst✝⁸ : MeasurableSpace M
inst✝⁷ : BorelSpace M
inst✝⁶ : ChartedSpace (ClosedSmoothModel 3) M
inst✝⁵ : IsManifold (closedSmoothModelWithCorners 3) ∞ M
inst✝⁴ : CompactSpace M
inst✝³ : ConnectedSpace M
inst✝² : SimplyConnectedSpace M
K : Type v
inst✝¹ : TopologicalSpace K
inst✝ : CompactSpace K
metric : K → ClosedSmoothRiemannianMetric 3 M
hjet : ∀ (slot : MetricEntryThirdJetSlot 3 M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
f : C(M, ℝ)
⊢ Continuous fun k => ∫ (x : M), f x ∂volumeMeasure (metric k)

EXIT 1
```

### Remaining-measure probe source

The probe appends this to the new module source:

```lean
namespace Poincare.HamiltonCompactFamilyInvariantContinuityProbe
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
example
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) := by
  apply FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  change Continuous (fun k ↦ ∫ x, f x ∂volumeMeasure (metric k))
  trace_state
end Poincare.HamiltonCompactFamilyInvariantContinuityProbe
```

## Appendix C. Source verification and measure searches

These are actual rg results in the checkout and pinned Mathlib. Empty declaration searches identify requested names that were not added. The local anonymous instance is tied to its source separately in Appendix A. The initial broad measure-name search is only a bounded negative search, not proof of library-wide absence.

### source-declarations

```text
$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuousAt_scalarAt_of_ricciJet\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:31:theorem continuousAt_scalarAt_of_ricciJet
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuousAt_ricciNormSqAt_of_ricciJet\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:105:theorem continuousAt_ricciNormSqAt_of_ricciJet
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcurvatureContinuity_of_continuous\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:193:theorem curvatureContinuity_of_continuous
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcurvatureContinuity_of_thirdJetProfiles_continuous\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean:217:theorem curvatureContinuity_of_thirdJetProfiles_continuous
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bHamiltonReactionCore3\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:132:def HamiltonReactionCore3 (M : Type u)
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bHamiltonReactionCore3Jet\b' Poincare .lake/packages/mathlib/Mathlib

EXIT 1

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\binvariantContinuity_of_thirdJetProfiles_continuous\b' Poincare .lake/packages/mathlib/Mathlib

EXIT 1

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartScalarTraceFlow\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointCurvatureRegularity.lean:377:noncomputable def anchorChartScalarTraceFlow
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartScalarTraceFlow_eq_scalarAt_zone\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointScalarTraceZoneBridge.lean:272:theorem anchorChartScalarTraceFlow_eq_scalarAt_zone
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartRicciNormSqFlow\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointPinchingEvolution.lean:948:noncomputable def anchorChartRicciNormSqFlow
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartRicciNormSqFlow_eq_ricciNormSqAt_zone\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1017:theorem anchorChartRicciNormSqFlow_eq_ricciNormSqAt_zone
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bMetricFamilyRicciJetChartContinuousAt\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:469:structure MetricFamilyRicciJetChartContinuousAt
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartInverseMetricCoeffFamily\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFamilyCovRicciNormContinuity.lean:30:noncomputable def anchorChartInverseMetricCoeffFamily
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\banchorChartRicciEntryFamily\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:399:noncomputable def anchorChartRicciEntryFamily
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\btoBlendedMetricThirdJetContinuousAt\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFamilyEntryThirdJetCovRicciContinuity.lean:63:theorem MetricFamilyBlendedMetricEntryThirdJetContinuousAt.toBlendedMetricThirdJetContinuousAt
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\btoRicciJetChartContinuousAt\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFamilyThirdJetCovRicciContinuity.lean:60:theorem MetricFamilyBlendedMetricThirdJetContinuousAt.toRicciJetChartContinuousAt
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bclosedSmoothRiemannianMetricEntryThirdJetTopology\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedMetricThirdJetTopology.lean:181:@[reducible] noncomputable def closedSmoothRiemannianMetricEntryThirdJetTopology :
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bmetricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedMetricThirdJetTopology.lean:224:theorem metricFamilyBlendedMetricEntryThirdJetContinuousAt_of_continuous
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedMetricThirdJetTopology.lean:205:theorem continuous_closedMetricFamily_of_entryThirdJetProfileJointContinuous
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bmetricEntryThirdJetProfile\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedMetricThirdJetTopology.lean:115:noncomputable def metricEntryThirdJetProfile (g : G) :
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bMetricEntryThirdJetSlot\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedMetricThirdJetTopology.lean:38:inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\btracelessRicciNormSqAt\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/RicciNorm.lean:190:noncomputable def tracelessRicciNormSqAt (x : M) : ℝ :=
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bclosedMetricFiniteVolumeMeasure\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:127:def closedMetricFiniteVolumeMeasure
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\binverseChartDensity_integrable\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonReactionCoreReduction.lean:31:theorem inverseChartDensity_integrable
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bhausdorffChartDensityEquality\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:124:theorem FiniteExtendedChartCover.hausdorffChartDensityEquality
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_inverseChartPullbackVolumeDensity\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffInverseChartGramContinuity.lean:124:theorem continuous_inverseChartPullbackVolumeDensity
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_movingIntegral_of_continuous_finiteMeasure_of_joint\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:44:theorem continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureContinuity.lean:245:theorem continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:41:theorem continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bFiniteExtendedChartCover\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:124:theorem FiniteExtendedChartCover.hausdorffChartDensityEquality
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:54:structure FiniteExtendedChartCover where
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:92:def chartSource (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:97:def manifoldPiece (C : FiniteExtendedChartCover (n := n) (M := M))
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcoordinateDomain\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:136:def coordinateDomain
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\brawHausdorffCoordinateDensityMeasure_relative_bounds\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HausdorffCoordinateDensityComparison.lean:59:theorem rawHausdorffCoordinateDensityMeasure_relative_bounds
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuous_iff_forall_continuousMap_continuous_integral\b' Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:829:lemma continuous_iff_forall_continuousMap_continuous_integral :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:397:lemma continuous_iff_forall_continuousMap_continuous_integral :
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\btendsto_finsetSum\b' Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Topology/Algebra/Monoid.lean:922:@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bisOpen_setOf_eventually_nhds\b' Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Topology/Neighborhoods.lean:238:theorem isOpen_setOf_eventually_nhds {p : X → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcutoff_eventuallyEq_one\b' Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/GeodesicTransport.lean:115:theorem cutoff_eventuallyEq_one :
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bcontinuousAt_extChartAt\b' Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:513:theorem continuousAt_extChartAt' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:517:theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
EXIT 0

$ rg -n --glob '*.lean' '(theorem|lemma|def|structure|inductive|abbrev|alias) .*\bextChartAt_source_mem_nhds\b' Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:496:theorem extChartAt_source_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:500:theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source ∈ 𝓝 x :=
EXIT 0
```

### measure-search

```text
$ rg -n 'continuous.*(FiniteVolumeMeasure|volumeMeasure)|volumeMeasure.*withDensity|withDensity.*volumeMeasure|inverseChartDensity.*(continuous|bound)|continuous.*inverseChartDensity' Poincare

EXIT 1
```

### weak-measure-api

```text
$ sed -n "817,842p" .lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean

variable [CompactSpace Ω]

/-- The characterization of weak convergence of finite measures by the condition that the
integrals of every continuous bounded nonnegative function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_lintegral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ≥0), Continuous fun x ↦ ∫⁻ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_lintegral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

/-- The characterization of weak convergence of finite measures by the usual (defining)
condition that the integrals of every continuous bounded function are continuous. -/
lemma continuous_iff_forall_continuousMap_continuous_integral :
    Continuous μs ↔ ∀ f : C(Ω, ℝ), Continuous fun x ↦ ∫ ω, f ω ∂(μs x) :=
  continuous_iff_forall_continuous_integral.trans
    (ContinuousMap.equivBoundedOfCompact ..).symm.forall_congr_left

variable [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {F : Type*}

lemma continuous_lintegral_continuousMap [FunLike F X ℝ≥0] [ContinuousMapClass F X ℝ≥0] (f : F) :
    Continuous fun μ : FiniteMeasure X ↦ ∫⁻ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_lintegral.1 continuous_id ⟨f, map_continuous f⟩

lemma continuous_integral_continuousMap [FunLike F X ℝ] [ContinuousMapClass F X ℝ] (f : F) :
    Continuous fun μ : FiniteMeasure X ↦ ∫ x, f x ∂μ :=
  continuous_iff_forall_continuousMap_continuous_integral.1 continuous_id ⟨f, map_continuous f⟩

EXIT 0
```

### finite-cover

```text
$ sed -n "35,92p" Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean; sed -n "300,335p" Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- A finite family of genuine extended charts whose open sources cover the
compact manifold. -/
structure FiniteExtendedChartCover where
  chartCount : ℕ
  anchor : Fin chartCount → M
  sources_cover :
    (⋃ i : Fin chartCount, (extChartAt I (anchor i)).source) = Set.univ

/-- Compactness extracts a finite subcover from the canonical extended-chart
source cover. -/
theorem exists_finiteExtendedChartCover :
    Nonempty (FiniteExtendedChartCover (n := n) (M := M)) := by
  classical
  obtain ⟨anchors, hanchors⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : M ↦ (extChartAt I x).source)
      (fun x ↦ isOpen_extChartAt_source x)
      (fun x _hx ↦ Set.mem_iUnion.mpr
        ⟨x, mem_extChartAt_source x⟩)
  refine ⟨
    { chartCount := anchors.card
      anchor := fun i ↦ (anchors.equivFin.symm i).1
      sources_cover := ?_ }⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hanchors (Set.mem_univ x))
  let a' : anchors := ⟨a, ha⟩
  refine Set.mem_iUnion.mpr ⟨anchors.equivFin a', ?_⟩
  simpa [a'] using hxa

/-- A fixed noncomputable finite extended-chart cover chosen from
compactness.  All later analytic hypotheses can be stated directly on this
canonical choice. -/
noncomputable def compactFiniteExtendedChartCover :
    FiniteExtendedChartCover (n := n) (M := M) :=
  Classical.choice exists_finiteExtendedChartCover

namespace FiniteExtendedChartCover

/-- The open source of the selected inverse chart. -/
def chartSource (C : FiniteExtendedChartCover (n := n) (M := M))
on a fixed compactness-selected finite inverse atlas. -/
structure FiniteExtendedChartFrameMeasureData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (s : Set ℝ) where
  density_integrable : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    Integrable (C.inverseChartDensity (gt t) i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  areaFormula : ∀ t ∈ s, ∀ i : Fin C.chartCount,
    C.RestrictedInverseChartPullbackHausdorffAreaFormula (gt t) i

/-- The finite decomposition bookkeeping is automatic from a finite genuine
inverse-atlas cover.  Only the variable-metric area formula and density
integrability are supplied by `H`. -/
def FiniteExtendedChartFrameMeasureData.toDecomposition
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (H : FiniteExtendedChartFrameMeasureData C gt s) :
    FiniteHausdorffChartDensityDecomposition gt s where
  chartCount := C.chartCount
  coordinateDomain := C.coordinateDomain
  coordinateDomain_measurable := C.coordinateDomain_measurable
  inverseChart := C.inverseChart
  inverseChart_measurable := C.inverseChart_measurable
  manifoldPiece := C.manifoldPiece
  manifoldPiece_measurable := C.manifoldPiece_measurable
  pieces_pairwise := C.manifoldPieces_pairwise
  pieces_cover := C.manifoldPieces_cover
  density := fun t i ↦ C.inverseChartDensity (gt t) i
  density_nonneg := fun t _ht i ↦
    Eventually.of_forall fun z ↦ C.inverseChartDensity_nonneg (gt t) i z
  density_integrable := H.density_integrable
  chartMeasure := fun t ht i ↦
    C.hausdorffChartDensityEquality_of_restrictedAreaFormula
      (gt t) i (H.areaFormula t ht i)

/-- The explicit intrinsic derivative used by dominated differentiation on

EXIT 0
```

### density-comparison

```text
$ cat Poincare/Global/HausdorffCoordinateDensityComparison.lean
import Poincare.Global.HausdorffCoordinateDensityVariation

/-!
# Order comparison for raw Hausdorff coordinate-density measures

The raw coordinate-density construction is monotone in its real density.
It also turns multiplication of the density by a nonnegative real constant
into scalar multiplication of the resulting measure.  These elementary
facts let pointwise relative density bounds be used directly in the local
Hausdorff epsilon squeeze.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory

namespace Poincare

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- Pointwise order of real coordinate densities induces order of their raw
Hausdorff-normalized measures. -/
theorem rawHausdorffCoordinateDensityMeasure_mono
    {U : Set E} {δ η : U → ℝ} (hδη : ∀ z, δ z ≤ η z) :
    rawHausdorffCoordinateDensityMeasure U δ ≤
      rawHausdorffCoordinateDensityMeasure U η := by
  rw [rawHausdorffCoordinateDensityMeasure,
    rawHausdorffCoordinateDensityMeasure]
  apply withDensity_mono
  filter_upwards [] with z
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hδη z) (by positivity)

/-- Multiplying a coordinate density by a nonnegative real constant scales
the resulting raw Hausdorff coordinate-density measure by its `ENNReal`
image. -/
theorem rawHausdorffCoordinateDensityMeasure_const_mul
    (U : Set E) (δ : U → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    rawHausdorffCoordinateDensityMeasure U (fun z ↦ a * δ z) =
      ENNReal.ofReal a • rawHausdorffCoordinateDensityMeasure U δ := by
  rw [rawHausdorffCoordinateDensityMeasure,
    rawHausdorffCoordinateDensityMeasure]
  rw [← withDensity_smul' (ENNReal.ofReal a)
    (fun z ↦ ENNReal.ofReal
      ((rawHausdorffLebesgueScale n : ℝ) * δ z)) ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show
      (rawHausdorffLebesgueScale n : ℝ) * (a * δ z) =
        a * ((rawHausdorffLebesgueScale n : ℝ) * δ z) by ring]
  rw [ENNReal.ofReal_mul ha]

/-- Pointwise relative bounds around a constant density become a two-sided
measure comparison with exactly the same scalar factors. -/
theorem rawHausdorffCoordinateDensityMeasure_relative_bounds
    (U : Set E) (δ : U → ℝ) (δ₀ a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : ∀ z, a * δ₀ ≤ δ z ∧ δ z ≤ b * δ₀) :
    ENNReal.ofReal a •
          rawHausdorffCoordinateDensityMeasure U (fun _ ↦ δ₀) ≤
        rawHausdorffCoordinateDensityMeasure U δ ∧
      rawHausdorffCoordinateDensityMeasure U δ ≤
        ENNReal.ofReal b •
          rawHausdorffCoordinateDensityMeasure U (fun _ ↦ δ₀) := by
  constructor
  · rw [← rawHausdorffCoordinateDensityMeasure_const_mul U
      (fun _ ↦ δ₀) ha]
    exact rawHausdorffCoordinateDensityMeasure_mono fun z ↦ (hδ z).1
  · rw [← rawHausdorffCoordinateDensityMeasure_const_mul U
      (fun _ ↦ δ₀) hb]
    exact rawHausdorffCoordinateDensityMeasure_mono fun z ↦ (hδ z).2

end Poincare

EXIT 0
```

### search-sums

```text
$ rg -n 'continuousAt_finset|continuousAt_prod|ContinuousAt\.fun_(sum|prod)|theorem.*fun_prod' .lake/packages/mathlib/Mathlib/Topology
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:645:theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {x : α × β} :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:649:theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {x : α × β} :

EXIT 0
```


## Appendix D. Remaining recorded checks

### scalar-scan

```text
$ rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 1
```

### scalar-diff

```text
$ git diff --check

EXIT 0
```

### ricci-diff

```text
$ git diff --check

EXIT 0
```

### topology-diff

```text
$ git diff --check

EXIT 0
```

### report-diff

```text
$ git diff --check; git diff --check b358db205a55844fa09cf253630ec4cc6525d406 -- Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean

EXIT 0
```
