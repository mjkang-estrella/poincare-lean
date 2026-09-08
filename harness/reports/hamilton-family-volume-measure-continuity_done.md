# Hamilton family volume-measure continuity: completed worker proof

Date: 2026-09-08. Base: `eb483699d8c38496aad1f9c21c7331ae69b56e73`.
Branch: `worker/hamilton-family-volume-measure-continuity`.
Verified proof head: `2b7412aea2cc741b7502fd075dbd6416445b58b2`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.
Pinned Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.

Both requested targets compile. The new module is
`Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean`, in namespace
`Poincare.HamiltonFamilyVolumeMeasureContinuity`.
The finite volume measure has its original weak topology. Target 1 retains
exactly the requested parameter, compactness, and third-jet hypotheses and
the manifold section assumptions of the original reaction core.

Target 2 defines `HamiltonReactionCore3Jet`, reconstructs `HamiltonReactionCore3`,
and supplies both the manifold and universal Hamilton endpoint adapters.
Only the three family-continuity clauses were replaced. A source comparison
against the landed core confirmed that every other clause and quantifier is
unchanged. No analytic premise was added to an auxiliary definition.

This is a worker result awaiting independent orchestrator review. It proves
the continuity implication and the core-to-endpoint implications. It does not
prove existence of a jet-form reaction core, a Ricci flow, or the Poincare
conjecture. No merge or task acceptance is asserted.

## 1. Proof route

The ordinary finite extended-chart cover does not certify compact coordinate
closures. The useful landed replacement is
`FiniteFixedAnchorCutoffOneChartCover`, imported from its existing module.
Its open inner domains cover the manifold, and each inner-domain closure has
a compact coordinate image contained in its fixed anchor's cutoff-one region.

On such a coordinate set, the value slots of `metricEntryThirdJetProfile`
are precisely the genuine metric entries. Entrywise continuity gives
continuity of the Gram matrix and its square-root determinant density.
No continuity in a moving chart anchor is assumed.

Coordinate Lebesgue measure on each compact coordinate set is finite.
The local integral theorem also permits restriction to any fixed subset of
that compact set. It applies the landed compact-space moving-integral theorem
to a **constant coordinate measure**. This use is not circular: no continuity
of the moving Riemannian volume measures is supplied to that theorem.
Currying into continuous maps on the compact spatial domain handles arbitrary
topological parameter spaces. The initial dominated-convergence attempt was
replaced because its Mathlib theorem requires first countability of the
parameter, which the task does not assume.

The landed inverse-chart area formula is restricted using the existing raw
coordinate-density inclusion theorem and measure push-forward identities.
This transports the local coordinate integrals to intrinsic volume integrals
on every measurable piece lying in the compact chart image.

The final assembly disjointizes the finite cover's open inner domains.
Each disjointized piece stays in its associated compact coordinate image.
A finite sum of the local continuous integrals is the global integral of any
`f : C(M, ℝ)`. The finite-measure test-integral characterization gives Target 1.
The intermediate global integral theorem works in every dimension and for
arbitrary topological parameters, without parameter compactness.

The core adapter combines Target 1 with the two landed curvature-continuity
conclusions. The universal adapter installs the canonical Borel structure,
matching the original universal reduction and preserving independent
universes `u` and `v`.

## 2. Declarations and commits

The module contains these 14 source declarations:

- `continuous_inner_of_thirdJetProfiles_continuous`
- `continuous_parameter_inverseChartPullbackGramMatrix`
- `continuous_parameter_inverseChartPullbackVolumeDensity`
- `continuous_inverseChartPullbackVolumeDensity_on_cutoffOne`
- `continuous_integral_inverseChartPullbackVolumeDensity_on_compact`
- `compact_inverseChart_hausdorffChartDensityEquality`
- `continuous_integral_volumeMeasure_restrict_compact_chart`
- `continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous`
- `continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`
- `HamiltonReactionCore3Jet`
- `hamiltonReactionCore3_of_jet`
- `hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet`
- `UniversalHamiltonReactionCoreJetStatement`
- `universalHamiltonConvergence_of_universalHamiltonReactionCoreJet`

Each theorem or definition was committed after successful source elaboration
and its individual printed dependency check. A final cleanup commit removes
local notation declarations without changing the mathematical statements.

```text
e60bbf1b Prove parameter continuity of intrinsic metric pairings
8b4d6d8f Prove pointwise parameter continuity of inverse-chart Gram matrices
04e0a0da Prove parameter continuity of inverse-chart volume densities
fb087ddf Prove joint density continuity on cutoff-one coordinate sets
c0be1653 Prove restricted weighted density integral continuity on compact coordinate sets
6e5b1041 Restrict the inverse-chart area formula to compact coordinate sets
50cdfc9a Prove intrinsic volume-integral continuity on compact chart pieces
ff78d5be Prove global volume test-integral continuity from third-jet profiles
c739418b Prove weak volume-measure continuity with the exact family hypotheses
ceab8432 Define the jet-form Hamilton reaction core
e8a22967 Recover the original Hamilton reaction core from jet continuity
58a70231 Connect the jet-form reaction core to Hamilton convergence
da098b02 State universal jet-form Hamilton reaction core existence
b5a2cc25 Derive universal Hamilton convergence from universal jet-form core existence
2b7412ae Remove generated local-notation helpers from the continuity module
```

## 3. Verification scope and results

All Lean commands below ran with `LEAN_NUM_THREADS=1`; the evidence runner
sets it in the subprocess environment. The displayed command and output are
captured from actual executions, including each exit status.

- Direct module elaboration: exit 0.
- Exact target and endpoint signature probes: exit 0.
- Forbidden-token scan: empty, exit 1, the expected `rg` result for no matches.
- Diff whitespace check: exit 0.
- Every one of the 14 source declarations: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Every compiler-generated helper was also checked for nonstandard dependencies.

The exact-three check uses the source-declaration scope of the repository's
`harness/gate.sh`, whose scanner excludes `Name.isInternal`. The expanded
check additionally inspects internal helpers and reports them explicitly.
There are seven internal proof helpers generated while elaborating the core.
Six have the same three dependencies. The remaining helper,
`HamiltonReactionCore3Jet._proof_1`, proves `(2 + 1).AtLeastTwo` and has only
`[propext]`. Thus the exact-three statement applies to all 14 source
declarations, not literally to every compiler-generated constant. The full
output and scanner source below make this distinction reviewable.

The direct compiler emits one unused-section-variable warning for
`SecondCountableTopology M` and `SimplyConnectedSpace M` in Target 1. Those
assumptions are retained to match the requested manifold section; they are
not needed by the integration proof. There are no proof errors.

No existing Lean source, root import, frozen contract, task, ledger, mission,
or HANDOFF file changed. The task-specific restriction on existing files
supersedes the general HANDOFF-edit instruction. This report provides the
handoff instead. Only the new Lean module and this report are added.
No full root build or root integration audit was run.

### Direct Lean gate

```text
$ lake env lean Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean
Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean:283:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

EXIT 0
```

### Compiled module for fresh declaration inspection

```text
$ lake env lean -o .lake/build/lib/lean/Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.olean Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean
Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean:283:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

EXIT 0
```

### Forbidden-token scan

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean

EXIT 1
```

### Diff check against the recorded base

```text
$ git diff --check eb483699d8c38496aad1f9c21c7331ae69b56e73

EXIT 0
```

### Exact target and endpoint probes

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/exact-target.lean

EXIT 0
```

### Complete declaration and helper scan

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/module-scan.lean
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_1: [propext]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackVolumeDensity
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackVolumeDensity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackGramMatrix
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackGramMatrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_4: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_3: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_6: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_restrict_compact_chart
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_restrict_compact_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inner_of_thirdJetProfiles_continuous
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inner_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_5: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_7: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement
'Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
INTERNAL_HELPER Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_2: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.compact_inverseChart_hausdorffChartDensityEquality
'Poincare.HamiltonFamilyVolumeMeasureContinuity.compact_inverseChart_hausdorffChartDensityEquality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_CLOSURES_PASS declarations=14
Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (K : Type v) [TopologicalSpace K] [CompactSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hjet :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) :
  Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k)
Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet.{u, v} (M : Type u) [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) : Poincare.HamiltonReactionCore3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet.{u, v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) :
  Poincare.HamiltonConvergencePinchedLimit3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement.{u, v} : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet.{u, v}
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement) :
  Poincare.UniversalHamiltonConvergenceStatement

EXIT 0
```

### Core body comparison

```text
CORE_BODY_MATCH_PASS: exactly the three continuity clauses replaced
```

## 4. Independent review and retained evidence

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean
```

Then rerun the source-token scan, compile the module for fresh inspection,
and execute the declaration and exact-signature probes below. Review the
new core against `HamiltonReactionCoreReduction.lean`, including the unchanged
local-domination and all-real-time joint C³ requirements. Root import wiring,
root audits, merge order, and acceptance belong to the orchestrator.

Scratch sources, all successful and failed compiler receipts, the final diff,
and the runner remain in `/tmp/hamilton-family-volume-measure-evidence`.
The proof commits preserve the diff durably. The receipt appendices below
preserve the relevant compiler output in this report as well.

### Declaration scan source

```lean
import Poincare.Global.HamiltonFamilyVolumeMeasureContinuity
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HamiltonFamilyVolumeMeasureContinuity
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      for ax in axs do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "nonstandard dependency for {n}: {axs}"
      if n.isInternal then
        logInfo m!"INTERNAL_HELPER {n}: {axs}"
      else
        count := count + 1
        unless axs.size == 3 && axs.contains ``propext &&
            axs.contains ``Classical.choice && axs.contains ``Quot.sound do
          throwError "incorrect closure for {n}: {axs}"
        logInfo m!"DECL {n}"
        elabCommand (← `(command| #print axioms $(mkIdent n)))
  logInfo m!"EXACT_CLOSURES_PASS declarations={count}"
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement
#check Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet
```

### Exact target and endpoint probe source

```lean
import Poincare.Global.HamiltonFamilyVolumeMeasureContinuity
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonFamilyVolumeMeasureContinuityProbe
variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
example (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) :=
  HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
    K metric hjet
example : HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet.{u, v} M →
    HamiltonReactionCore3.{u, v} M :=
  HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet
example : HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet.{u, v} M →
    HamiltonConvergencePinchedLimit3 M :=
  HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet
example : HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement.{u, v} →
    UniversalHamiltonConvergenceStatement.{u} :=
  HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet
end Poincare.HamiltonFamilyVolumeMeasureContinuityProbe
```

## Appendix A. Individual successful proof checks

### inner-03

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/inner-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inner_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### gram-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/gram-check.lean
/tmp/hamilton-family-volume-measure-evidence/gram-check.lean:42:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackGramMatrix`:
  [T2Space M]
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackGramMatrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### density-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/density-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_parameter_inverseChartPullbackVolumeDensity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### joint-03

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/joint-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### integral-03

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/integral-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### area-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/area-check.lean
/tmp/hamilton-family-volume-measure-evidence/area-check.lean:131:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.compact_inverseChart_hausdorffChartDensityEquality`:
  [SecondCountableTopology M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.compact_inverseChart_hausdorffChartDensityEquality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### local-02

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/local-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_restrict_compact_chart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### global-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/global-check.lean
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### target-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/target-check.lean
/tmp/hamilton-family-volume-measure-evidence/target-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### core-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/core-check.lean
/tmp/hamilton-family-volume-measure-evidence/core-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### adapter-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/adapter-check.lean
/tmp/hamilton-family-volume-measure-evidence/adapter-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### endpoint-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/endpoint-check.lean
/tmp/hamilton-family-volume-measure-evidence/endpoint-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### universal-core-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/universal-core-check.lean
/tmp/hamilton-family-volume-measure-evidence/universal-core-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

### universal-endpoint-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/universal-endpoint-check.lean
/tmp/hamilton-family-volume-measure-evidence/universal-endpoint-check.lean:286:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT 0
```

## Appendix B. Failed attempts and their resolution

All failures below were resolved before the final proof head.

- The first pairing proof needed composition and identity reduction before
  applying the anchor-value equality.
- The joint chart proof needed an explicit subtype on its composition map.
  A premature omission of the manifold assumptions was reversed because the
  landed Gram-field identity includes those assumptions in its signature.
- The first integral proof exposed the extra first-countability requirement
  of `continuous_of_dominated`. The final proof uses compact-space integration
  against a fixed coordinate measure instead.
- Two measure-theorem namespace guesses were corrected using their source.
- An initial scan over every generated constant included local-notation
  unexpanders. The notation was removed. The remaining generated numeral
  instance proof has the smaller standard dependency set documented above;
  the final scanner follows the repository's source-declaration scope and
  separately audits every internal helper.

### inner-gate

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/inner-check.lean
/tmp/hamilton-family-volume-measure-evidence/inner-check.lean:34:2: error: Type mismatch: After simplification, term
  h
 has type
  Continuous
    ((fun p => (metricEntryThirdJetProfile (metric p.1) (MetricEntryThirdJetSlot.value x a b)) p.2) ∘ fun x_1 =>
      (id x_1, ↑(extChartAt I x) x))
but is expected to have type
  Continuous fun k => (((metric k).inner x) a) b
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inner_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

EXIT 1
```

### joint-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/joint-check.lean
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:85:12: error: don't know how to synthesize implicit argument `f`
  @Continuous.comp (K × Subtype ?m.138) (K × E) ℝ instTopologicalSpaceProd instTopologicalSpaceProd
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace (fun x => (x.1, (Subtype.val ∘ Prod.snd) x))
    (fun p =>
      (metricEntryThirdJetProfile (metric p.1)
          (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
            ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
        p.2)
    (hjet
      (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i) ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
    (Continuous.prodMk continuous_fst (Continuous.comp continuous_subtype_val continuous_snd))
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ K × Subtype ?m.138 → K × E
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:85:12: error: don't know how to synthesize implicit argument `X`
  @Continuous.comp (K × Subtype ?m.138) (K × E) ℝ instTopologicalSpaceProd instTopologicalSpaceProd
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace (fun x => (x.1, (Subtype.val ∘ Prod.snd) x))
    (fun p =>
      (metricEntryThirdJetProfile (metric p.1)
          (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
            ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
        p.2)
    (hjet
      (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i) ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
    (Continuous.prodMk continuous_fst (Continuous.comp continuous_subtype_val continuous_snd))
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type v
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:5: error: don't know how to synthesize implicit argument `g`
  @Continuous.prodMk K E (K × Subtype ?m.138) inst✝ (PiLp.topologicalSpace 2 fun x => ℝ) instTopologicalSpaceProd
    Prod.fst (Subtype.val ∘ Prod.snd) continuous_fst (Continuous.comp continuous_subtype_val continuous_snd)
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ K × Subtype ?m.138 → E
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:5: error: don't know how to synthesize implicit argument `f`
  @Continuous.prodMk K E (K × Subtype ?m.138) inst✝ (PiLp.topologicalSpace 2 fun x => ℝ) instTopologicalSpaceProd
    Prod.fst (Subtype.val ∘ Prod.snd) continuous_fst (Continuous.comp continuous_subtype_val continuous_snd)
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ K × Subtype ?m.138 → K
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:5: error: don't know how to synthesize implicit argument `Z`
  @Continuous.prodMk K E (K × Subtype ?m.138) inst✝ (PiLp.topologicalSpace 2 fun x => ℝ) instTopologicalSpaceProd
    Prod.fst (Subtype.val ∘ Prod.snd) continuous_fst (Continuous.comp continuous_subtype_val continuous_snd)
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type v
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:28: error: don't know how to synthesize implicit argument `g`
  @Continuous.comp (K × Subtype ?m.138) (Subtype ?m.138) E instTopologicalSpaceProd instTopologicalSpaceSubtype
    (PiLp.topologicalSpace 2 fun x => ℝ) Prod.snd Subtype.val continuous_subtype_val continuous_snd
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Subtype ?m.138 → E
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:28: error: don't know how to synthesize implicit argument `f`
  @Continuous.comp (K × Subtype ?m.138) (Subtype ?m.138) E instTopologicalSpaceProd instTopologicalSpaceSubtype
    (PiLp.topologicalSpace 2 fun x => ℝ) Prod.snd Subtype.val continuous_subtype_val continuous_snd
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ K × Subtype ?m.138 → Subtype ?m.138
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:28: error: don't know how to synthesize implicit argument `Y`
  @Continuous.comp (K × Subtype ?m.138) (Subtype ?m.138) E instTopologicalSpaceProd instTopologicalSpaceSubtype
    (PiLp.topologicalSpace 2 fun x => ℝ) Prod.snd Subtype.val continuous_subtype_val continuous_snd
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:28: error: don't know how to synthesize implicit argument `X`
  @Continuous.comp (K × Subtype ?m.138) (Subtype ?m.138) E instTopologicalSpaceProd instTopologicalSpaceSubtype
    (PiLp.topologicalSpace 2 fun x => ℝ) Prod.snd Subtype.val continuous_subtype_val continuous_snd
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type v
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:56: error: don't know how to synthesize implicit argument `Y`
  @continuous_snd K (Subtype ?m.138) inst✝ instTopologicalSpaceSubtype
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:51: error: don't know how to synthesize placeholder
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ E → Prop
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:20: error: don't know how to synthesize implicit argument
  @continuous_fst K (Subtype ?m.138) inst✝ instTopologicalSpaceSubtype
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ TopologicalSpace (Subtype ?m.138)
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:87:20: error: don't know how to synthesize placeholder
context:
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Type
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:85:7: error: failed to infer `have` declaration type
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:79:43: error: unsolved goals
case hG.h.h
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
⊢ Continuous fun a => inverseChartPullbackGramMatrix (metric a.1) x ⟨↑a.2, ⋯⟩ i j
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

EXIT 1
```

### joint-02

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/joint-check.lean
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:91:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  T2Space M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:91:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  CompactSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:91:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  ConnectedSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:91:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  MeasurableSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:91:6: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  BorelSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/joint-check.lean:79:43: error: unsolved goals
n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
hp : Continuous fun p => (p.1, ↑p.2)
h :
  Continuous
    ((fun p =>
        (metricEntryThirdJetProfile (metric p.1)
            (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
          p.2) ∘
      fun p => (p.1, ↑p.2))
p : K × ↑S
⊢ T2Space M

n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
hp : Continuous fun p => (p.1, ↑p.2)
h :
  Continuous
    ((fun p =>
        (metricEntryThirdJetProfile (metric p.1)
            (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
          p.2) ∘
      fun p => (p.1, ↑p.2))
p : K × ↑S
⊢ CompactSpace M

n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
hp : Continuous fun p => (p.1, ↑p.2)
h :
  Continuous
    ((fun p =>
        (metricEntryThirdJetProfile (metric p.1)
            (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
          p.2) ∘
      fun p => (p.1, ↑p.2))
p : K × ↑S
⊢ ConnectedSpace M

n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
hp : Continuous fun p => (p.1, ↑p.2)
h :
  Continuous
    ((fun p =>
        (metricEntryThirdJetProfile (metric p.1)
            (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
          p.2) ∘
      fun p => (p.1, ↑p.2))
p : K × ↑S
⊢ MeasurableSpace M

n : ℕ
M : Type u
K : Type v
inst✝³ : TopologicalSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : TopologicalSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
i j : Fin n
hp : Continuous fun p => (p.1, ↑p.2)
h :
  Continuous
    ((fun p =>
        (metricEntryThirdJetProfile (metric p.1)
            (MetricEntryThirdJetSlot.value x ((EuclideanSpace.basisFun (Fin n) ℝ) i)
              ((EuclideanSpace.basisFun (Fin n) ℝ) j)))
          p.2) ∘
      fun p => (p.1, ↑p.2))
p : K × ↑S
⊢ BorelSpace M
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

EXIT 1
```

### integral-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/integral-check.lean
/tmp/hamilton-family-volume-measure-evidence/integral-check.lean:117:8: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.comap_subtype_coe_apply`
/tmp/hamilton-family-volume-measure-evidence/integral-check.lean:115:31: error: unsolved goals
n : ℕ
M : Type u
K : Type v
inst✝⁹ : TopologicalSpace M
inst✝⁸ : T2Space M
inst✝⁷ : ChartedSpace E M
inst✝⁶ : IsManifold I ∞ M
inst✝⁵ : TopologicalSpace K
inst✝⁴ : CompactSpace M
inst✝³ : ConnectedSpace M
inst✝² : MeasurableSpace M
inst✝¹ : BorelSpace M
inst✝ : CompactSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hSc : IsCompact S
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
f : C(↑S, ℝ)
this : CompactSpace ↑S := isCompact_iff_compactSpace.mp hSc
μ : Measure ↑S := coordinateLebesgueMeasure S
⊢ (Measure.comap Subtype.val volume) univ < ⊤
/tmp/hamilton-family-volume-measure-evidence/integral-check.lean:125:8: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  FirstCountableTopology K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/hamilton-family-volume-measure-evidence/integral-check.lean:112:66: error: unsolved goals
n : ℕ
M : Type u
K : Type v
inst✝⁹ : TopologicalSpace M
inst✝⁸ : T2Space M
inst✝⁷ : ChartedSpace E M
inst✝⁶ : IsManifold I ∞ M
inst✝⁵ : TopologicalSpace K
inst✝⁴ : CompactSpace M
inst✝³ : ConnectedSpace M
inst✝² : MeasurableSpace M
inst✝¹ : BorelSpace M
inst✝ : CompactSpace K
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hSc : IsCompact S
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
f : C(↑S, ℝ)
this✝ : CompactSpace ↑S := ⋯
μ : Measure ↑S := ⋯
this : IsFiniteMeasure μ := ⋯
hF : Continuous fun p => f p.2 * inverseChartPullbackVolumeDensity (metric p.1) x ⟨↑p.2, ⋯⟩
B : ℝ
hB : ∀ x_1 ∈ univ, ‖f x_1.2 * inverseChartPullbackVolumeDensity (metric x_1.1) x ⟨↑x_1.2, ⋯⟩‖ ≤ B
⊢ FirstCountableTopology K
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

EXIT 1
```

### local-01

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/local-check.lean
/tmp/hamilton-family-volume-measure-evidence/local-check.lean:200:4: error(lean.unknownIdentifier): Unknown constant `MeasureTheory.Measure.restrict_withDensity`
/tmp/hamilton-family-volume-measure-evidence/local-check.lean:180:68: error: unsolved goals
n : ℕ
M : Type u
K : Type v
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : ChartedSpace E M
inst✝⁵ : IsManifold I ∞ M
inst✝⁴ : TopologicalSpace K
inst✝³ : CompactSpace M
inst✝² : ConnectedSpace M
inst✝¹ : MeasurableSpace M
inst✝ : BorelSpace M
metric : K → ClosedSmoothRiemannianMetric n M
hjet : ∀ (slot : MetricEntryThirdJetSlot n M), Continuous fun p => (metricEntryThirdJetProfile (metric p.1) slot) p.2
x : M
S : Set E
hSc : IsCompact S
hS : S ⊆ (extChartAt I x).target
hχ : ∀ z ∈ S, GeodesicTransport.cutoff x z = 1
P : Set M
hPm : MeasurableSet P
hP : P ⊆ range fun z => inverseExtendedChartParametrization x ⟨↑z, ⋯⟩
f : C(M, ℝ)
ψ : ↑S → M := fun z => inverseExtendedChartParametrization x ⟨↑z, ⋯⟩
hψ : Continuous ψ
c : ℝ := ↑(rawHausdorffLebesgueScale n)
A : Set ↑S := ψ ⁻¹' P
F : C(↑S, ℝ) := { toFun := fun z => c * f (ψ z), continuous_toFun := ⋯ }
hcont :
  Continuous fun k =>
    ∫ (z : ↑S) in A, F z * inverseChartPullbackVolumeDensity (metric k) x ⟨↑z, ⋯⟩ ∂coordinateLebesgueMeasure S
k : K
hchart :
  Measure.map ψ
      (rawHausdorffCoordinateDensityMeasure S fun z => inverseChartPullbackVolumeDensity (metric k) x ⟨↑z, ⋯⟩) =
    (volumeMeasure (metric k)).restrict (range ψ)
⊢ (∫ (x : ↑S) in ψ ⁻¹' P,
      f
        (ψ
          x) ∂(coordinateLebesgueMeasure S).withDensity fun z =>
        ENNReal.ofReal (↑(rawHausdorffLebesgueScale n) * inverseChartPullbackVolumeDensity (metric k) x ⟨↑z, ⋯⟩)) =
    ∫ (z : ↑S) in A, F z * inverseChartPullbackVolumeDensity (metric k) x ⟨↑z, ⋯⟩ ∂coordinateLebesgueMeasure S
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_restrict_compact_chart' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

EXIT 1
```

### module-scan

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/module-scan.lean
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
/tmp/hamilton-family-volume-measure-evidence/module-scan.lean:3:0: error: incorrect closure for _private.Poincare.Global.HamiltonFamilyVolumeMeasureContinuity.0.Poincare.HamiltonFamilyVolumeMeasureContinuity._aux_Poincare_Global_HamiltonFamilyVolumeMeasureContinuity___unexpand_Poincare_ClosedSmoothModel_1: []
Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (K : Type v) [TopologicalSpace K] [CompactSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hjet :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) :
  Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k)
Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet.{u, v} (M : Type u) [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) : Poincare.HamiltonReactionCore3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet.{u, v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) :
  Poincare.HamiltonConvergencePinchedLimit3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement.{u, v} : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet.{u, v}
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement) :
  Poincare.UniversalHamiltonConvergenceStatement

EXIT 1
```

### module-scan-02

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/module-scan.lean
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet
'Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_inverseChartPullbackVolumeDensity_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_integral_volumeMeasure_of_thirdJetProfiles_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne
'Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_inverseChartPullbackVolumeDensity_on_cutoffOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
/tmp/hamilton-family-volume-measure-evidence/module-scan.lean:3:0: error: incorrect closure for Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_1: [propext]
Poincare.HamiltonFamilyVolumeMeasureContinuity.continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous.{u,
    v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (K : Type v) [TopologicalSpace K] [CompactSpace K]
  (metric : K → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hjet :
    ∀ (slot : Poincare.MetricEntryThirdJetSlot 3 M),
      Continuous fun p => (Poincare.metricEntryThirdJetProfile (metric p.1) slot) p.2) :
  Continuous fun k => Poincare.closedMetricFiniteVolumeMeasure (metric k)
Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet.{u, v} (M : Type u) [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonReactionCore3_of_jet.{u, v} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) : Poincare.HamiltonReactionCore3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet.{u, v}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet M) :
  Poincare.HamiltonConvergencePinchedLimit3 M
Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement.{u, v} : Prop
Poincare.HamiltonFamilyVolumeMeasureContinuity.universalHamiltonConvergence_of_universalHamiltonReactionCoreJet.{u, v}
  (h : Poincare.HamiltonFamilyVolumeMeasureContinuity.UniversalHamiltonReactionCoreJetStatement) :
  Poincare.UniversalHamiltonConvergenceStatement

EXIT 1
```

### generated-proof

```text
$ lake env lean /tmp/hamilton-family-volume-measure-evidence/generated-proof.lean
theorem Poincare.HamiltonFamilyVolumeMeasureContinuity.HamiltonReactionCore3Jet._proof_1 : (2 + 1).AtLeastTwo :=
Nat.instAtLeastTwoHAddOfNat 2

EXIT 0
```
