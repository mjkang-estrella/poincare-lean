# Supplied unit recognition completed

Date: 2026-09-08. Branch: `worker/supplied-unit-recognition`.
Frozen base: `e9e7d3e7aa559f3a28f08773beec606d402aeb4f`.
Verified proof head: `8f32a50d722efc0c7f5097ce6b1b629001c6bfea`.

All five frozen task-19 targets are proved in the one new Lean file
`Poincare/Global/CartanSuppliedUnitRecognition.lean`. This is a worker result
awaiting independent orchestrator review, not an acceptance or merge decision.

## What was proved

- `controlled_globalLocalDevelopment` constructs the quantitative cover and
  unconditional switch control, chooses the rooted skeleton and whole-cell
  realization, and uses the landed supplied development local homeomorphism.
- `controlled_unitRecognition` applies the existing compact-covering and
  round-sphere recognition consumer to that developing map.
- `unitRecognition` proves the literal `UnitConstantCurvatureSphereRecognition3 M`
  on the original chart instance. For each input metric it invokes the landed
  controlled recognition reduction, installs exactly its returned `charts` and
  `hs`, builds `Controlled charts (d.replaceTopology hd.symm)` from its finite
  atlas and ball clauses, and applies the recognition transfer to the original
  metric and curvature proof.
- `universal_unitRecognition` proves the existing
  `UniversalUnitConstantCurvatureSphereRecognitionStatement.{u}` with all
  displayed type and instance binders.
- `poincare_of_hamiltonConvergence` proves the displayed implication to
  `PoincareConjecture.{u}`, retaining exactly the universal Hamilton convergence
  premise. No patch-cover, switch, mesh, homotopy, atlas compatibility, or
  recognition premise remains.

The controlled adapter retains its frozen arguments. The supplied construction
already works for arbitrary smooth chart instances, so those auxiliary control
arguments are not needed inside its geometric proof, as explicitly allowed by
task 19. The auxiliary metric and the geometric chain metric are never equated.
The reduction uses the exact `replaceTopology` metric for its ball clause.

Hamilton convergence is not proved. The reserved theorem
`Poincare.poincare_conjecture` is not declared and was confirmed absent from the
compiled module's environment.

## Scope and proof commits

The initial status was clean at the frozen base. The worktree list confirmed
this isolated worker branch. The task-specific branch and file restrictions
supersede the general branch-naming and `HANDOFF.md` update instructions.
No existing Lean file, `Poincare.lean`, audit wiring, task file, or `HANDOFF.md`
was changed. The only deliverables are the new Lean module and this report.

Each theorem was compiled before its individual commit:

```text
372c57d7 Prove controlled supplied global local development
8d5f6ce2 Deduce controlled unit curvature sphere recognition
fdffbc5b Transfer supplied unit recognition through controlled chart reduction
5b821062 Prove universal unit curvature sphere recognition
8f32a50d Discharge recognition premise in Hamilton Poincare reduction
```

## Actual verification commands and output

The direct command was run after each of the five successive theorem additions:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUnitRecognition.lean
```

All five runs exited 0. Logs are `lean-01.log` through `lean-05.log` under
`/tmp/supplied-unit-recognition-evidence`. Every run produced the same sole
warning below. There were no failed compiler attempts.

```text
Poincare/Global/CartanSuppliedUnitRecognition.lean:31:0: warning: automatically included section variable(s) unused in theorem `Poincare.CartanSuppliedUnitRecognition.controlled_globalLocalDevelopment`:
  [SecondCountableTopology M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

The focused build command exited 0:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSuppliedUnitRecognition
```

Its complete output is preserved in `build.log` in the evidence directory.
The final output, including replayed dependency warnings, was:

```text

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
⚠ [3604/3633] Replayed Poincare.Global.CartanFixedChartGenericInverseEndpointODEPrimitive
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [3620/3633] Replayed Poincare.Global.CartanSuppliedBufferedPairAgreement
warning: Poincare/Global/CartanSuppliedBufferedPairAgreement.lean:350:7: unused variable `hcurv`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [3633/3633] Built Poincare.Global.CartanSuppliedUnitRecognition (2.4s)
warning: Poincare/Global/CartanSuppliedUnitRecognition.lean:31:0: automatically included section variable(s) unused in theorem `Poincare.CartanSuppliedUnitRecognition.controlled_globalLocalDevelopment`:
  [SecondCountableTopology M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (3633 jobs).
```

The five frozen signatures were copied from the task-19 block in
`harness/reports/parametrization-plan-3.md`, changed only from theorem headers
into `example` declarations, and given the respective implemented theorem as
proof. The scratch probe enables `autoImplicit false` and uses the displayed
common context. This command exited 0 with no output:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-unit-recognition-evidence/signatures.lean
```

The named closure checks, module-wide scan including internal declarations,
and reserved-name absence check also exited 0:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/supplied-unit-recognition-evidence/axioms.lean
```

Actual output:

```text
'Poincare.CartanSuppliedUnitRecognition.controlled_globalLocalDevelopment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUnitRecognition.controlled_unitRecognition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUnitRecognition.unitRecognition' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanSuppliedUnitRecognition.universal_unitRecognition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CartanSuppliedUnitRecognition.poincare_of_hamiltonConvergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
MODULE_SCAN declarations=11 nonstandard=[]
RESERVED_THEOREM_ABSENT
```

The token and whitespace gates produced:

```text
$ rg -n \b(sorry|admit|axiom)\b|native_decide Poincare/Global/CartanSuppliedUnitRecognition.lean
exit=1
$ git diff --check
exit=0
$ git diff --check e9e7d3e7aa559f3a28f08773beec606d402aeb4f
exit=0
$ git diff --stat e9e7d3e7aa559f3a28f08773beec606d402aeb4f
 Poincare/Global/CartanSuppliedUnitRecognition.lean | 84 ++++++++++++++++++++++
 1 file changed, 84 insertions(+)
exit=0
```

The no-match token scan exited 1 as required. Both whitespace checks exited 0.
The full proof diff is retained in `proof.diff` in the evidence directory and
is reproducible with:

```sh
git diff e9e7d3e7aa559f3a28f08773beec606d402aeb4f 8f32a50d722efc0c7f5097ce6b1b629001c6bfea -- Poincare/Global/CartanSuppliedUnitRecognition.lean
```

No root build, root import modification, or integration audit was performed.
Those remain the orchestrator's integration checkpoint.

## Reproducible exact-signature probe

```lean
import Poincare.Global.CartanSuppliedUnitRecognition
set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
namespace CartanSuppliedUnitRecognition
open CartanSuppliedFinitePatchCover
variable [SecondCountableTopology M] [SimplyConnectedSpace M]

example : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M) :=
  controlled_globalLocalDevelopment

example : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitConstantCurvatureSphereRecognition3 M :=
  controlled_unitRecognition

example : UnitConstantCurvatureSphereRecognition3 M :=
  unitRecognition

example :
  CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement.{u} :=
  universal_unitRecognition

example :
  (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonConvergencePinchedLimit3 N) → PoincareConjecture.{u} :=
  poincare_of_hamiltonConvergence
end CartanSuppliedUnitRecognition
end Poincare
```

## Reproducible closure and absence probe

```lean
import Poincare.Global.CartanSuppliedUnitRecognition
#print axioms Poincare.CartanSuppliedUnitRecognition.controlled_globalLocalDevelopment
#print axioms Poincare.CartanSuppliedUnitRecognition.controlled_unitRecognition
#print axioms Poincare.CartanSuppliedUnitRecognition.unitRecognition
#print axioms Poincare.CartanSuppliedUnitRecognition.universal_unitRecognition
#print axioms Poincare.CartanSuppliedUnitRecognition.poincare_of_hamiltonConvergence
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.CartanSuppliedUnitRecognition
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      count := count + 1
      let axs ← liftCoreM (collectAxioms n)
      for a in axs do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "{n} uses {a}"
  logInfo m!"MODULE_SCAN declarations={count} nonstandard=[]"
  if env.contains `Poincare.poincare_conjecture then
    throwError "reserved theorem unexpectedly present"
  logInfo "RESERVED_THEOREM_ABSENT"
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUnitRecognition.lean
```
