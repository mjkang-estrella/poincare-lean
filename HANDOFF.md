# Handoff Snapshot

Snapshot date: 2026-09-08 (UTC)


## 2026-09-08 Connection naturality worker result

Branch `worker/connection-naturality`, base `0af3ddc6008aa53120b04d91a1caea455e89b4ae`,
verified proof head `487a4158`. The new
`ConnectionInstanceNaturality.lean` discharges both clauses of
`CurvatureInstanceTransport.ConnectionCurvatureNaturality` without `hN`.
Scalar derivatives and Lie brackets transform by the geometric identification;
Leibniz, metric compatibility, zero torsion, and Levi-Civita uniqueness give
connection naturality. Local regularity, germ locality, and curvature
tensoriality give curvature values on the canonical extensions.

The controlled-instance sphere-recognition reduction and its compatible-metric
existential form now have no naturality premise. Recognition on the controlled
instance remains an input. This result does not prove sphere recognition or
the Poincare conjecture.

Direct Lean, the focused 3072-job build, the three exact-signature probes,
and diff/token checks pass. All 20 declaration closures are exactly
`[propext, Classical.choice, Quot.sound]`. No existing Lean file or root
import changed. Commands, outputs, proof commits, and evidence paths are in
`harness/reports/connection-naturality_done.md`. This worker result awaits
orchestrator review.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.ConnectionInstanceNaturality`.

## 2026-09-08 Curvature transport worker partial

Branch `worker/curvature-transport`, base `99419b12559e2f220d868c56983a26cc10716603`,
proof head `330e7f07`. `CurvatureInstanceTransport.lean` proves inverse-J
transport of tangent-section Cn regularity in both directions for every
`n ≤ ∞`, pointwise differentiability transport, and additivity of the raw
conjugated Levi-Civita operator. These results have no naturality premise.

Connection bundling, compatibility, torsion, curvature transport, and the
controlled-instance sphere-recognition reductions retain the explicit
`ConnectionCurvatureNaturality` premise. Its pointwise connection and
curvature-tensor identities are both unproved. The result does not supply
unconditional curvature transport or sphere recognition.

Direct elaboration and the focused 3071-job build pass. All 23 declaration
closures are exactly `[propext, Classical.choice, Quot.sound]`; token and diff
checks pass. No existing Lean file or root import changed. This worker result
awaits orchestrator review. Commands, failed attempts, and commits are in
`harness/reports/curvature-transport_blocked.md`.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.CurvatureInstanceTransport`.
The next mathematical action is the cross-instance scalar exterior-derivative
chain rule stated in the report, needed for the raw conjugated Leibniz law.

## 2026-09-08 Cached audit payload wiring

Worker branch `worker/audit-payload-wiring`, base `7acd90a8`, now builds the
fixed payloads in `audit/PoincareAudit` from the four Lean-heavy audit scripts.
The generated parser checks and reserved-theorem probe remain live. Token
coverage reads each audit's own modules, including two preserved comment-only
semantic markers. The legacy-revision equivalence check passes.

Same-tree old/new comparison preserved all 112 axiom, 979 root-import, 124
semantic, and 13,397 completion result/header lines and every exit code.
Status generation fell from 448.222 s to 296.975 s in single warm-cache runs.
Both snapshots record `reserved theorem absent only`; `CURRENT_STATUS.md`
was restored and is not part of this change. All 55 script tests and 66 runtime
tests passed. Renaming one checked theorem in a scratch copy made the cached
root-import audit fail; restoring it made the target build pass again.

No proof source changed and no merge or acceptance was performed. Full
commands, timings, retained live checks, and fault evidence are in
`harness/reports/audit-payload-wiring_done.md` and its evidence archive.

Exact first action: review the worker diff from `7acd90a8`, then independently
run `python3 scripts/audit_payload_equivalence.py --check` before integration.


## 2026-09-07 Geometric metric transport worker result

Branch `worker/metric-transport-2`, base
`80fcfacea10aa364aa7bd9d3e7670b136a4f57fb`, verified proof head `51df193e`.
The new `RiemannianMetricInstanceTransportGeometric.lean` constructs `J` as
an invertible new-to-old chart derivative, proves the tangent and hom-bundle
coefficient bridges, transfers smoothness across compatible chart instances,
and constructs `transport` with the frozen geometric `transport_inner`
formula. The smoothness field is proved, not assumed. This supersedes the
previous metric worker's open geometric transport action below.

Direct elaboration and the focused 2704-job build pass. All 28 new declaration
closures are exactly `[propext, Classical.choice, Quot.sound]`; forbidden-token
and diff checks pass. No existing Lean file or root import was edited.
The result awaits orchestrator review. Actual output and proof commits are in
`harness/reports/metric-transport-2_done.md`.

The optional induced-distance equality is not proved; its exact remaining
shape is `RiemannianMetricInstanceTransportGeometric.InducedDistanceAgreement`.
A separately bundled fiber `LinearIsometryEquiv` is also not supplied.

Exact first action for independent review against the recorded base:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.RiemannianMetricInstanceTransportGeometric`.


## 2026-09-07 Metric transport worker obstruction

Branch `worker/metric-transport`, base
`7e955466b24a22af0873a73f20a3b00d7e8f05b9`, proof commit `c9eb952c`.
The new `RiemannianMetricInstanceTransport.inner_trivialization_apply`
theorem computes metric coefficients using the derivative from the fixed
anchor chart to the moving preferred chart, in both arguments. Direct
elaboration, the focused 2702-job build, forbidden-token scan, and diff
check pass. Its axiom closure is `[propext, Classical.choice, Quot.sound]`.
No existing Lean file or root import was changed.

The frozen transport preserving raw `inner` values is mathematically false.
Choosing the identity chart at zero and the global doubling chart elsewhere
on `ClosedSmoothModel 3` preserves the maximal atlas, but an unchanged
Euclidean bilinear form has coefficients `g` at zero and `4g` elsewhere in
the fixed identity-chart trivialization. The coordinate formula is verified
in Lean; the concrete counterexample has not been fully instantiated in
Lean. The worker stops under the invalid-statement rule and awaits review.
See `harness/reports/metric-transport_blocked.md` for actual command output.

Exact first action: revise the frozen `transport_inner` target to pull back
both metric arguments by the derivative from the new preferred chart to
the old preferred chart. Then prove the tangent-trivialization intertwining
law for that geometric identification.

## 2026-09-07 Controlled preferred-chart worker result

Branch `worker/controlled-chart-instance`, recorded base `c7338a642d2cf5bf3044f1ed5ca1a90bb86cf075`,
proof head `df7b3ed3`. This worker result awaits orchestrator review.
`Poincare/Global/ControlledChartInstance.lean` proves existence of a finite
atlas of original smooth charts whose preferred sources contain one positive
uniform metric ball. It proves equality of the old and new maximal atlases,
the fixed-endpoint source-neighborhood property, and scalar `ContMDiff`
equivalence for every `n ≤ ∞`. The compatible-metric theorem explicitly uses
`d.toUniformSpace.toTopologicalSpace = t` and `d.replaceTopology hd.symm` to
preserve the original topology.

The focused build completed successfully with 2702 jobs. Direct elaboration,
the frozen-target and scalar-equivalence probes, and `git diff --check`
passed. All nine theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; the forbidden-token scan is empty.
No existing Lean file or root import was edited. Details and actual compiler
output are in `harness/reports/controlled-chart-instance_done.md`.
This does not prove generic exponential joint regularity, H1/H2, or metric
and curvature transport. Those remain separate mathematical tasks.

Exact first action for independent review, after applying the worker commits
against the recorded base:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.ControlledChartInstance`.
The next mathematical task is `ClosedSmoothRiemannianMetric` transport across
the compatible instances, using the new scalar smoothness transport lemma.

## 2026-09-07 M5-glob-69 worker obstruction

Worker branch `worker/M5-glob-69`, base `d08f4a52`, proof commits `df566640`
and `8d1b76a7`. This is a worker result awaiting orchestrator review.
The frozen curvature-only successor-equality persistence theorem was not
proved or changed. The new module `SuccessorEqualityRadiusPersistence.lean`
proves that even a positive admissible radius at fixed `(x,p)` forces every
nearby total preferred chart to be injective on one common neighborhood.
It also proves that constant total extensions outside chart balls shrinking
toward a nonisolated anchor produce collisions, and that such collisions
exclude the frozen persistence conclusion under constant curvature.

The concern is equality of total partial-homeomorphism coercions outside
their sources. The allowed chart choices do not impose a common neighborhood
of injectivity there. A recharted round-sphere counterexample is described
in `harness/reports/M5-glob-69_blocked.md`, but its metric and curvature have
not been instantiated in Lean. The verified result is a conditional
obstruction, not a complete Lean refutation or a proof of H2.

The new module passed direct Lean elaboration and the focused `lake build`
with 3579 jobs. All six new theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; forbidden-token scans are empty.
No existing Lean file, root import, mission, task, or ledger was changed.

Exact first action: instantiate the report's shrinking preferred charts on
the round sphere, then apply
`SuccessorEqualityRadiusPersistence.preferredChartCollisionAccumulation_of_shrinking_constant_extensions`
and
`SuccessorEqualityRadiusPersistence.not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation`.
Review the frozen statement before resuming source/target flow-uniformity work.

## 2026-09-07 Validation refactor

Branch `worker/audit-loops`, merged to `main` after the checks below. The
scaffold audits were the validation bottleneck: `root_import_audit.sh` and
`axiom_audit.sh` rescanned all 23,309 harvested theorem names once per
route check and spawned one `rg` process per lookup, `write_status_summary.sh`
ran every audit twice through `completion_audit.sh`, and every script
required an `rg` binary that this Mac does not expose to non-interactive
shells (the audits aborted with `rg: command not found`).

Changes, each preserving the printed PASS/FAIL/MISSING lines and exit
semantics:

- The route-naming checks are single `awk` passes over the harvested name
  list (`route_awk_lib` in the axiom and root-import audits; the semantic
  family loops likewise). Same-tree comparison: old and new stdout are
  byte-identical for the axiom (112 result lines), root-import (979), and
  semantic (124) audits; renaming a route theorem makes old and new fail with
  the same single FAIL line and exit 1.
- `scripts/bin/rg` is a stdlib-only Python subset of ripgrep, prepended to
  `PATH` by every audit script only when no `rg` binary exists. With no `rg`
  on `PATH`, the interface, shape, mathlib-gap, semantic, root-import, axiom,
  and formalization audits print the same result lines as with ripgrep.
- `write_status_summary.sh` records each gate's exit status and passes the
  directory to `completion_audit.sh` as `COMPLETION_AUDIT_GATE_RESULTS_DIR`;
  the completion audit prints `REUSE:` under each gate header and aborts on a
  recorded nonzero status. Standalone `sh scripts/completion_audit.sh` is
  unchanged.
- The axiom audit prints `FAIL: axiom footprint Lean check did not elaborate`
  with the first Lean lines instead of exiting silently.
- The completion and formalization audits' placeholder scan is
  `scripts/lean_placeholder_scan.py`, which strips `--` and nested `/- -/`
  comments before matching. The previous `rg` scan flagged docstring prose
  (`admit`, `postulate`, `constant`) in four modules written after June, which
  made the completion boundary read as "unexpected completion audit
  failures" although the only real failures are the absent reserved theorem.
  On this tree the scan reports zero hits.
- `scripts/theorem_contract_audit.sh` prints its `== Theorem contract audit ==`
  header again; the 2026-09-05 rewrite to `frozen_contract_audit.py` had
  dropped it while `completion_audit.sh` still requires that sentinel in
  `CURRENT_STATUS.md`, so the snapshot sentinel check failed on the first
  regeneration.
- Tests: `scripts/tests/test_rg_fallback.py`,
  `scripts/tests/test_completion_gate_reuse.py`,
  `scripts/tests/test_lean_placeholder_scan.py`; the harness runtime, deploy,
  and worker suites are unchanged and green.

Warm-cache timings on the same tree, sequential runs:

| Audit | Before | After (ripgrep) | After (fallback) |
| --- | ---: | ---: | ---: |
| axiom footprint | 522 s | 55 s | 74 s |
| root import | 524 s | 64 s | 93 s |
| semantic surface | 178 s | 81 s | 93 s |
| interface | 14 s | 13 s | 22 s |

Integration checkpoint on `main` at `b807cd42`: `sh scripts/write_status_summary.sh`
(build plus every audit once, then the completion audit reusing the recorded
gate statuses) completed in 518 s and regenerated `CURRENT_STATUS.md` with
every scaffold audit at status 0, completion audit status 1, and completion
boundary status `reserved theorem absent only`.

Not merged: branch `worker/audit-refactor` (commit `9c2c7584`) holds an
interrupted agent's extraction of the Lean check payloads into a non-default
`lean_lib PoincareAudit` (`audit/PoincareAudit/*.lean`,
`scripts/audit_payload_equivalence.py`). It would let Lake cache the Lean half
of the audits. On 2026-09-07, after adding the missing root module
`audit/PoincareAudit.lean` and moving the module docstrings below the
`import` lines (two follow-up commits on that branch), its own `--check`
reports every module as a lossless extraction of the legacy heredocs (83,887
checks), `lake build PoincareAudit` succeeds in 35 s on a warm cache with all
seven payload modules elaborating under `#guard_msgs` and `#std_axioms`, and a
no-op rebuild takes 2 s. No audit script consumes the library yet: wiring it
in means replacing the heredoc elaborations and reworking the
self-referential token-coverage checks that read the script text, so it stays
a separate reviewed change.

## 2026-09-07 Boundary correction

Checked in `/Users/mjkang/Develop/poincare` on branch `main`, base `b2b96fc2`.
Two prose ledgers were behind Lean; both are corrected here with theorem-level
evidence (`harness/reports/M5-glob-68_closure.md`).

1. The 2026-09-04 "exact next analytic action" below was already done by
   commit `723b4132`: `CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison`
   (`Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean`)
   removes the `UniformClosedRiemannianMetricLowerComparison` input, and
   `NormalizedFlowFormalProfilePositiveEinstein.lean` exposes the
   `...OfCompactTensorControl` constructors. Its axiom footprint is
   `[propext, Classical.choice, Quot.sound]`. The remaining open inputs of
   `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl`
   are, by exact name: `compactTensorReferenceControl :
   CompactReferenceMetricTensorFamilyData reaction.K reaction.metric`,
   `hequicontinuous`, `hpointwiseCompact`, and `scalarSubordinateGeometry`,
   plus the `reaction` record itself, whose only producer needs
   `HamiltonPinchingCoreData3` (normalized-flow existence with Hamilton's
   eigenvalue floor). These are the Hamilton-1982 analytic wall; no producer
   of any of them exists in the repository.

2. The Cartan "F-transition law" that `harness/ledger.json` and reports
   M5-glob-21..67 call blocked was closed curvature-only by commit `d8f2e43c`
   (2026-07-17), never recorded:
   `UniformAnchoredFTransition.exists_cartanChartMap_christoffelAt_F_transition_law_curvature_only`,
   `UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law`,
   `DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`.
   The M5-glob-49..67 third-variation/selector tower is not on the closing
   path. Reports through M5-glob-67 are historical.

3. The live Cartan boundary is now recorded in Lean:
   `Poincare/Global/CartanTwoNeighborhoodDevelopment.lean` defines H1
   (`UnitCurvatureSuccessorDataNeighborhood3`) and H2
   (`UnitCurvatureSuccessorEqualityNeighborhood3`) and proves
   `globalLocalDevelopment_of_two_neighborhoods`,
   `unitConstantCurvatureSphereRecognition3_of_two_neighborhoods`,
   `universalUnitRecognition_of_two_neighborhood_statements`, and
   `Poincare.poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods`,
   each with axiom footprint `[propext, Classical.choice, Quot.sound]`.
   Constant curvature proves only the fixed-anchor slices of H1 and H2
   (`universalSuccessorDataLocus_vertical_mem_nhds_of_curvature`,
   `fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature`);
   the joint neighborhoods as anchors and alignments move are open.
   The reviewed obligations are machine-readable in
   `harness/v2/missions/unit-recognition.json`; on this tree

   ```sh
   python3 scripts/theorem_registry.py graph \
     --mission harness/v2/missions/unit-recognition.json --require-closed
   ```

   exits `2` with `successor-data-neighborhood`,
   `successor-equality-neighborhood`, and `unit-recognition` open and the
   reduction `checked_with_hypotheses`.

The module is wired into `Poincare.lean`; `LEAN_NUM_THREADS=1 lake env lean
Poincare.lean` succeeded on this tree. The independent root probe still reports
`Unknown identifier Poincare.poincare_conjecture`; the repository is not
complete.

Exact first action for the next agent: attack H2 through its equivalent
`DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence g`
(persistence of the radius of
`DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`
under motion of the anchors), or H1 through
`CartanGenericSuccessorDataLocalCover.FixedChartLocalGenericDataPersistence g`
(persistence of the successor datum's open conditions and strict derivative
as the anchors move, using `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`).
Freeze the chosen statement with a schema-2.1 contract before dispatch.

## 2026-09-08 Repair track and audit payload caching

Integrated on `main` after the orchestrator's gate and review (codex workers,
`harness/dispatch_codex.sh`):

- `Poincare/Global/ControlledChartInstance.lean` (task
  `controlled-chart-instance`): a compact manifold admits a finite
  `ChartedSpace` instance with the same smooth maximal atlas whose preferred
  chart sources contain a uniform ball around their anchors
  (`exists_controlled_chartedSpace_source_persistence`,
  `exists_controlled_chartedSpace_of_compatibleMetric`), and scalar
  smoothness agrees between such instances
  (`scalarContMDiff_iff_of_atlas_subset`).
- `Poincare/Global/RiemannianMetricInstanceTransport.lean` (task
  `metric-transport`, stopped as statement-invalid): the hom-bundle
  trivialization formula `inner_trivialization_apply`; the raw-fiber transport
  contract was refuted because the identification `TangentSpace I x = E` is
  chart-dependent.
- `Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean` (task
  `metric-transport-2`): the geometric transport `transport inst' h g` with
  `transport_inner` (pullback by the chart-change derivative `J x` in both
  slots), including the smoothness of the transported section. The induced
  distance comparison is the exact remaining `def InducedDistanceAgreement`.
- `Poincare/Global/CurvatureInstanceTransport.lean` (task
  `curvature-transport`, stopped with a verified partial): unconditional
  vector-field transport with regularity equivalence in both directions, the
  conjugated derivative and its additivity; the bundled connection, metric
  compatibility, zero torsion, Levi-Civita agreement, constant-curvature
  transport, and the recognition reduction
  (`exists_controlled_recognition_reduction`: any compatible metric gives a
  finite controlled instance to which unit recognition reduces) are all
  conditional on the single explicit boundary
  `ConnectionCurvatureNaturality` (the conjugated derivative equals the new
  Levi-Civita connection on differentiable fields, and curvature values
  conjugate by `J`). Sixteen theorems, standard axiom footprint.
- Dispatched next: `harness/tasks/connection-naturality.md` (discharge that
  boundary: cross-instance chain rule for scalar derivatives, Lie-bracket
  naturality, Leibniz and compatibility for the conjugated operator,
  uniqueness, curvature tensoriality).

Validation: the audit payload wiring (task `audit-payload-wiring`) is merged.
The Lean check payloads of the axiom, root-import, semantic, and completion
audits live in the non-default Lake library `PoincareAudit` (`audit/`), built
and cached by Lake; `scripts/audit_payload_equivalence.py --check` proves the
modules are a lossless extraction of the legacy heredocs at
`b2b96fc2` (83,887 checks and 10,210 axiom probes). The four scripts shrank
from 129,000 to 25,000 lines. Same-tree comparison on `main` after the merge:
sorted result lines identical for all four audits (112, 985, 124, and 13,390
lines); warm timings axiom 56 s to 48 s, root import 68 s to 57 s, semantic
82 s to 46 s, standalone completion 488 s to 415 s. The worker's evidence
archive is kept outside git in `harness/logs/`.

## 2026-09-08 H1 and H2 are atlas-dependent as stated

Three codex workers (tasks M5-glob-69, 70, 71; `harness/dispatch_codex.sh`)
attacked H2, H1, and the joint regularity of the exponential chart in its
anchor. All three stopped under the contract's invalid-statement rule with
Lean-checked obstructions, consolidated in
`harness/reports/M5-glob-72_statement_refutation.md`: the statements are
formulated for the arbitrary preferred charts `chartAt E x`, and a
`ChartedSpace` instance may exclude a fixed point from every other chart, so
`GenericJointRegularity` is false for every metric on the punctured model
(`Poincare/Global/GenericJointRegularityCounterexample.lean`), H1 forces
`PreferredChartSourcePersistence` (`FixedChartSuccessorDataPersistence.lean`),
and H2 forces chart injectivity on common neighborhoods
(`SuccessorEqualityRadiusPersistence.lean`). All new modules pass the gate with
the standard axiom footprint and are wired into the root import.

The mission `harness/v2/missions/unit-recognition.json` therefore records
obligations that cannot be discharged in their current form; its description
says so. The checked reduction from H1 and H2 remains valid but is now known to
start from unprovable premises for pathological atlases. The Hamilton-front
registration (`harness/v2/missions/hamilton-front.json`, worker
`hamilton-front-mission`, gated and merged) is unaffected.

Exact first action: task `harness/tasks/controlled-chart-instance.md`
(dispatched to a codex worker at high effort): prove that a compact manifold
admits a `ChartedSpace` instance with the same smooth structure whose
preferred-chart sources contain a uniform ball around their anchors, from a
finite subatlas and a Lebesgue number. The subsequent steps are metric and
curvature transport across such instances and re-running the Cartan chain over
a controlled `CartanSourceExponential.Family`.

## 2026-09-07 Hamilton front registration

Worker branch `worker/hamilton-front-mission`, based on
`aa82826aec916ad9339e2da1049f80009cdf2c7a`, adds
`Poincare/Global/HamiltonFrontStatements.lean` and the mission
`harness/v2/missions/hamilton-front.json`. The structure preserves exactly the
five inputs of the compact-tensor formal-profile constructor, including its
independent compact-parameter universe. Checked reductions reach universal
positive-Einstein existence, Hamilton convergence, and the conditional smooth
`PoincareConjecture` composition with Cartan H1/H2. Neither universal Hamilton
inputs nor the unconditional Hamilton endpoint is proved. The worker report
`harness/reports/hamilton-front-mission_done.md` records compiler, registry, and
test evidence, including an existing ripgrep output-order test flake and a
passing unchanged rerun. Exact first action for the orchestrator: independently
run `python3 scripts/theorem_registry.py graph --mission
harness/v2/missions/hamilton-front.json --require-closed` and review the five
input types before accepting or decomposing this mission.

## 2026-09-05 Main integration

The integration checkout is now `/Users/mjkang/Develop/poincare`, branch `main`.
The merge retains the old local-main history and incorporates
`codex/proof-workflow-improvements` at `5d408763`, the repeated-interruption
handling at `81cde044`, and the focused-review implementation at `a87c80a6`.
The earlier proof-worker branches are included through their reviewed
cherry-picked changes. Existing worktrees and their evidence are preserved.

The focused reviewer now uses the same schema-2.1 declaration-probe generator
as the runtime gate. A regression test checks both strict deliverables and
legacy probe compatibility. Integration preserves both the execution-backlog
target and the independent integration-batch setting.

The combined runtime suite passed 66 tests, deployment suite 49, worker suite
33, and Pi suite 94 with 11 skips. The Lean sources, root imports, toolchain,
and dependency manifest are byte-for-byte identical to the verified
`5d408763` tree; no Lean theorem was changed during these merges. No live
model or persistent harness service was changed by this Git integration.

The next action remains the reviewed mission check, run from `main`:

```sh
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
```

The source-existence, covering-construction, and final Poincare obligations
remain open. The historical verification limitations below still apply.

## 2026-09-05 Reviewed topology and proof-workflow checkpoint

The active integration worktree is
`/Users/mjkang/.codex/worktrees/proof-workflow-improvements/poincare`, branch
`codex/proof-workflow-improvements`, based on the previously pushed
`64c9f999c9c699cb52e87ea36fad294d43b774d4`. The implementation commits are
`d73eb030` for the topology source, `500ecdd3` for the theorem registry, and
`84ca80dd` for strict statement contracts. This section supersedes older
descriptions of the active branch and theorem-selection workflow below.

The new `GroundedTopologySource` retains one decomposition and trace, their
owning surgery package, and a Perelman production source on the matching flow.
`GroundedTopologyPresentation` selects a compatible atlas on the same topology.
The independent read-back rejected an earlier draft which required the original
arbitrary topological atlas to be differentiable; the accepted types remove
that requirement. The new conditional assembly passes the presentation's full
source into the covering premise.

`GroundedTopologySource.active_components_cover` proves coverage of the original
space at every recorded stage by backwards induction through the actual parent
maps. Disjointness gives unique component membership. The high-Ricci membership
lemma transfers a point using the actual trace-flow equality and locates its
spatial point in that partition. It does not locate the point at the stage's
event time or in the event region.

These are sets in the original manifold, not physical time-slice manifolds.
Their carriers still lack the topology and embedding requirements needed for
geometric reconstruction. The source also does not identify event regions with
high-curvature regions. Both universal chosen-atlas source existence and
`GroundedTopologyThreeSphereCoveringStatement` remain open, as does treatment
of a zero-event history. No final Poincare theorem is supplied by this work.

The registry reads exact types and dependencies from Lean after focused builds.
Its reviewed mission is `harness/v2/missions/grounded-topology.json`. Planned
edges stay separate from checked proof dependencies; a conditional theorem
cannot discharge an unconditional obligation. Expected statements include
transitive semantic fingerprints. Catalogs bind to source identity, and stale
or edited evidence is rejected.

New mathematical Tasks use opt-in schema `2.1`, as required by the updated
orchestrator prompt. Every deliverable has a frozen type and universe list,
with definition hashes and an independent read-back tied to the snapshot.
Pinned source files are streamed through hash checks without being copied into
worker prompts. Existing context limits and broker scope remain unchanged.
Version `2.0` remains available for historical tasks. The curated theorem audit
now checks exact types and axiom footprints; it no longer demands reflexive
`theorem_eq` companions. The full completion audit also rejects a failed or
nonstandard final axiom check instead of printing it and continuing.

The full completion run passed build, interface, mathlib-gap, semantic-surface,
root-import, and axiom checks, then exposed four older shape-parser false
positives. That parser treated qualified methods such as `Type.ofSource` as
definitions of `Type`. It now limits the legacy name convention to unqualified
definitions, always records filenames, and preserves the existing checks on
those definitions. Four regression tests and the live shape audit pass after
the repair. The five curated contracts were then rerun and passed. The initial
completion log is preserved; the entire completion script was not repeated
after this parser-only repair. No successful full completion audit is claimed.
An independent final root probe still reports
`Unknown identifier Poincare.poincare_conjecture`.

Independent verification passed the focused Lean checks and axiom probes for
all eight new proof declarations, the five curated contracts, and a serialized
4,105-target full build. The runtime suite passed 63 tests, worker suite 33,
registry suite 16, and curated-audit suite 10. The Pi suite completed 94 tests
with 14 environment-dependent skips. These suites include changed secondary
types, forged or stale review evidence, unsafe proof-typed definitions, changed
dependent definitions, false graph closure, and omitted multi-megabyte pinned
sources. The warm-cache pilot medians were 2.60 seconds for statements and
2.52 seconds for assembly, measured while the completion audit also ran; no
before/after speedup is claimed.

Local implementation task snapshots and their corrected directory-scope
revisions are under `harness/v2/tasks`; the invalid initial spellings are
preserved under `tasks/history`. These records were not dispatched to the
persistent Harness database. All local worker leases are released in
`proof-workflow-improvements-leases.closed.json`. The live model services and
persistent deployment were not modified.

The exact first action is:

```sh
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
```

Exit `2` denotes valid evidence with open obligations. Before dispatching the
next proof, split the `covering-construction` obligation at a geometric carrier
or gluing interface and review its exact statement. Do not infer carrier
embeddings, spherical pieces, or a covering from the existing partition fields.
See `docs/PROOF_WORKFLOW.md` for commands and the precise scope of the pilot.

## Project Truth

- Mac integration repository: `/Users/mjkang/Develop/poincare`, branch `main`.
- Harness v2 pivot base: `7ce913d87be973256517ea862fb4d3dbfae7cb82`,
  equal to `origin/main` before the implementation. The Mac control-plane
  commit is `8114cfe2a592d22ea1973441c0fb086c72e8826d`; the bounded proof Job
  commit is `f266c2fd4a8c23ca55bad0a09f35cc638e6842c0`. Inspect the current
  commit and working tree before acting; preserve any later changes.
- An exact stdin probe at the pivot base and again at the deployed release
  candidate failed with `Unknown identifier Poincare.poincare_conjecture`.
- The repository is still incomplete. Completion means Lean checks exactly
  `Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`, its
  axiom footprint is allowed, and the full completion audit passes in a clean,
  stable integration checkout.

`CURRENT_STATUS.md` was generated on 2026-06-30 and `harness/ledger.json` ends
with the 2026-07-07 legacy selector-assembly work. Both are historical until
regenerated or revalidated against the current commit. Lean and the current
diff remain authoritative.

## 2026-09-04 Formal Profile and Grounded-Interface Checkpoint

The active integration worktree is
`/Users/mjkang/.codex/worktrees/formalization-until-6/poincare` on branch
`codex/formalization-until-6`. Its clean checkpoint is
`77fb1a54ba95f099ffe891d54190aec7a2f80d60`, 82 commits ahead of unchanged
`origin/main` at `bc076f1e893c6ba834729f8bcb359a1f400a3e72`.

The scalar `C0,3` compactness route no longer requires every profile limit to
be realized by a smooth Riemannian metric. The new verified chain is:

```text
compact componentwise scalar third-jet profiles
  -> formal metric and inverse on the nondegenerate locus
  -> formal Christoffel jets through order two
  -> formal curvature, Ricci, covariant Ricci, and norm contraction
  -> exact agreement with genuine chart quantities
  -> finite fixed-anchor cutoff-one cover
  -> global UniformCovariantRicciDerivativeNormBound
  -> reaction-decay positive-Einstein analytic data
```

The principal endpoint is
`NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfiles`.
Its remaining nondegeneration input is the explicit
`UniformClosedRiemannianMetricLowerComparison`; the former
`hForwardProfileLimitsRealized` premise is absent. The bounded-component
variant is also proved. All formal curvature expressions agree exactly with
the repository's genuine `anchorChartCurvatureFamily`, Ricci,
covariant-Ricci, inverse-metric, and sixfold norm formulas.

The grounded surgery interface was also repaired. The constructorless
`HasSingularityModelBlowupClassification` marker is now a proof-bearing
classification source together with surjectivity onto every pointed
rescaling index. The five component classification maps compose to this
coverage theorem in `SingularityModelBlowupCoverage.lean`. No existing
payload proves any of those five surjectivity claims, so that remains genuine
Perelman work rather than an artificial inconsistency.

On the topology side,
`ExtinctionThreeSphereCoveringProjectionStatement` records the non-circular
post-extinction target `exists p : ThreeSphere -> M, IsCoveringMap p`.
Simply connected covering-space rigidity turns it into the sphere
homeomorphism. The older full topology package still stores the final
homeomorphism and is not an honest proof plan; its decomposition and surgery
trace realization predicates also remain empty inductives.

At this checkpoint, a serialized 4,095-target `lake build`, root elaboration,
interface audit, semantic-surface audit, 6,008-declaration theorem-contract
audit, root-import audit, and axiom audit all pass. The exact probe still
fails with `Unknown identifier Poincare.poincare_conjecture`; the repository
is not complete.

The exact next analytic action is to derive a pointwise inverse-chart volume
density lower bound from
`CompactReferenceMetricTensorFamilyData.volume_le`, using the proved
`inverseChart_hausdorffChartDensityEquality`. Combined with its uniform metric
upper bound and the three-dimensional determinant inequality, this should
produce `UniformClosedRiemannianMetricLowerComparison` and remove the last new
nondegeneration input. In parallel mathematical terms, the independent hard
frontiers remain classified-model coverage of all pointed rescalings and
Cartan successor-equality persistence needed for a total developing map.

## Completed Bounded Deployment Exercise

The first Harness v2 exercise was
`automatic-scalar-derivative-constructor` revision 4, accepted from Job
`automatic-scalar-derivative-constructor-r4-a03`, frozen at
`7ce913d87be973256517ea862fb4d3dbfae7cb82`. Attempts `r4-a01` and `r4-a02`
were terminalized and preserved; neither immutable Job was relaunched after a
supervisor record existed.

Its single allowed source file is:

```text
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean
```

The accepted edit adds the frozen `ofReactionFields` constructor and derives
`scalarTimeDerivativeJointContinuous` from `reaction.jointMetricEntries` via
the existing theorem
`scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three`.
The constructor may not add `ScalarTimeDerivativeJointContinuous` or scalar
domination as a replacement argument. Leanstral made the one-file edit through
Pi's scoped patch tool, its worker `lean_check` passed, and Codex independently
reran all six frozen acceptance commands plus the canonical exact-type
declaration probe before committing and accepting it. The accepted Job gate is
`harness/v2/state/jobs/automatic-scalar-derivative-constructor-r4-a03/gate.json`
on `mj-zima`.

The previous broad positive-time-overlap and compact-history surfaces remain
important context, but this narrower constructor is the selected first
dependency reduction. Do not redispatch the last legacy ledger entry.

## 2026-07-20 Bochner Continuity Checkpoint

The integration checkout advanced from
`ee4a8e5382f2b664a9843fc6b8ec237c535a9460` to the accepted proof commit
`bec8bc4a5a514a6ba502e2a945f96317be397a5c`. Harness Task
`cov-ricci-bochner-continuity-inline` revision 2 was accepted from Job
`cov-ricci-bochner-continuity-inline-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-continuity-inline-r2-a01/gate.json`
on `mj-zima`. The worker lease is released and no Job remains active.

The accepted theorem is
`Poincare.continuous_joint_covRicciNormSqAt_of_bochner_fields`. It uses the
Ricci Bochner identity to derive joint continuity of `covRicciNormSqAt` from
joint continuity of the Ricci-norm Laplacian and rough-Ricci pairing, together
with the existing pointwise smoothness hypotheses. Its focused Lean gate,
canonical frozen-type `import Poincare` probe, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit retained only its known direct-import ledger failures; this checkpoint
also wires the previously accepted automatic scalar-time-derivative module
directly into `Poincare.lean`, reducing that ledger by one.

## 2026-07-20 Bochner-Fields Constructor Checkpoint

The integration checkout advanced from
`12b700a27f31e7fb521eb1bec1845fbf4e842e61` to accepted proof commit
`c5a80d17b236b82d5daac96982e9edf87fdb89b4`. Harness Task
`cov-ricci-bochner-fields-constructor` revision 2 was accepted from Job
`cov-ricci-bochner-fields-constructor-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-fields-constructor-r2-a01/gate.json`
on `mj-zima`. No Job or file lease remains active.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerFields`.
It installs `reaction.topologicalSpaceK`, derives joint covariant-Ricci norm
continuity with `continuous_joint_covRicciNormSqAt_of_bochner_fields`, and
calls `ofReactionFields`, so neither joint covariant-Ricci norm continuity nor
scalar-time-derivative continuity is an explicit constructor argument. The
canonical frozen-type probe passed and `#print axioms` reported only
`propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `cov-ricci-bochner-fields-constructor-r1-a01` is preserved as
interrupted evidence: its draft omitted the local topology instance, then
exhausted its 12,000-token budget on stale correction hunks. Revision 2
recorded that exact failure and passed in a fresh supervised Pi session. Its
focused gate, targeted module build, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit has exactly the same four known direct-import ledger failures as before
this checkpoint, with no new failure.

The exact completion probe at the integrated commit still reports
`EXACT_DECLARATION_PROBE=absent`; `Poincare.poincare_conjecture` is not
declared. The next theorem-shaped action is to probe and freeze a fixed-target
lifting constructor that packages `ofBochnerFields` for the `analytic` field
of the automatic-finite-nerve ODE-primitive compact-history boundary, rather
than adding another alias or assuming the already assembled analytic record.
Before claiming any Job at the new base, publish and verify the immutable Lake
cache for the final clean HEAD. Do not redispatch the obsolete broad
`cov-ricci-bochner-constructor` Task; it retains only an interrupted Job and
could not be marked superseded because the accepted replacement Task did not
name that older Task in its immutable `supersedes` field.

## 2026-07-21 Bochner Pairing-Regularity Reduction Checkpoint

The integration checkout advanced from
`682560dcd37dd510b51b5a789fe8efc71ed8d97c` through the accepted proof
integration recorded by this commit. Harness Task
`bochner-pairing-from-ricci-norm` revision 3 was accepted from Job
`bochner-pairing-from-ricci-norm-r3-a01`; its reviewed worker commit is
`e216ed5bfc0e6dd098ea445eafc06d7048d3e669` and its strict gate is
`harness/v2/state/jobs/bochner-pairing-from-ricci-norm-r3-a01/gate.json` on
`mj-zima`. All Jobs and leases for the Task are terminal and released.

The accepted theorem is
`Poincare.continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`. It derives
the pairing differentiability input to the existing Bochner continuity theorem
from C2 regularity of `ricciNormSqAt`, using
`covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two`.
Consequently the new theorem requires the Ricci-norm regularity field plus the
Ricci second-derivative, Laplacian, and rough-pairing continuity fields, but no
independent `hPairDiff` hypothesis. The canonical frozen-type probe passed and
`#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `bochner-pairing-from-ricci-norm-r1-a01` is preserved as
interrupted evidence after it exhausted its bounded Pi context without a patch.
Revision-2 Job `bochner-pairing-from-ricci-norm-r2-a01` found the correct proof
but was rejected because its first scoped patch request was broker-rejected and
the immutable Task allowed exactly one patch call. Revision 3 froze the valid
patch bytes and completed exactly one scoped patch, one Lean check, and one diff
request in a fresh supervised Pi session.

Focused elaboration, the frozen acceptance array, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit retains exactly its four known missing direct imports: the two Cartan
tail-overlap reductions, the scalar-variation joint-continuity reduction, and
the automatic finite-nerve compact-history boundary module. The exact
completion probe still reports `EXACT_DECLARATION_PROBE=absent`.

The next theorem-shaped action is to freeze an
`NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3`
constructor that takes the norm-field inputs above and installs the analytic
record through `continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`,
removing `hPairDiff` at the constructor boundary. Before claiming a Job at the
new integration base, complete the required root build and publish and verify a
new immutable Lake cache for that exact clean HEAD.

## 2026-07-21 Bochner Norm-Fields Constructor Checkpoint

The integration checkout advanced from
`7b216e8c246a309f2ec43ef59507799ec0e8d980` to accepted proof commit
`c39ad01f334e372d169428f8fd874b070f7d644d`. Harness Task
`cov-ricci-bochner-norm-fields-constructor` revision 2 was accepted from Job
`cov-ricci-bochner-norm-fields-constructor-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-norm-fields-constructor-r2-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no Harness Job or
file lease remains active.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerNormFields`.
It installs the reaction parameter topology, derives joint covariant-Ricci
norm continuity through
`continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`, and calls
`ofReactionFields`. Its frozen constructor type therefore retains the Ricci
norm C2, Ricci second-derivative, Laplacian-continuity, rough-pairing
continuity, and subordinate-geometry inputs but has no independent
`hPairDiff`, joint covariant-Ricci continuity, or scalar-time-derivative
continuity argument. The canonical exact-type probe passed and `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `cov-ricci-bochner-norm-fields-constructor-r1-a01` is preserved
as interrupted evidence. It eventually produced the same valid one-file patch
and passed its brokered focused Lean check, but its final report hit
`stopReason=length`, so the Harness correctly refused to route it to review.
Revision 2 froze those exact patch bytes and completed exactly one scoped
patch, one Lean check, and one diff request in a fresh supervised Pi session.

The frozen acceptance array, targeted module build, canonical declaration
probe, root elaboration, interface, semantic-surface, theorem-contract, and
axiom audits passed. The root-import audit retains exactly its four known
baseline direct-import gaps—
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`, and the
automatic-finite-nerve joint-covariant-Ricci tail-overlap compact-history
boundary—and this proof commit changes neither `Poincare.lean` nor that audit.
The exact completion probe still fails with unknown identifier
`Poincare.poincare_conjecture`.

The next theorem-shaped action is to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFields`
in the existing automatic-finite-nerve boundary module. Freeze its type as the
current `ofBochnerFields` type with `hPairDiff` removed, and construct its
`analytic` field through the newly accepted analytic-data constructor. The
exact first action in the next cycle is to create and schema-validate that
single-file Task at the final clean HEAD; before claiming its first Job, run
the Task-bound root-build provenance recorder and publish and verify the new
immutable Lake cache for that exact base.

## 2026-07-21 Automatic Finite-Nerve Norm-Fields Boundary Checkpoint

The integration checkout advanced from
`0d89b5a67f9577e16f75601e8ac7cad20dee0901` to accepted proof commit
`c778276a36de0bacda0462a95f002d50f7d52129`. Harness Task
`automatic-finite-nerve-bochner-norm-boundary-constructor` revision 2 was
accepted from Job
`automatic-finite-nerve-bochner-norm-boundary-constructor-r2-a01`; its strict
gate is
`harness/v2/state/jobs/automatic-finite-nerve-bochner-norm-boundary-constructor-r2-a01/gate.json`
on `mj-zima`. All Jobs for the Task are terminal and no file lease remains
active.

The accepted declaration is
`Poincare.AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFields`.
It constructs the boundary's analytic field through the accepted analytic-data
`ofBochnerNormFields` constructor. Its frozen type retains the tetrahedral-star,
reaction, compact tensor, Ricci-norm C2, Ricci second-derivative,
Laplacian-continuity, rough-pairing-continuity, subordinate-geometry, ODE
primitive, and compact-history inputs, while removing the independent
`hPairDiff` premise. It also takes neither joint covariant-Ricci continuity nor
scalar-time-derivative continuity as a replacement argument. The canonical
exact-type probe passed and `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound`.

Revision-1 Job
`automatic-finite-nerve-bochner-norm-boundary-constructor-r1-a01` is preserved
as interrupted evidence. Its broad prompt produced two broker-rejected patch
requests, then terminated fail-closed with an empty worker patch after a
partial Pi stream and tool-crosscheck disagreement. Revision 2 froze a
7,409-byte patch that Codex had independently checked with `git apply --check`
and full stdin elaboration; its fresh Pi session then completed exactly one
scoped patch, one focused Lean check, and one patch-form diff request.

The frozen Task gate, a private incremental 4,065-job root build, root
elaboration, interface, semantic-surface, theorem-contract, and axiom audits
passed. The root-import audit retains exactly its four known direct-import
ledger failures: the two Cartan tail-overlap reductions, the scalar-variation
joint-continuity reduction, and the automatic finite-nerve joint-covariant-
Ricci tail-overlap compact-history boundary. The exact completion probe still
reports unknown identifier `Poincare.poincare_conjecture`.

The next theorem-shaped action is to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`
in the existing positive-time-overlap boundary module. Freeze its type as the
new ODE-primitive constructor type with the primitive moving input replaced by
`FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3`
and compact-history feedback indexed by its existing conversion. Construct the
analytic field through the accepted analytic-data norm-fields constructor and
do not reintroduce `hPairDiff`. Before claiming the first Job at the final clean
HEAD, record, publish, and verify a new immutable Lake cache for that exact
base.

## 2026-07-21 Positive-Time and Tail-Overlap Boundary Checkpoint

The integration checkout advanced from
`3d8dc9f20a5b943d1fc55019ad968713947ca137` through accepted proof commits
`4b1f19736735a536ab2e5c6023da4fcfdf441bbb`,
`6bc720d764a74893e04ec27cc32e04272c0677f9`, and finally
`079292fae8a23cbb88082f2270a5e1c3f95cddf9`.

Harness Task
`automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor`
revision 2 was accepted from Job
`automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor-r2-a01`.
It adds
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`.
Revision-1 evidence is preserved as interrupted after Pi's stream and broker
events could not be reconciled, even though its later broker-applied patch was
mathematically valid. Revision 2 froze those exact patch bytes and passed a
fresh three-call session. Its strict gate is
`harness/v2/state/jobs/automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor-r2-a01/gate.json`.

Task `automatic-positive-time-tail-bochner-norm-boundary-constructor`
revision 1 was then accepted from Job
`automatic-positive-time-tail-bochner-norm-boundary-constructor-r1-a01`.
Its declaration
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsAndTailOverlap`
replaces the positive-time moving input by the exact tail-only input, using the
verified tail-to-positive-time adapter while preserving the compact-history
index definitionally. Its strict gate is
`harness/v2/state/jobs/automatic-positive-time-tail-bochner-norm-boundary-constructor-r1-a01/gate.json`.

Finally, Task `automatic-scalar-tail-boundary-sphere-conclusion` revision 2
was accepted from Job
`automatic-scalar-tail-boundary-sphere-conclusion-r2-a01`. It defines the
named scalar-derivative/tail-overlap compact-history boundary, converts it to
the verified positive-time boundary, and proves
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.sphereConclusion`.
It also adds the single direct `Poincare.lean` import required to expose this
declaration canonically. Revision-1 Job
`automatic-scalar-tail-boundary-sphere-conclusion-r1-a01` is preserved as
rejected evidence: all focused commands passed, but its frozen scope forbade
the root import, so the mandatory `import Poincare` declaration probe returned
unknown identifiers. Revision 2 records that exact failure and its strict gate
is
`harness/v2/state/jobs/automatic-scalar-tail-boundary-sphere-conclusion-r2-a01/gate.json`.

Every accepted Job used exactly one scoped patch, one focused Lean check, and
one patch diff. Codex independently checked the exact frozen types and observed
only `propext`, `Classical.choice`, and `Quot.sound`. Post-integration root
elaboration and the interface, semantic-surface, theorem-contract, and axiom
audits passed. The root-import ledger shrank from four failures to exactly
three: the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe still reports unknown identifier
`Poincare.poincare_conjecture`; no unconditional final theorem exists.

No Harness Job or file lease remains active. The next theorem-shaped action is
to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`
in the now root-visible tail-boundary module. Freeze its arguments as the
accepted positive-time `ofBochnerNormFieldsAndTailOverlap` type, but return the
new scalar-tail structure and store the original tail input directly. The
exact first action in the next cycle is to create and schema-validate that
single-file Task at the final clean HEAD; before claiming its Job, record,
publish, and independently verify a new immutable Lake cache for that exact
base.

## 2026-07-21 Scalar-Tail Bochner Norm-Fields Constructor Checkpoint

The integration checkout advanced from
`b2d4ac3cafd3a64848877bcd950864371a7b2e73` through accepted proof commit
`cea0abe49a28290d6c37dcb365caa6440688c4b7`. Harness Task
`automatic-scalar-tail-bochner-norm-boundary-constructor` revision 2 was
accepted from Job
`automatic-scalar-tail-bochner-norm-boundary-constructor-r2-a01`; its strict
gate is
`harness/v2/state/jobs/automatic-scalar-tail-bochner-norm-boundary-constructor-r2-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no Harness Job or
file lease remains active.

The accepted declaration is
`Poincare.AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`.
It calls the verified positive-time `ofBochnerNormFieldsAndTailOverlap`
constructor, explicitly projects its analytic field at the ambient charted
space, and stores the original tail input and definitionally indexed
compact-history feedback in the scalar-tail record. Its frozen type retains
the reaction, compact tensor, Ricci-norm C2, Ricci second-derivative,
Laplacian-continuity, rough-pairing-continuity, subordinate-geometry,
tail-overlap, and compact-history inputs, while adding neither `hPairDiff` nor
joint covariant-Ricci or scalar-time-derivative continuity as replacement
arguments. The canonical exact-type probe passed and `#print axioms` reported
only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job
`automatic-scalar-tail-bochner-norm-boundary-constructor-r1-a01` is preserved
as interrupted evidence: it exhausted its 5,000-token output budget before
making a tool call and left an empty patch. Revision 2 froze the independently
checked 7,904-byte patch and completed exactly one scoped patch, one focused
Lean check, and one patch diff in a fresh supervised Pi session.

The frozen Task gate, targeted module build, root olean build, root
elaboration, interface, semantic-surface, theorem-contract, and axiom audits
passed. The root-import audit retains exactly its three established direct-
import gaps: the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe still reports `EXACT_DECLARATION_PROBE=absent`.

The next theorem-shaped dependency reduction is to prove, in
`NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean`,
the pointwise `CovTensor2DerivExtDifferentiableAt` premise for
`ricciVariationField (reaction.metric k)` from the reaction package's
`normalizedFlow`, `jointMetricEntries`, and `realizesFlow` fields, using
`ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow` and
`covTensor2DerivExtDifferentiableAt_of_extSecond`. Freeze that lemma as one
single-file Task before propagating it into a constructor without an explicit
`hRicSecond` argument. Before claiming a Job at the final clean HEAD, record,
publish, and independently verify the immutable Lake cache for that exact
base.

## 2026-07-21 Normalized-Flow-Slice Ricci Regularity Checkpoint

The integration checkout advanced from
`82c77b324b73ee7a196f4fba4fb35880bb73dc63` to accepted proof commit
`0a5915fb3c4bbb5e3b513a6911e9aed6e92af23b`. Harness Task
`reaction-flow-slice-ricci-second-regularity` revision 4 was accepted from Job
`reaction-flow-slice-ricci-second-regularity-r4-a01`; its strict gate is
`harness/v2/state/jobs/reaction-flow-slice-ricci-second-regularity-r4-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no queued,
preparing, running, or reviewing Job remains.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.ricciVariationField_covTensor2DerivExtDifferentiableAt`.
For every nonnegative time and point, it derives second differentiability of
`ricciVariationField (reaction.gt t)` from `reaction.normalizedFlow` and
`reaction.jointMetricEntries`. The proof first obtains C2 extended Ricci
entries with
`ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow`, then uses
`covTensor2DerivExtDifferentiableAt_of_extSecond` and the canonical Ricci
tensor-linearity lemmas. The exact frozen-type probe passed and `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `reaction-flow-slice-ricci-second-regularity-r1-a01` is
preserved as interrupted evidence after it exhausted its budget on broker-
rejected context requests. Revision 2 is rejected evidence for the exact
missing `[SimplyConnectedSpace M]` source binder. Revision 3 produced the
green proof but is rejected because it exceeded its immutable three-call
contract after an initial patch rejection. Revision 4 froze those final patch
bytes and completed exactly one scoped patch, one focused Lean check, and one
patch diff in a fresh supervised Pi session.

The frozen Task gate, isolated and integrated root builds, root elaboration,
interface, semantic-surface, theorem-contract, and axiom audits passed. The
root-import audit reproduced exactly its three established direct-import gaps:
the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe at the integrated commit still reports
`EXACT_DECLARATION_PROBE=absent`.

This checkpoint deliberately does not claim the stronger all-parameter result
for `reaction.metric k`. The record field `realizesFlow` states only
`reaction.metric (reaction.parameter t) = reaction.gt t`; no field makes
`reaction.parameter` surjective onto every `k : reaction.K`. Consequently the
previously proposed direct all-`k` lift is not justified by the reaction
package. The next theorem-shaped action is to isolate intrinsic Ricci C2
regularity for an arbitrary `ClosedSmoothRiemannianMetric` (starting with
`CovTensor2ExtContMDiffAt (ricciVariationField g) x 2`, using the existing
coordinate Ricci C2 lemmas), and then feed that result through
`covTensor2DerivExtDifferentiableAt_of_extSecond`. Freeze that one interface at
the final clean HEAD only after recording, publishing, and independently
verifying its exact-base immutable Lake cache.

## 2026-07-21 Chart Levi-Civita C3 Regularity Checkpoint

The integration checkout advanced from
`39054bc8268b9e4734c03ede4ccb0fe2ad8e7c2f` through the accepted proof
integration recorded by this commit. Harness Task
`chart-levicivita-section-c3-regularity` revision 4 was accepted from Job
`chart-levicivita-section-c3-regularity-r4-a01`; its reviewed worker commit is
`6e7eb9208248a2ffba8b11a71e8b566ee096fe9e` and its strict gate is
`harness/v2/state/jobs/chart-levicivita-section-c3-regularity-r4-a01/gate.json`
on `mj-zima`. The Job is passed and its lease is released.

The accepted declaration is
`CovariantDerivative.chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₃`.
It raises the existing chart-transported Levi-Civita section result from C2 to
C3 for a C4 metric and C4 transported section. The proof globalizes the local
section with a smooth bump, invokes the chart Levi-Civita C3 connection
regularity theorem, and transfers the resulting germ back to the original
section. The canonical exact-type probe passed and `#print axioms` reported
only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 and revision-2 Jobs are preserved as interrupted evidence after
bounded sessions exhausted their output without a patch. Revision 3 was
interrupted before a known-unsafe zero-context patch could be broker-relocated.
Revision 4 froze the deletion-anchored patch, completed exactly one scoped
patch, one focused Lean check, and one patch diff, and then passed Codex's four
frozen acceptance commands. An independent exact-commit root build completed
all 4,068 jobs successfully before acceptance.

The local C3 interface is now resolved. Harness Task
`local-covariant-section-c3-regularity` revision 5 was accepted from Job
`local-covariant-section-c3-regularity-r5-a01`; its reviewed proof commit is
`1204566315a24f521536244b58d925f917585477`, its strict gate is
`harness/v2/state/jobs/local-covariant-section-c3-regularity-r5-a01/gate.json`,
and its lease is released. The accepted declaration is
`CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_three`. Its
canonical exact-type probe passed, and `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound`. The serial root build completed all 4,068
jobs. Root elaboration plus the interface, semantic-surface, and theorem-
contract audits passed; the theorem-contract audit first exposed and then
verified the required equality companion
`contMDiffAt_cov_section_of_contMDiffAt_three_eq`.

### 2026-07-22 closed Levi-Civita C3 frontier

Main now integrates
`Poincare.LeviCivitaExistence.closedLeviCivitaConnection_contMDiff₃` with
type `CovariantDerivative.ContMDiffCovariantDerivative
  (LeviCivitaExistence.closedLeviCivitaConnection g) 3`. The proof lowers the
metric's C4 regularity to the C3 chart input, applies
`chartTransportedLeviCivitaHom_contMDiffAt₃`, explicitly lowers the resulting
section regularity to C2, and supplies that C2 fact to the closed-chart germ
bridge. The exact `Poincare.poincare_conjecture` declaration remains absent.

Harness Task `closed-levicivita-connection-c3-regularity` revision 5 was
accepted through Job `closed-levicivita-connection-c3-regularity-r5-a01`.
That fresh bounded Pi session used one scoped patch, one successful Lean check,
and one diff read. Codex independently inspected the 107-line theorem proof,
committed it in the Job worktree as
`199f4173969951444c06cfc2a62f3273c3c7f715`, and passed the complete frozen
four-command focused review plus the exact canonical declaration probe before
accepting the Task. The integration checkpoint passed root elaboration at this
theorem source tree. Revision-3 Job `r3-a02` and
revision-4 Job `r4-a01` remain preserved as interrupted evidence; no Job or
file lease remains active.

The next theorem-shaped objective is arbitrary closed-metric Ricci C2
regularity,
`CovTensor2ExtContMDiffAt (ricciVariationField g) x 2`, using the new C3
closed Levi-Civita instance and the existing canonical first-regularity route
in `Poincare/Global/ScalarVariation.lean`. The first action in the next cycle
is to record, publish, and verify the immutable Lake cache for this final base,
then freeze the exact declaration name, source scope, imports, and focused gate
for that objective before dispatch. Do not reuse any interrupted worktree.

## 2026-08-31 Canonical Ricci C2 and Bochner Boundary Checkpoint

The integration branch `codex/formalization-until-6` advances clean base
`bc076f1e893c6ba834729f8bcb359a1f400a3e72` through seven reviewed commits:

- `1d44e245` proves
  `covTensor2ExtContMDiffAt_ricciVariationField_canonical`. The proof uses the
  C3 closed Levi-Civita connection and C2 Lie-bracket regularity to construct
  C2 curvature fields, pairs them with the metric, traces the auxiliary
  curvature tensor, and identifies the result with the Ricci tensor.
- `b1717bc3` packages fixed-time global C2 scalar-curvature regularity from a
  normalized Ricci flow with joint C3 metric entries.
- `81f97fc4` proves
  `covTensor2DerivExtDifferentiableAt_ricciVariationField_canonical`, deriving
  the former `hRicSecond` field from canonical Ricci C2 regularity.
- `074fc72d` adds
  `continuous_joint_covRicciNormSqAt_of_bochner_norm_fields_canonical` and
  `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerNormFieldsCanonical`.
  Both omit `hRicSecond`; the older APIs remain unchanged.
- `970026cb` lifts the same reduction into
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.
- `7b5a8b6a` carries the premise removal through
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.
- `6465a615` completes the same reduction through
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.

Focused elaboration passed for every changed Lean module. Exact declaration
probes reported only `propext`, `Classical.choice`, and `Quot.sound`. The
dependency refresh completed 3,755 jobs, root `Poincare.lean` elaboration
passed, and the interface, semantic-surface, and theorem-contract audits
passed. The axiom audit passed. The root-import audit retains exactly its
three pre-existing direct-import gaps:
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
and `NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The
project is still incomplete; an exact probe reports unknown identifier for
the reserved `Poincare.poincare_conjecture` endpoint.

The next exact theorem-shaped action is to prove
`ricciNormSqAt_contMDiffAt_two_canonical (g) (x)` in
`Poincare/Global/MetricFlowJointPinchingEvolution.lean`, using
`contMDiffAt_two_ricciNormSqAt_of_ricci_entries` and the new canonical Ricci C2
theorem. Then remove `hRicNorm₂` from new canonical Bochner constructors in
the same staged order. Do not replace or weaken the older constructors.

## 2026-09-03 Covariant-Ricci Joint Continuity Checkpoint

The isolated integration branch `codex/formalization-until-6` continued from
the unchanged `origin/main` base `bc076f1e`. The committed tree reached
`0a9d3aeb` before the next bounded proof attempt.

The first group of commits completed the canonical Bochner cleanup described
above. `bb3491ef` proves canonical C2 regularity of `ricciNormSqAt`.
`c0571e50`, `e0ee52d9`, `25ebbf90`, and `d1138972` remove the explicit
`hRicNorm₂` premise from new canonical analytic, primitive, positive-time, and
tail constructors while preserving every older API. `a7d770ff` packages the
Ricci curvature commutation theorem canonically, and `0defb8f0` removes the
duplicated commutation proofs from both flow-evolution modules.

The next group proves genuine real-time continuity of the intrinsic squared
covariant-Ricci derivative norm:

- `40b035fa` proves continuity of spatial Frechet derivatives of jointly C1
  maps, and `035a28cb` specializes it to coordinate Ricci entries.
- `9d3471e2` identifies `covRicciNormSqAt` with its full contraction in any
  tangent basis and the metric-raised dual basis.
- `85dd2462` and `cc8fd116` construct the coordinate covariant-Ricci entries
  and their six-index norm contraction.
- `bf6def94` proves that anchored tangent-field extensions remain smooth on
  the chart source.
- `ef448e97` identifies each coordinate covariant-Ricci entry with
  `covTensor2DerivAt` in the cutoff-one chart zone.
- `b98f65b2` identifies the six-index coordinate contraction with
  `covRicciNormSqAt`, transfers continuity back to `ℝ × M`, and proves
  `continuous_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three`.
  `4ab619b0` exposes this chain through direct root imports.

`9acc98c7` applies the real-time theorem on every compact interval and proves
`exists_uniformCovariantRicciDerivativeNormBound_on_compact_slab_of_metricEntriesJointContDiffAt_three`.
This is a finite-slab bound. It does not claim one constant on the noncompact
forward ray.

The compact-family boundary is now explicit instead of hidden inside a final
continuity premise:

- `a0b698a7` introduces `MetricFamilyCovRicciChartContinuousAt` and proves
  that inverse-metric coefficient continuity plus coordinate
  covariant-Ricci entry continuity on `K × E` gives the intrinsic continuity
  on `K × M` used by compactness.
- `e6d873a9` adds the analytic-data constructor
  `ofCovRicciChartContinuous`.
- `838690b1` derives the coordinate covariant-Ricci entries from inverse
  coefficients, Christoffel values, Ricci entries, and their spatial
  derivative.
- `08d06874` proves a separate quotient route: if nonnegative real time is a
  quotient parameterization of the whole family and realizes every metric,
  the real-time continuity theorem descends to `K × M`. `70dbfe04` exposes
  that route through `ofQuotientRealization`. Quotient surjectivity remains an
  explicit extra premise because the current reaction record does not supply
  it.
- `1befc74b`, `2e8d7110`, and `0a9d3aeb` lower the chart route further.
  Continuity of the blended metric gives inverse coefficients; its first
  spatial derivative gives Christoffel continuity; and the Christoffel first
  jet gives coordinate Ricci-entry continuity by the curvature formula and
  finite trace.
- `895ae4e2` differentiates the curvature formula and finite Ricci trace,
  deriving the Ricci spatial derivative from the first two Christoffel jets.
  `4d630fd7` reconstructs the full Christoffel value from the blended-metric
  first jet. `e259654f` derives the first Christoffel jet from directional
  metric jets through order two.
- `73a77f87` proves the inverse-raise and Koszul product rules needed to
  differentiate the Christoffel variation once more. It derives the second
  Christoffel jet from directional metric jets through order three and then
  constructs the full Ricci chart jet without independent Christoffel or
  Ricci regularity premises.
- `61c70659` packages that input as
  `MetricFamilyBlendedMetricThirdJetContinuousAt`, the exact `C^{0,3}`
  spatial contract over an arbitrary topological parameter space. It proves
  local and global intrinsic covariant-Ricci norm continuity. `0885296a`
  exposes this route through the analytic-data constructor
  `ofMetricFamilyThirdJets`.
- `81aaf1b3` lowers the operator-valued package to
  `MetricFamilyBlendedMetricEntryThirdJetContinuousAt`, whose fields are all
  real-valued fixed coordinate components. Finite-dimensional reconstruction
  recovers the operator jets and the same intrinsic continuity theorem.
- `dd3a1a44` and `dc17d909` add direct root imports for the compact-family
  modules. `dc3af356` and `c32177c8` expose both third-jet packages.

Focused Lean checks, targeted Lake builds, forbidden-term scans, diff checks,
and exact axiom probes passed for every accepted source commit. The new
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. At
`4ab619b0`, root elaboration, the interface audit, semantic-surface audit,
6,008 theorem-contract checks, and the axiom audit passed. The root-import
audit retained exactly the three earlier wiring gaps named in the previous
checkpoint. A later 3,755-job targeted dependency repair and the subsequent
3,282 to 3,285-job module builds also passed. The known nonfatal
`LibrarySuggestions` timeout appeared during one cache build; that build
still exited successfully.

The final paused proof head is `c32177c8`. A serialized full `lake build`
completed all 4,077 targets. Root `Poincare.lean` elaboration, the interface
audit, semantic-surface audit, all 6,008 theorem-contract checks, and the axiom
audit passed. The root-import audit sees every new metric-family module and
retains exactly the same three pre-existing gaps:
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
and `NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The
exact final probe still reports unknown identifier
`Poincare.poincare_conjecture`; this checkpoint does not claim project
completion.

Real-time C3 regularity alone cannot prove continuity on an arbitrary compact
family. The current reaction record constrains `metric` only along
`parameter : Ici 0 → K`, and it supplies neither quotient surjectivity nor
parameter-side spatial-jet continuity. The formalization now names the latter
requirement down to scalar chart components, but no current compactification
constructor proves it for `reaction.metric`. The next theorem-shaped action is
to connect the concrete compact metric-family construction to
`MetricFamilyBlendedMetricEntryThirdJetContinuousAt`, or to strengthen that
construction with the exact componentwise `C^{0,3}` data. Do not infer this
record from compactness or from regularity of `gt` only.

## 2026-09-03 Explicit C0,3 Orbit Compactness Checkpoint

The isolated integration branch `codex/formalization-until-6` advanced from
the preceding compact-family checkpoint through proof-bearing source head
`c5179232`. The original `main` checkout was not modified.

This checkpoint replaces the previously opaque metric-topology boundary by an
explicit scalar compact-open C0,3 topology and carries that topology through
the normalized-flow positive-Einstein endpoint:

- `e6b5431f` and `9fcd8a06` connect stored joint C3 metric entries to the
  scalar third-jet covariant-Ricci constructor.
- `224e039d`, `3518a7e3`, `17faa895`, and `469e738a` define and expose the
  compact-open scalar third-jet topology, prove joint intrinsic
  `covRicciNormSqAt` continuity on an orbit closure, and turn compactness of a
  nonempty orbit closure into a uniform full covariant-Ricci derivative bound.
- `ff5723b4` and `91c95958` feed that bound directly into the reaction-decay
  positive-Einstein package and restrict the required orbit to the honest
  forward family indexed by `Ici 0`.
- `42f6d185` proves that the value slots recover the metric, so
  `metricEntryThirdJetProfile` is injective and an embedding. It also proves
  that a continuous realization from a compact parameter space has compact
  orbit closure; continuity of the indexing map is unnecessary.
- `754c4a78` exposes compact-realization and full scalar-profile joint-
  continuity constructors at the positive-Einstein boundary.
- `ae0e2cfe`, `9b9599b1`, and `0d92c260` apply componentwise
  Arzela--Ascoli and Tychonoff in the profile target, characterize metric-orbit
  compactness by the realized part of the profile closure, and derive the
  uniform covariant-Ricci bound once every profile limit is realized by an
  actual metric.
- `58f241e9` imports the new compactness modules at the root. `c5179232`
  supplies compact-containment and pointwise-bounded Ascoli constructors that
  reach the established positive-Einstein analytic data for the forward flow.

No global topology or T2 instance was installed on the metric type. The
topology remains local to each theorem. Exact declaration and axiom probes for
the new chain report only `propext`, `Classical.choice`, and `Quot.sound`. The
missing Mathlib Ascoli object was repaired with a targeted 927-job build.

At `c5179232`, a serialized full `lake build` completed all 4,082 targets.
Root `Poincare.lean` elaboration, the interface audit, semantic-surface audit,
all 6,008 theorem-contract checks, and the axiom audit passed. The root-import
audit still fails on exactly the same three pre-existing direct-import gaps:

```text
Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction
Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
Poincare.Global.NormalizedFlowHausdorffScalarVariationJointContinuityReduction
```

An exact `import Poincare` probe still reports
`Unknown identifier Poincare.poincare_conjecture`; this checkpoint does not
claim completion.

The remaining compactness obligation is now precise. Componentwise
equicontinuity and pointwise bounds make the ambient C0,3 profile closure
compact, but they do not prove that a limit profile is a smooth positive-
definite metric. The forward endpoint therefore retains
`hForwardProfileLimitsRealized`. This premise cannot be inferred from the
embedding alone: finite C0,3 limits can lose smoothness, and positive
definiteness can degenerate without a uniform lower bound. The alternative
compact-parameter route retains the equally explicit requirement that
`reaction.metric` be continuous in the full profile topology; the reaction
record's local real-time C3 field does not imply continuity of its arbitrary
extension over `reaction.K`.

The exact first action for the next proof cycle is to freeze one theorem with
conclusion

```text
closure (Set.range (metricEntryThirdJetProfile ∘ forward)) ⊆
  Set.range metricEntryThirdJetProfile
```

for `forward t = reaction.gt t.1`, and prove it from explicit uniform higher-
regularity and two-sided metric nondegeneracy hypotheses. If the repository
does not yet supply those estimates, stop with their exact Lean types rather
than weakening or assuming the realized-limit conclusion.

## Executable Harness Boundary

The primary path is:

```text
Codex GPT on mj-zima
  -> Harness v2 Task/Job SQLite, leases, artifacts, worktrees, and gates
  -> one fresh bounded Pi JSON Job session
  -> Leanstral on the existing private vLLM endpoint
```

Codex is the only frontier selector, worktree allocator, reviewer, gate owner,
Task acceptance authority, and commit authority. Each Job gets a new Pi
process/session. Pi built-ins are disabled, and Leanstral receives exactly:

- `read_context`
- `search_symbol`
- `apply_patch_scoped`
- `lean_check`
- `git_diff`
- `report_blocked`

As of 2026-07-20 the executable worker plane can fill up to four fixed Pi
execution slots from fully prepared queued Jobs with disjoint SQLite file
leases. The supervisor renews each running lease, releases its execution slot
when Pi exits, and routes a sealed successful result to Codex-owned
`reviewing`. Blocked or unsuccessful runs keep immutable evidence; only Codex
may create a fresh attempt. Reviewing Jobs do not consume Leanstral execution
capacity, so independent serial review can overlap another disjoint proof Job.

The 2026-07-21 throughput control update adds a configured execution-backlog
target, defaulting to four and never exceeding the four-session ceiling. The
target counts queued, preparing, and running Jobs; reviewing Jobs do not hide
unused inference capacity. Codex must replenish a safe disjoint same-base batch
before optional repository-wide audits or record the concrete lease, cache,
dependency, resource, or theorem-shape reason for underfill. Compatible
accepted Jobs still pass independent frozen gates and one serial Codex merge
queue, while broad root audits may run once per compatible integration batch.
Cycle results, `status.sh`, and the three-hour heartbeat expose the target and
underfill. This policy does not authorize overlapping leases, duplicate or
filler Tasks, extra Leanstral tools, or any worker acceptance/commit authority.

There is no worker access to an unrestricted shell, SSH, arbitrary filesystem
or network tools, Git mutation, worktree deletion, Docker, Ray, tmux, or model
service management. `harness/v2/worker/` is fallback-only: keep its endpoint
health check, deterministic prompt snapshot, and explicit one-shot inference
path, but do not extend it into another agent loop.

The control plane stores validated Task/Job transitions and fenced leases in
SQLite and keeps prompts, Pi JSON events, tool results, diffs, compiler output,
blocked reports, gates, and reviews append-only under ignored Job artifacts. A
passed Job never accepts its Task; Codex must inspect the diff and independently
rerun the frozen gate first.

## Verified Live Deployment Facts

Checks and the bounded release exercise on 2026-07-20 established:

- The integration checkout is `/srv/projects/poincare`; the committed control
  checkout is `/srv/data/poincare-harness/control`; Job worktrees are beneath
  `/srv/projects/poincare-worktrees`.
- The project toolchain reports Lean `4.30.0-rc2` on `mj-zima`.
- Production Pi is the fresh sealed installation
  `/srv/data/poincare-harness/pi-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`,
  with owner-only attestations under
  `/srv/data/poincare-harness/pi-attestation-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`.
  The legacy unsealed `/srv/data/poincare-harness/pi` tree was not mutated or
  reused.
- Fresh runtime state is
  `/srv/projects/poincare/harness/v2/state/harness.sqlite3`; no Mac SQLite,
  WAL, staging directory, or prior Mac Job artifact was transferred.
- The existing private vLLM API is healthy, serves model ID `leanstral-1.5`,
  and reports a 200,000-token model limit.
- The model artifact is `mistralai/Leanstral-1.5-119B-A6B`, revision
  `81592da95d94ab0439bfce16df1d55b402e598b6`.
- The exact-base root bootstrap completed successfully: 4,064/4,064 jobs,
  `exit_code=0`, at `2026-07-20T00:39:27Z`. The focused automatic scalar-time
  derivative module then completed 3,382/3,382 jobs, `exit_code=0`, at
  `2026-07-20T00:40:20Z`. No overlapping Lean build or owned bootstrap tmux
  session remained at the subsequent read-only check.
- The bounded accepted Job used a fresh Pi JSON session, exactly the six scoped
  tools, dispatch generation 1 and lease token 1. Its sealed Pi run reported
  success with 8 tool events; Codex's clean accepted tree is
  `0581d0c497d584406dbfd75386214e1ed67426b6`.
- Serial integration verification passed root elaboration plus the interface,
  semantic-surface, theorem-contract, and axiom audits. The portable
  root-import audit then reported five pre-existing direct-import ledger gaps,
  so the root-import and full completion audits correctly remain non-green.

The private endpoint URL belongs only in ignored configuration and Job
evidence. Do not restart or modify the live vLLM/Ray service, inspect or manage
its GPU processes, change model files, or take ownership of the Spark runtime.

The Mac tldraw offline canvas is titled inside the drawing `Poincare Proof
Orchestration`, stable document ID `nPBFgUN4xNLuW1nWbbtkE` (the app currently
lists the unsaved canvas as `Untitled`). It shows the Pi-centered chain, exact
six tools, Codex-only authority, and the exact long-term Harness completion
terminal. The Mac lane records the final setup-thread handoff and future
on-demand inspection; it does not imply that this thread remains alive. The
`mj-zima` observe process produces durable evidence every 10,800 seconds.

## Operator Handoff

The persistent deployment owns exactly `poincare-control`,
`poincare-workers`, and `poincare-observe`. From the Mac, use:

```sh
ssh -i ~/.ssh/id_ed25519_zimaboard_ai_lab -o IdentitiesOnly=yes \
  mj-kang@192.168.30.227 \
  '/srv/data/poincare-harness/control/harness/v2/deploy/status.sh /srv/data/poincare-harness/private/deploy.env'
```

Durable three-hour evidence is under
`/srv/projects/poincare/harness/v2/state/deploy/`, especially
`observe/heartbeats.jsonl` and `observe/snapshots/`. To request a graceful
drain without deleting state:

```sh
/srv/data/poincare-harness/control/harness/v2/deploy/stop.sh \
  /srv/data/poincare-harness/private/deploy.env
```

Restart with the corresponding `launch.sh` command. The SQLite store and Job
artifacts, not tmux scrollback, are recovery state. This Mac setup thread ends
after its one deployment report; it does not remain alive for the three-hour
loop. The long-term Harness may report proof completion only after the exact
declaration probe, allowed-axiom check, clean stable HEAD, and full completion
audit all pass.

Known non-blocking release follow-ups are bounded: Pi 0.80.10 emits harmless
read-only global-settings lock warnings in the sealed namespace, and its
cumulative JSON message updates made this successful 7,116-token Job's event
files large. Both are retained as evidence and remain within the Job disk
budget; neither expands Leanstral's authority or blocks restart/recovery. The
root-import ledger still needs direct `Poincare.lean` imports for the two
Cartan tail-overlap reductions and the scalar-variation continuity reduction.
Their current transitive visibility remains sufficient for exact
`import Poincare` type probes; they are separate wiring follow-ups rather than
proof completion.
