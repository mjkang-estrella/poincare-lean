# Handoff Snapshot

Snapshot date: 2026-08-31 (UTC)

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
