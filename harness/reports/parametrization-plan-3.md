# Final chain parametrization plan

Date: 2026-09-08. Base: `92f944c671d72d19f7dee20081f19efbfdd42053`.
Branch: `worker/parametrization-plan-3`. Deliverable: this report only.

The remaining program is nine new files, tasks 11–19 below. It includes a separate uniform patch-switch task, subdivision transport, and terminal transport. These are proposed proof obligations, not statements that the landed H1/H2 theorem already proves global development. Every displayed target was checked as a proposition in Lean 4.30.0-rc2; none was proved in this analysis job.

`git status --short --branch`, `git worktree list --porcelain`, and `git rev-parse HEAD` identified the clean isolated worktree at the base above. I read `README.md`, the relevant current and historical `HANDOFF.md` sections, `docs/PROJECT_MAP.md`, [the inventory](chain-parametrization-inventory.md), [plan 2](parametrization-plan-2.md), and the requested landed modules and their imports. The task-specific report-only contract takes precedence over the general handoff-update and branch-naming instructions. No Lean source, `Poincare.lean`, or `HANDOFF.md` is changed.

## Verified source index

All identifiers below were checked with source searches or the successful declaration probe. Paths are relative to this report; namespace names are included where the filename is not the namespace. The task discussions cite these entries.

| ID | Verified file and declarations | Relevant boundary |
| --- | --- | --- |
| S1 | [CartanSuppliedDifferentialSuccessor.lean](../../Poincare/Global/CartanSuppliedDifferentialSuccessor.lean): `Interpretation`, `patch`, `Data`, `Data.successor`, `anchor_laws` in `CartanSuppliedDifferentialSuccessor` | The geometric state has no patch label. Supplied data retains its source, host coordinates, derivative and actual alignment. |
| S2 | [CartanSuppliedDifferentialTransfer.lean](../../Poincare/Global/CartanSuppliedDifferentialTransfer.lean): `successor_eq_of_eqOn_open`, `successor_eq`, `patch_germ_eventuallyEq_generic`, `patch_successor_at_anchor`, `local_equality_transfer` | Cross-policy successor equality needs open agreement at the evaluated successor point. Patch/generic comparison is at the anchor. |
| S3 | [FixedChartLocalSuccessorExistence.lean](../../Poincare/Global/FixedChartLocalSuccessorExistence.lean): `OnCompact`, `exists_uniform_normal_radius`, `exists_uniform_linear_bound`; [FixedChartMovingPositionJacobi.lean](../../Poincare/Global/FixedChartMovingPositionJacobi.lean): `movingInitialPositionJacobiComparison`, `exists_radius` | H1 is uniform over compact source/target anchors and every alignment. The unconditional `exists_radius` is in the latter namespace/file. |
| S4 | [FixedChartLocalSuccessorEquality.lean](../../Poincare/Global/FixedChartLocalSuccessorEquality.lean): `OnCompact`, `exists_uniform_domain_radius_into_open`; [FixedChartMappedGeodesicAssembly.lean](../../Poincare/Global/FixedChartMappedGeodesicAssembly.lean): `FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature`, `FixedChartLocalSuccessorEquality.exists_radii` | Import the assembly to obtain unconditional H1/H2. Both radii precede all anchors, alignments and data. H2 contains both full-ball source inclusion and equality. |
| S5 | [CartanSuppliedReachableChain.lean](../../Poincare/Global/CartanSuppliedReachableChain.lean): `ReachableChain`, `StepAvailable`, `exists_reachableChain`, `state_anchor_eq_node`, `state_eq`, `state_eq_of_open_agreement` | Recursion is supplied; mesh, policy construction, refinement and homotopy invariance are not. |
| S6 | [FixedChartUniformSourceNormal.lean](../../Poincare/Global/FixedChartUniformSourceNormal.lean): `Patch`, `exists_patch`, `Patch.anchors`, `Patch.isOpen_anchors`, `Patch.center_mem_anchors`; [IsometryInstantiate.lean](../../Poincare/Global/IsometryInstantiate.lean): `cutoffOneLocus_mem_nhds_anchor` | A patch contains its center in an open anchor set. There is no assertion that it covers its whole host chart. |
| S7 | [ControlledChartInstance.lean](../../Poincare/Global/ControlledChartInstance.lean): `exists_finite_uniform_chart_cover`, `chartedSpaceOfCover`, `exists_controlled_chartedSpace`; [ConnectionInstanceNaturality.lean](../../Poincare/Global/ConnectionInstanceNaturality.lean): `exists_controlled_recognition_reduction'` | Finite preferred atlas and uniform chart-source balls, with recognition transport. No normal-patch cover or cutoff lower bound is supplied. |
| S8 | [CartanCanonicalRootedDirectGenericNeighborhoodRecognition.lean](../../Poincare/Global/CartanCanonicalRootedDirectGenericNeighborhoodRecognition.lean): `exists_genericRootedRealization_with_wholeCellMesh_of_certificate`, `restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry` | Reusable strictification and gluing templates; their chain and certificate inputs are legacy generic types. |
| S9 | [CartanAtlasRootedPathSkeleton.lean](../../Poincare/Global/CartanAtlasRootedPathSkeleton.lean): `RootedCartanPathSkeleton`, `rootedCartanPathSkeletonAt`, `nonempty_rootedCartanPathSkeleton`, `RootedPathChainRealization` | Reuse the skeleton itself. Replace the realization, whose chain field is specialized to legacy data. |
| S10 | [DifferentialSuccessorAdjacentContinuation.lean](../../Poincare/Global/DifferentialSuccessorAdjacentContinuation.lean): `reachableChains_ladder_invariant`, `reachableChains_endpoint_eq`, `exists_homotopy_metricBall_grid`, `homotopyGridRow`, `differentialHomotopyGrid_chain_endpoint_eq_of_metricBall_patches` | The grid compactness theorem is reusable directly. The ladder must be ported to supplied data and interpretation switches. |
| S11 | [DifferentialSuccessorFiniteSubdivisionRefinement.lean](../../Poincare/Global/DifferentialSuccessorFiniteSubdivisionRefinement.lean): `finiteSortedSequence`, `exists_common_monotone_refinement_strict_factor`, `exists_common_refinement_subordinate_to_open_cover_prod_strict_factor`; [CartanAtlasRootedPathAdaptiveMeshRealization.lean](../../Poincare/Global/CartanAtlasRootedPathAdaptiveMeshRealization.lean): `exists_monotone_subdivision_subordinate_to_pointwise_path_balls`; [CartanCanonicalFamilyComparedWholeCellRealization.lean](../../Poincare/Global/CartanCanonicalFamilyComparedWholeCellRealization.lean): `finiteSortedSequence_strict_until_card_of_one_mem_zero_not_mem`, `finiteSortedSequence_eventually_one_from_card_of_one_mem_zero_not_mem` | Parameter geometry does not depend on the Cartan interpretation. |
| S12 | [CartanRestrictedOverlapCompatibility.lean](../../Poincare/Global/CartanRestrictedOverlapCompatibility.lean): `UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3`, its `diagonalDevelopment_eqOn_domain`, `isLocalHomeomorph_diagonalDevelopment`, and `globalLocalDevelopment_of_restrictedCompatibleCartanAtlas` | The structure uses generic `CartanMap.openPartialHomeomorph`; its restriction/gluing proof is topological. |
| S13 | [UnitRecognitionNext.lean](../../Poincare/Global/UnitRecognitionNext.lean): `UnitCurvatureGlobalLocalDevelopment3`, `unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment`; [RoundSphereSimpleConnected.lean](../../Poincare/Global/RoundSphereSimpleConnected.lean): `roundSphere3_simplyConnectedSpace`, `unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment`; [CoveringSkeleton.lean](../../Poincare/Global/CoveringSkeleton.lean): `GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph`, `homeomorphOfIsCoveringMapSimplyConnected` | The target accepts any total local homeomorphism. Compact covering and sphere simple connectivity are already supplied. |
| S14 | [CartanTwoNeighborhoodDevelopment.lean](../../Poincare/Global/CartanTwoNeighborhoodDevelopment.lean): `restrictedCompatibleCartanAtlas_of_two_neighborhoods`, `globalLocalDevelopment_of_two_neighborhoods`, `UniversalUnitConstantCurvatureSphereRecognitionStatement`; [SphereTheorem.lean](../../Poincare/Global/SphereTheorem.lean): `UnitConstantCurvatureSphereRecognition3`, `poincareConjecture_of_hamiltonConvergence_of_unitRecognition` | Reuse the unchanged recognition statement and final Hamilton consumer. Do not instantiate the old generic neighborhoods with supplied H1/H2. |
| S15 | [CartanSuppliedSourceGermTransfer.lean](../../Poincare/Global/CartanSuppliedSourceGermTransfer.lean): `germ_eventuallyEq_of_normal_eventuallyEq`, `normal_symm_eventuallyEq_of_normal_eventuallyEq`, `exists_open_common_source_agreement`; [FixedChartUniformPreferredGermAgreement.lean](../../Poincare/Global/FixedChartUniformPreferredGermAgreement.lean): `normalized_endpoint_eventuallyEq_expAt`, `normal_eventuallyEq_generic_in_anchor_frame` | Forward and inverse comparison uses actual source memberships and the anchor frame. No equality of selected source sets or uniform comparison radius follows. |
| S16 | [CartanTerminalShortPathScheduleFree.lean](../../Poincare/Global/CartanTerminalShortPathScheduleFree.lean): `scheduleFreeTerminalDistanceRadius`, `scheduleFreeTerminalDistanceRadius_pos`, `terminalShortPathCertificate_of_dist_lt_scheduleFreeTerminalDistanceRadius`; [CartanCanonicalRootedEndpointAssembly.lean](../../Poincare/Global/CartanCanonicalRootedEndpointAssembly.lean): `TerminalShortPathCertificate` | A possible source of terminal paths. Its path-length bound is independent of the new supplied-chain interpretation; its legacy transport consumer is not. |
| S17 | [Mathlib FundamentalGroupoid/SimplyConnected.lean](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean): `SimplyConnectedSpace.paths_homotopic`; [RiemannianContext.lean](../../Poincare/Global/RiemannianContext.lean): `ClosedSmoothRiemannianMetric.toMetricSpace` | Source simple connectivity produces relative-endpoint path homotopy. The metric supplies the same topology used by the manifold. |

## Two necessary qualifications

“One patch per chart” is not a consequence of S6 or S7. Starting with one arbitrarily chosen patch at a representative of each member of a finite atlas need not cover the other points of those charts. The executable contract below instead constructs a finite refinement: choose a patch centered at every point, then a finite subcover of smaller open anchor neighborhoods. On the controlled source, every host `chartAt E (center i)` still belongs to the given finite atlas, but a host chart may be used by several patches. On the sphere, use the existing sphere instance and take a finite patch subcover in the same way. If exactly one patch per original chart is a frozen requirement, stop at that coverage gap; do not assert `ball_cover` from S7. This qualification follows from the exact `exists_patch` and `Patch.anchors` types in S6.

Likewise, H1/H2 is uniform on compact anchor sets, not on their whole surrounding open patch. Use an operating core `core i` and a larger compact buffer with `core i ⊆ interior (buffer i) ⊆ buffer i ⊆ anchors`. The policy retains a label while both current anchors remain in its operating cores; when either leaves, it switches. This is the precise quantitative meaning of re-anchoring within a patch until leaving its operating anchor set. Waiting until the boundary of the full open `Patch.anchors` would have no uniform H1 justification. S3/S4 also only retain the target in an open set unless the stronger `exists_uniform_domain_radius_into_open` clause is used.

A policy of type `ℕ → ChainState → Interpretation` cannot read a previous label from `ChainState`. Task 13 gives it an external preferred-label schedule, constructed together with one chain by recursion. For off-history states it has a covering fallback, so `StepAvailable` still holds for every state anchored at the node, as S5 requires. No patch label is added to geometric state equality.

## Shared dispatch contract

Task 11 starts at the base above. For task `n > 11`, freeze a new exact commit containing its accepted prerequisites before dispatch; this report does not invent future hashes. Each task owns only its named new file. All existing Lean files, `Poincare.lean`, other tasks' files, audit wiring and source definitions are forbidden. Dependencies are `11 → 12 → 13 → 14 → 15 → 16`, with `17` using 13–15, `18` using 16–17, and `19` using 11–18 plus S7/S13/S14. A serial 11–19 dispatch is valid.

Each section specifies imports, proof templates, new work, and its stop condition. The common gate below means the exact command printed in that section plus a no-match prohibited-token scan and `git diff --check`. Require exit 0 for Lean and the diff check; require no matches, normally exit 1, for the scan. Independently probe every named target at its displayed signature and inspect its axiom closure. Only the standard logical dependencies are acceptable. Build accepted dependencies serially if their oleans are missing. These are worker gates, not acceptance or merge authority; root build/audits remain the orchestrator's integration checkpoint.

The Lean blocks are the complete proposed definitions and target signatures. A target has no proof body here. The reproducible probe converts each `theorem name : P` into a definition whose body is the proposition `P`; binder-bearing signatures are preserved. `autoImplicit false` prevents a misspelled interface from becoming an invented variable. The broad import envelope is only for the combined scratch probe. Each new implementation file uses the narrower imports listed in its task and the relevant common notation/variables.

```lean
import Poincare.Global.FixedChartMappedGeodesicAssembly
import Poincare.Global.CartanSuppliedReachableChain
import Poincare.Global.CartanTwoNeighborhoodDevelopment
import Poincare.Global.ConnectionInstanceNaturality

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
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain
```

## 11. `Poincare/Global/CartanSuppliedFinitePatchCover.lean`

Namespace: `Poincare.CartanSuppliedFinitePatchCover`.

Imports: `Poincare.Global.FixedChartMappedGeodesicAssembly`, `Poincare.Global.ControlledChartInstance`.

Objective: produce finite nested source and sphere covers and three uniform positive radii before any path, alignment or chain is chosen. `exists_patchCover` is intentionally stronger than a controlled-instance-only statement: its ingredients in S6 require no atlas finiteness assumption. The final adapter still uses the controlled reduction requested in S7.

For each point choose `zone := cutoffOneLocus center`, using S6, and a patch. Choose smaller metric balls whose nested closures lie in the open anchor set; compactness of the metric space makes the closed cores compact. Take a finite subcover of the innermost open sets. Then apply `lebesgue_number_lemma_of_metric` to those sets, exactly as S7.`exists_finite_uniform_chart_cover` does for chart sources. `covers` is the consequence at ball centers, retained to define `pick` without another proof-producing choice. Repeat for `roundSphereMetric3`; there is no new sphere chart instance.

Apply S4.`exists_radii` to every pair of buffers. Take finite minima of these already uniform pair radii. Apply S4.`exists_uniform_domain_radius_into_open` to each pair of operating cores, with the interiors of the buffers as the requested neighborhoods, and take a finite minimum for `retention`. The new work is the nested finite cover and these quantifier-preserving minima. The controlled-chart cover proof is the topological template; S3/S4 supply the geometric estimates. A minimum of per-state generic chosen radii is not part of this task.

```lean
namespace CartanSuppliedFinitePatchCover
structure PatchCover (g : ClosedSmoothRiemannianMetric 3 M) where
  count : ℕ
  center : Fin count → M
  zone : Fin count → Set E
  patch : ∀ i, FixedChartUniformSourceNormal.Patch g (center i) (zone i)
  cutoff : ∀ i, zone i ⊆ IsometryInstantiate.cutoffOneLocus (center i)
  core : Fin count → Set M
  buffer : Fin count → Set M
  openCore : Fin count → Set M
  core_compact : ∀ i, IsCompact (core i)
  buffer_compact : ∀ i, IsCompact (buffer i)
  openCore_open : ∀ i, IsOpen (openCore i)
  openCore_subset : ∀ i, openCore i ⊆ core i
  core_subset : ∀ i, core i ⊆ interior (buffer i)
  buffer_subset : ∀ i, buffer i ⊆ (patch i).anchors
  lebesgue : ℝ
  lebesgue_pos : 0 < lebesgue
  ball_cover : letI : MetricSpace M := g.toMetricSpace
    ∀ x : M, ∃ i, ball x lebesgue ⊆ openCore i
  covers : ∀ x : M, ∃ i, x ∈ core i

def PatchCover.pick (C : PatchCover g) (x : M) : Fin C.count :=
  Classical.choose (C.covers x)

def Controlled (charts : ChartedSpace E M) (d : MetricSpace M) : Prop :=
  charts.atlas.Finite ∧ letI : MetricSpace M := d
    ∃ δ > (0 : ℝ), ∀ x : M, ball x δ ⊆ (charts.chartAt x).source

structure QuantitativeCover (g : ClosedSmoothRiemannianMetric 3 M) where
  source : PatchCover g
  target : PatchCover roundSphereMetric3
  step : ℝ
  evaluation : ℝ
  retention : ℝ
  step_pos : 0 < step
  evaluation_pos : 0 < evaluation
  retention_pos : 0 < retention
  h1 : ∀ i j, FixedChartLocalSuccessorExistence.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j) step
  h2 : ∀ i j, FixedChartLocalSuccessorEquality.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j)
    step evaluation
  retained : letI : MetricSpace M := g.toMetricSpace
    ∀ i j (s : CartanChain.ChainState g),
      s.anchor ∈ source.core i → s.target ∈ target.core j →
      ∀ z : M, dist z s.anchor < retention →
        z ∈ interior (source.buffer i) ∧
        map (patch (source.patch i) (target.patch j)) s z ∈ interior (target.buffer j)

def QuantitativeCover.Label (B : QuantitativeCover g) :=
  Fin B.source.count × Fin B.target.count

def QuantitativeCover.interp (B : QuantitativeCover g) (a : B.Label) : Interpretation g :=
  patch (B.source.patch a.1) (B.target.patch a.2)

def QuantitativeCover.Valid (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.core a.1 ∧ s.target ∈ B.target.core a.2

def QuantitativeCover.Buffered (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.buffer a.1 ∧ s.target ∈ B.target.buffer a.2

theorem exists_patchCover : ∀ g : ClosedSmoothRiemannianMetric 3 M,
  Nonempty (PatchCover g)

theorem exists_quantitativeCover : HasConstantSectionalCurvature3 g 1 →
  Nonempty (QuantitativeCover g)
end CartanSuppliedFinitePatchCover
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedFinitePatchCover.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedFinitePatchCover.lean
git diff --check
```

Exact stop condition: Both existence targets must compile, including `ball_cover`, the finite sphere cover, H1/H2 over buffers, and retention of both successor anchors in buffer interiors. A collection whose cores do not cover, or whose radius depends on the current alignment/chain, is failure. If finite refinement is disallowed, report the exact unsupported one-patch coverage type.

## 12. `Poincare/Global/CartanSuppliedUniformPatchSwitch.lean`

Namespace: `Poincare.CartanSuppliedUniformPatchSwitch`.

Imports: task 11. S2/S15 are already in its import graph.

Objective: close the quantitative comparison between different patch interpretations at the same geometric state, then combine it with H2 at a successor. This is an explicit new geometric obligation. The landed statements do not already provide `SwitchControl`.

`buffered_eventuallyEq` follows by comparing both patch maps to `s.map` using S2.`patch_germ_eventuallyEq_generic`, with membership supplied by the buffers. S15 explains the framed normal and inverse-normal comparisons behind that theorem. Their output is a neighborhood of `s.anchor` for this fixed state; it gives neither a radius uniform over states nor agreement around a different node.

The genuinely new target is `exists_switchControl`. It asks for a positive ball radius common to all finitely many patch pairs and all alignments at common buffer anchors. A prospective proof must compare the two fixed-host flows/normal inverses on common retained domains, control host-to-host frame changes, and obtain uniform comparison on compact intersections. S3.`exists_uniform_linear_bound` supplies a bound in each fixed pair of hosts. S15's ODE/frame proof is a template for local identification, not a theorem of uniform comparison. Taking a minimum of its pointwise neighborhoods is invalid. Neither equality of arbitrary total extensions nor agreement on entire source intersections is requested.

After this target, `transition_eqOn` is a quantitative consequence of S4 H2 and the switch bound. H1's predecessor lies in its operating core. `retained` puts the successor in the old buffers, while validity for the next label puts it in the new buffers. Apply H2 in the old interpretation, then the uniform same-state switch equality at `d.successor`. The displayed `/ 32` reserves more than the factor 4 used by this transition and the later two-edge comparisons. This task must not use task 16's global path independence to prove the switch bound.

```lean
namespace CartanSuppliedUniformPatchSwitch
open CartanSuppliedFinitePatchCover
structure SwitchControl (B : QuantitativeCover g) where
  radius : ℝ
  radius_pos : 0 < radius
  agreement : letI : MetricSpace M := g.toMetricSpace
    ∀ (a b : B.Label) (s : CartanChain.ChainState g),
      B.Buffered a s → B.Buffered b s →
      ball s.anchor radius ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor radius)

structure System (g : ClosedSmoothRiemannianMetric 3 M) where
  cover : QuantitativeCover g
  switch : SwitchControl cover

def System.mesh (S : System g) : ℝ :=
  min S.cover.step (min S.cover.evaluation
    (min S.cover.retention S.switch.radius)) / 32

theorem buffered_eventuallyEq : ∀ (B : QuantitativeCover g)
    (a b : B.Label) (s : CartanChain.ChainState g),
  B.Buffered a s → B.Buffered b s →
  map (B.interp a) s =ᶠ[𝓝 s.anchor] map (B.interp b) s

theorem exists_switchControl : HasConstantSectionalCurvature3 g 1 →
  ∀ B : QuantitativeCover g, Nonempty (SwitchControl B)

theorem mesh_pos : ∀ S : System g, 0 < S.mesh

theorem transition_eqOn : ∀ (S : System g) (a b : S.cover.Label)
    (s : CartanChain.ChainState g) (z : M)
    (d : Data (S.cover.interp a) s z),
  S.cover.Valid a s → S.cover.Valid b d.successor →
  letI : MetricSpace M := g.toMetricSpace
  dist z s.anchor < 4 * S.mesh →
    ball z (4 * S.mesh) ⊆ (germ (S.cover.interp a) s).source ∩
      (germ (S.cover.interp b) d.successor).source ∧
    EqOn (map (S.cover.interp a) s) (map (S.cover.interp b) d.successor)
      (ball z (4 * S.mesh))
end CartanSuppliedUniformPatchSwitch
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
git diff --check
```

Exact stop condition: Prove all four targets with the displayed quantifier order and actual common-source ball. `buffered_eventuallyEq` alone is only a partial result. If uniform comparison cannot be established, record the exact resisting `SwitchControl.agreement` goal and strongest checked local statement; do not turn switch control into an extra hypothesis of final recognition.

## 13. `Poincare/Global/CartanSuppliedPatchPolicy.lean`

Namespace: `Poincare.CartanSuppliedPatchPolicy`.

Imports: task 12, `Poincare.Global.CartanSuppliedReachableChain`.

Objective: define the actual state-dependent policy and realize its sticky version. `fallback` selects the pair of cores containing the current source anchor and current sphere target, using the two `covers` witnesses. `select` keeps the preferred pair if both memberships hold, and otherwise uses that fallback. No continuity of this selection is claimed.

For any externally fixed schedule `a`, `policy B a n s` is exactly `B.interp (select B (a n) s)`. `select_valid` gives both core memberships, hence both buffer memberships. If the next-node distance is below `S.mesh`, it is below `B.step`; apply `B.h1` to the actual `s.alignment`, using `s.anchor = nodes n`. This proves S5.`StepAvailable` for all node-anchored states, including every possible target. H1 does not need to keep the next target in the same operating core, because the next policy call selects again.

For `exists_sticky_chain`, recurse jointly on the reached state and preferred pair. Start with `fallback initial`; choose a datum in the selected interpretation; pass its successor and the selected pair to the next recursion step. The resulting schedule satisfies `Sticky`, and the policy's off-history fallback makes it a total policy with the stated type. This is S5.`exists_reachableChain`'s dependent recursion template with one external recursion component. It is not circular choice of a policy from an already assumed realized chain.

For `chains_eq`, induct on equal prefix states. Task 12 switch control gives predecessor-map equality on the ball at that common anchor. The next node is inside that ball since the mesh is smaller than the switch radius. Restrict to an open neighborhood of the next node and apply S2.`successor_eq_of_eqOn_open`. The resulting open agreements discharge S5.`state_eq_of_open_agreement`; S5.`state_eq` handles witness choice for an identical policy. Its hypotheses do not directly compare different node sequences.

```lean
namespace CartanSuppliedPatchPolicy
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch

def fallback (B : QuantitativeCover g) (s : CartanChain.ChainState g) : B.Label :=
  (B.source.pick s.anchor, B.target.pick s.target)

def select (B : QuantitativeCover g) (preferred : B.Label)
    (s : CartanChain.ChainState g) : B.Label :=
  @ite _ (B.Valid preferred s) (Classical.propDecidable _) preferred (fallback B s)

def policy (B : QuantitativeCover g) (preferred : ℕ → B.Label) :
    ℕ → CartanChain.ChainState g → Interpretation g :=
  fun n s => B.interp (select B (preferred n) s)

def Sticky (B : QuantitativeCover g) (preferred : ℕ → B.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain (policy B preferred) nodes initial) : Prop :=
  ∀ n, preferred (n + 1) = select B (preferred n) (c.state n)

theorem select_valid : ∀ (B : QuantitativeCover g) (a : B.Label)
  (s : CartanChain.ChainState g), B.Valid (select B a s) s

theorem stepAvailable : ∀ (S : System g) (a : ℕ → S.cover.Label) (nodes : ℕ → M),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  StepAvailable (policy S.cover a) nodes

theorem exists_sticky_chain : ∀ (S : System g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g), initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∃ (a : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover a) nodes initial),
    a 0 = fallback S.cover initial ∧ Sticky S.cover a nodes initial c

theorem chains_eq : ∀ (S : System g) (a b : ℕ → S.cover.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g),
  initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∀ (c : ReachableChain (policy S.cover a) nodes initial)
    (d : ReachableChain (policy S.cover b) nodes initial), ∀ n, c.state n = d.state n
end CartanSuppliedPatchPolicy
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedPatchPolicy.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedPatchPolicy.lean
git diff --check
```

Exact stop condition: All four targets compile. Require a schedule with the displayed retention recurrence and a policy valid on off-history states. A recursion requiring membership in a previously selected target core forever, or agreement only at the previous anchor when comparing next-step data, is failure.

## 14. `Poincare/Global/CartanSuppliedWholeCellRealization.lean`

Namespace: `Poincare.CartanSuppliedWholeCellRealization`.

Imports: task 13, `Poincare.Global.CartanAtlasRootedPathSkeleton`, `Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition`.

Objective: choose strict eventually terminal whole-cell subdivisions, then realize supplied chains on them, for every path and for the common rooted skeleton. The whole-cell clause bounds all pairs of points in each parameter cell, not just its endpoint nodes. `Realization` stores the actual schedule and reached-chain data; it allows non-sticky policies so later comparisons cover every valid choice. The existence target additionally returns the sticky property.

Reuse the geometric part of S8.`exists_genericRootedRealization_with_wholeCellMesh_of_certificate`: subordinate to pointwise path balls of half the requested radius, remove duplicate times using the S11 finite-sorted-sequence lemmas, and retain `Monotone`, strictness, and terminal tail. Apply task 13 only after the subdivision is fixed. Reuse S9's `RootedCartanPathSkeleton` without conversion to the old `RootedPathChainRealization`. The new part is the supplied policy/chain fields and the terminal anchor proof from S5.`state_anchor_eq_node`. The infinite tail is legitimate: all tail steps have zero distance and S2.`patch_successor_at_anchor` makes their states constant.

```lean
namespace CartanSuppliedWholeCellRealization
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
structure Subdivision {x y : M} (p : Path x y) (r : ℝ) where
  time : ℕ → unitInterval
  terminal : ℕ
  zero : time 0 = 0
  mono : Monotone time
  strict : ∀ n < terminal, time n < time (n + 1)
  tail : ∀ n ≥ terminal, time n = 1
  wholeCell : letI : MetricSpace M := g.toMetricSpace
    ∀ n (a b : unitInterval), a ∈ Icc (time n) (time (n + 1)) →
      b ∈ Icc (time n) (time (n + 1)) → dist (p a) (p b) < r

structure Realization (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) where
  subdivision : Subdivision (g := g) p S.mesh
  preferred : ℕ → S.cover.Label
  chain : ReachableChain (policy S.cover preferred)
    (fun n => p (subdivision.time n)) initial

def Realization.endpoint {S : System g} {initial : CartanChain.ChainState g}
    {y : M} {p : Path initial.anchor y} (R : Realization S initial p) :
    CartanChain.ChainState g := R.chain.state R.subdivision.terminal

structure RootedRealization (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g) where
  realization : ∀ x : M, Realization S skeleton.root (skeleton.path x)

theorem endpoint_anchor : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p),
  R.endpoint.anchor = y

theorem exists_subdivision : ∀ {x y : M} (p : Path x y) (r : ℝ),
  0 < r → Nonempty (Subdivision (g := g) p r)

theorem exists_realization : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y),
  ∃ R : Realization S initial p,
    Sticky S.cover R.preferred (fun n => p (R.subdivision.time n)) initial R.chain

theorem exists_rootedRealization_with_wholeCellMesh : ∀ (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g),
  Nonempty (RootedRealization S skeleton)
end CartanSuppliedWholeCellRealization
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedWholeCellRealization.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedWholeCellRealization.lean
git diff --check
```

Exact stop condition: All four targets compile. Require positive-mesh whole-cell control, strictness before the terminal index, constant terminal times, actual supplied `Data`, and the endpoint anchor equation. Existence along only the chosen skeleton without the arbitrary-path target, or a mesh selected after seeing chain data, is failure.

## 15. `Poincare/Global/CartanSuppliedSubdivisionTransport.lean`

Namespace: `Poincare.CartanSuppliedSubdivisionTransport`.

Imports: task 14. S11's refinement declarations are available through that import.

Objective: show that inserting sample times inside whole cells, changing finite subdivisions, and changing patch schedules do not change endpoint states on a fixed path.

S11 provides common finite refinements and monotone factor maps. Reuse those parameter results directly. The new proof is the transport of supplied states across each refinement block: compare the original one-step map with the several inserted steps. All points of that block lie in the original whole cell. H1 can supply direct data from its initial state to each intermediate point. Task 12's transition equality and task 13's policy comparison give open agreement near the next inserted node; S2 then identifies the actual differentials/successors. The factor 4 allowance handles the two relevant point distances. This is the insertion/ladder argument behind S10.`reachableChains_ladder_invariant`, adapted to an arbitrary block length. It requires actual open agreement, not value-only endpoint matching.

`refinement_state_eq` explicitly permits repeated factor values and terminal tails; use S2's zero-step law there. `endpoint_eq_same_path` obtains a common refinement from S11 and compares both original realizations to its realized chain. This task uses no simple connectivity.

```lean
namespace CartanSuppliedSubdivisionTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

theorem refinement_state_eq : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p)
    (f : ℕ → ℕ), f 0 = 0 → Monotone f →
  (∀ n, R.subdivision.time n = T.subdivision.time (f n)) →
  ∀ n, R.chain.state n = T.chain.state (f n)

theorem endpoint_eq_same_path : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R T : Realization S initial p),
  R.endpoint = T.endpoint
end CartanSuppliedSubdivisionTransport
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSubdivisionTransport.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedSubdivisionTransport.lean
git diff --check
```

Exact stop condition: Both targets compile for all displayed realizations and monotone factor maps. Equality for just one chosen subdivision, equality of targets without alignments, or a new global path-independence premise is failure. Stop at the exact block-induction/open-agreement type if it resists.

## 16. `Poincare/Global/CartanSuppliedHomotopyEndpoints.lean`

Namespace: `Poincare.CartanSuppliedHomotopyEndpoints`.

Imports: task 15, `Poincare.Global.DifferentialSuccessorAdjacentContinuation`.

Objective: port the metric-ball homotopy ladder to supplied chains and then compare arbitrary path realizations. `GridSmall` gives pairwise diameter control on every closed rectangle, including boundary and eventual constant cells.

Use S10.`exists_homotopy_metricBall_grid` with balls of radius `S.mesh / 2`, covering the image by balls centered at its points; triangle inequality gives `GridSmall`. For the supplied ladder, construct each rung by task 13 H1 with a policy evaluated at the actual lower-row successor state. S4 H2 supplies the bottom and rung evaluation balls. At each re-anchoring, task 12 transfers from the old patch at the successor to the selected patch there. A diagonal pair of successive top cells may require two mesh bounds, which fit inside `4 * S.mesh`. Intersect the open balls around the opposite vertex to compare the actual upper edge and the rung using S2.

The finite ladder proof is S10.`reachableChains_endpoint_eq` and `differentialHomotopyGrid_chain_endpoint_eq_of_metricBall_patches`, replacing legacy data and zero-vector steps with supplied data and S2.`patch_successor_at_anchor`. It must track the interpretations separately. S5.`state_eq_of_open_agreement` compares a rebuilt row policy on the same row nodes after those neighborhoods have been proved; it cannot itself compare different rows or different paths.

To get `endpoint_eq_of_homotopy`, include the finitely many boundary sample times of both input realizations in a common grid refinement, or strictly sort the grid boundary and use task 15 on a common refinement. S11's product-cover refinement theorem is the template. Establish boundary transport and terminal-tail constancy, rather than asserting that the new grid has the old samples. Only `endpoint_eq` uses `SimplyConnectedSpace M`, through S17.`SimplyConnectedSpace.paths_homotopic`. Its `Path.Homotopic` witness is `Nonempty` of the relative-endpoint `Path.Homotopy` type.

```lean
namespace CartanSuppliedHomotopyEndpoints
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

def GridSmall (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q) (t : ℕ → unitInterval) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m n (a b c d : unitInterval),
    a ∈ Icc (t m) (t (m + 1)) → b ∈ Icc (t m) (t (m + 1)) →
    c ∈ Icc (t n) (t (n + 1)) → d ∈ Icc (t n) (t (n + 1)) →
    dist (H (a, c)) (H (b, d)) < S.mesh

theorem exists_grid : ∀ (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q),
  ∃ (t : ℕ → unitInterval) (k : ℕ), t 0 = 0 ∧ Monotone t ∧
    (∀ n ≥ k, t n = 1) ∧ GridSmall S H t

theorem grid_endpoint_eq : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} {p q : Path initial.anchor y} (H : p.Homotopy q)
    (t : ℕ → unitInterval) (k : ℕ),
  t 0 = 0 → Monotone t → (∀ n ≥ k, t n = 1) → GridSmall S H t →
  ∀ (a : ℕ → ℕ → S.cover.Label)
    (c : ∀ m, ReachableChain (policy S.cover (a m))
      (fun n => H (t m, t n)) initial),
    (c 0).state k = (c k).state k

theorem endpoint_eq_of_homotopy : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    {p q : Path initial.anchor y}, p.Homotopy q →
  ∀ (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint

theorem endpoint_eq [SimplyConnectedSpace M] : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    (p q : Path initial.anchor y)
    (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint
end CartanSuppliedHomotopyEndpoints
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedHomotopyEndpoints.lean
git diff --check
```

Exact stop condition: All four targets compile, including full state equality for arbitrary boundary subdivisions/policies. A grid theorem still asking for unproduced equality balls or a same-node comparison alone is only partial. Do not introduce source simple connectivity before it is used to obtain the path homotopy; do not substitute sphere simple connectivity for it.

## 17. `Poincare/Global/CartanSuppliedTerminalTransport.lean`

Namespace: `Poincare.CartanSuppliedTerminalTransport`.

Imports: task 15. Task 16 is not needed for these targets.

Objective: prove the short-terminal-path and concatenation laws needed to identify a developing map with a terminal germ. `exists_short_paths` uses local path connectedness of a manifold, as established in S9 by `ChartedSpace.locPathConnectedSpace`, to choose an open path connected neighborhood inside the positive mesh ball. Alternatively, S16 supplies short smooth terminal curves, followed by their distance/diameter estimates. This task does not need any metric regularity of the patch policy.

For `short_path_endpoint`, all path points remain within one mesh of the initial anchor. Supply direct data from the initial fallback patch to each point by H1, and compare the realized chain with those direct successors using task 12 and S2. This is the supplied version of the short-terminal comparisons consumed in S8's restricted-atlas proof. The conclusion compares full states to every actual terminal datum, not merely target values.

For `endpoint_trans`, realize the concatenation with times scaled into its first and second halves, attaching the two actual reached chains at the middle state. Compare it with `C` by task 15. The endpoint anchor equation from task 14 provides `h`; `q.cast h rfl` only changes its endpoint proof and is the existing `Path.cast` in Mathlib's `Topology/Path.lean`. S11's finite reparameterization/refinement geometry and S8's direct-boundary construction are the templates. Supplying the dependent chain at the middle state and proving its samples follow `p.trans q` are new. No path-homotopy invariance is used to establish concatenation.

```lean
namespace CartanSuppliedTerminalTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

theorem exists_short_paths : ∀ (S : System g) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
    ∀ z ∈ W, ∃ q : Path x z,
      letI : MetricSpace M := g.toMetricSpace
      ∀ t : unitInterval, dist (q t) x < S.mesh

theorem short_path_endpoint : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (q : Path initial.anchor y) (R : Realization S initial q),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ t : unitInterval, dist (q t) initial.anchor < S.mesh) →
  ∀ d : Data (S.cover.interp (fallback S.cover initial)) initial y,
    R.endpoint = d.successor

theorem endpoint_trans : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {x y : M} (p : Path initial.anchor x) (q : Path x y)
    (R : Realization S initial p) (h : R.endpoint.anchor = x)
    (T : Realization S R.endpoint (q.cast h rfl))
    (C : Realization S initial (p.trans q)), C.endpoint = T.endpoint
end CartanSuppliedTerminalTransport
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedTerminalTransport.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedTerminalTransport.lean
git diff --check
```

Exact stop condition: All three targets compile, especially the every-datum short-path state equality and concatenation with its exact dependent start state. A path-existence lemma alone, a value-only equality without the needed successor comparison, or an assumed concatenation law is partial progress.

## 18. `Poincare/Global/CartanSuppliedRestrictedDevelopment.lean`

Namespace: `Poincare.CartanSuppliedRestrictedDevelopment`.

Imports: tasks 16 and 17, `Poincare.Global.CartanRestrictedOverlapCompatibility`.

Objective: form the total map from rooted endpoints and prove it is locally the selected terminal supplied germ. This uses the direct supplied-germ option in the task, with a new restricted atlas containing arbitrary open partial homeomorphisms.

`development R x` is the target of the reached terminal state. `terminalGerm` uses the covering fallback at that state; task 14 places its anchor at `x`, and S1.`anchor_laws` identifies its value at `x` with that target. The terminal label need not be the last predecessor's label. Task 12 supplies the relevant switch agreement.

To prove `development_eqOn_terminal_neighborhood`, choose the short-path neighborhood from task 17 and intersect it with the terminal germ source. For `z` in this neighborhood, realize the short path from `x` to `z` starting at the terminal state at `x`. H1 supplies direct terminal data, and task 17 identifies its target with `terminalGerm R x z`. Concatenation identifies the endpoint of the rooted path to `x` followed by this short path. Task 16 compares that concatenated realization to the rooted realization chosen at `z`. This is the new supplied replacement for S8.`restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry`; no equality on maximal packaged sources is requested.

Choose each `domain x` from this neighborhood theorem. On `domain x ∩ domain y`, both germs equal `development`, giving `compatible`. Reuse S12's `diagonalDevelopment_eqOn_domain` and `isLocalHomeomorph_diagonalDevelopment` proof text with the supplied `germ` field: restrict `A.germ x` to `A.domain x`, show `x` belongs, and prove agreement with the diagonal. These existing theorems cannot be applied directly to the new structure, since S12's old `germ` definition is hardwired to `CartanMap.openPartialHomeomorph`. The target is an actual total local homeomorphism, not an atlas whose compatibility remains a hypothesis.

```lean
namespace CartanSuppliedRestrictedDevelopment
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

structure RestrictedAtlas (M : Type u) [TopologicalSpace M] where
  germ : M → OpenPartialHomeomorph M RoundSphere3
  domain : M → Set M
  isOpen_domain : ∀ x, IsOpen (domain x)
  anchor_mem_domain : ∀ x, x ∈ domain x
  domain_subset_source : ∀ x, domain x ⊆ (germ x).source
  compatible : ∀ x y, EqOn (germ x) (germ y) (domain x ∩ domain y)

def RestrictedAtlas.diagonal (A : RestrictedAtlas M) : M → RoundSphere3 :=
  fun x => A.germ x x

def terminalState {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : CartanChain.ChainState g :=
  (R.realization x).endpoint

def terminalGerm {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) (x : M) : OpenPartialHomeomorph M RoundSphere3 :=
  germ (S.cover.interp (fallback S.cover (terminalState R x))) (terminalState R x)

def development {S : System g}
    {sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (R : RootedRealization S sk) : M → RoundSphere3 :=
  fun x => (terminalState R x).target

theorem development_eqOn_terminal_neighborhood [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ (terminalGerm R x).source ∧
    EqOn (development R) (terminalGerm R x) W

theorem exists_restrictedAtlas [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk),
  ∃ A : RestrictedAtlas M, A.germ = terminalGerm R ∧ A.diagonal = development R

theorem isLocalHomeomorph_diagonal : ∀ A : RestrictedAtlas M,
  IsLocalHomeomorph A.diagonal

theorem isLocalHomeomorph_development [SimplyConnectedSpace M] :
  ∀ (S : System g) (sk : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (R : RootedRealization S sk), IsLocalHomeomorph (development R)
end CartanSuppliedRestrictedDevelopment
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedRestrictedDevelopment.lean
git diff --check
```

Exact stop condition: All four targets compile, including source inclusion and equality with the total rooted-endpoint map on open neighborhoods. A compatible atlas constructor taking compatibility as a new geometric premise, or only a generic-source adapter without verified domain shrinking, is failure.

## 19. `Poincare/Global/CartanSuppliedUnitRecognition.lean`

Namespace: `Poincare.CartanSuppliedUnitRecognition`.

Imports: task 18, `Poincare.Global.ConnectionInstanceNaturality`, `Poincare.Global.CartanTwoNeighborhoodDevelopment`.

Objective: discharge the unchanged developing-map and unit-recognition interfaces and expose the universal recognition theorem consumed by the Hamilton reduction.

For `controlled_globalLocalDevelopment`, introduce a metric `g` and its unit-curvature proof. Construct task 11's quantitative cover, task 12's switch control, S9's rooted skeleton, task 14's realization, and task 18's developing map. The supplied geometry can be stronger than needed and work for arbitrary chart instances; the public adapter still explicitly accepts the controlled instance with its compatible auxiliary metric. Its auxiliary chart-control distance `d` and the geometric chain distance `g.toMetricSpace` are distinct parameters. No equality of these distances is assumed. S4 uses the latter.

Apply S13.`RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment` for `controlled_unitRecognition`. The covering and sphere topology require no new proof and the conclusion is S14's literal `UnitConstantCurvatureSphereRecognition3`, not a renamed interface.

For `unitRecognition` on the original instance, first introduce its `g` and unit-curvature proof and use `d := g.toMetricSpace`, whose topology agrees by S17. Apply S7.`ConnectionInstanceNaturality.exists_controlled_recognition_reduction'`. It returns `charts`, a positive chart-source radius, atlas finiteness, a manifold instance `hs`, and the recognition implication back to the original instance. Install exactly `charts` and `hs`, invoke `controlled_unitRecognition` with the returned finite-atlas/ball clauses and compatible auxiliary metric, and apply the returned implication to obtain original-instance recognition; then evaluate it on the original `g`. This ordering avoids requiring a Riemannian metric before introducing the recognition input. The reduction uses `replaceTopology`; retain its exact instance when passing the ball clause. It does not require proving an equality between the transported metric distance and `d`.

The universal target reuses S14's existing `UniversalUnitConstantCurvatureSphereRecognitionStatement`. Its universe `u` and all nine binders match the displayed final Hamilton target. Apply S14.`poincareConjecture_of_hamiltonConvergence_of_unitRecognition` with this universal proof. The last target still assumes Hamilton convergence; it is not the reserved unconditional `Poincare.poincare_conjecture`. S14.`globalLocalDevelopment_of_two_neighborhoods` supplies the assembly pattern only: none of its legacy generic H1/H2 premises is asserted by this new route.

```lean
namespace CartanSuppliedUnitRecognition
open CartanSuppliedFinitePatchCover
variable [SecondCountableTopology M] [SimplyConnectedSpace M]

theorem controlled_globalLocalDevelopment : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M)

theorem controlled_unitRecognition : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitConstantCurvatureSphereRecognition3 M

theorem unitRecognition : UnitConstantCurvatureSphereRecognition3 M

theorem universal_unitRecognition :
  CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement.{u}

theorem poincare_of_hamiltonConvergence :
  (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonConvergencePinchedLimit3 N) → PoincareConjecture.{u}
end CartanSuppliedUnitRecognition
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUnitRecognition.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedUnitRecognition.lean
git diff --check
```

Exact stop condition: All five targets compile with no extra patch-cover, switch, mesh, homotopy, atlas-compatibility or recognition premise. The final theorem may retain exactly the displayed Hamilton premise. Stop with the exact controlled-instance/metric/curvature transport type if adaptation fails; do not change the frozen recognition statement or claim unconditional Poincare completion.

```lean
end Poincare
```

## Patch-switch and consumer audit

| Event | What can be used | What must still be proved |
| --- | --- | --- |
| Same geometric state in two retained patches | S15's source-normal/frame and target-inverse comparison, composed by S2.`patch_germ_eventuallyEq_generic`, gives agreement near that state's anchor. | Task 12's radius common to all buffer states/alignments. A pair of pointwise neighborhoods is not this radius. |
| Differential successor within one selected patch | S4 H1 produces every step's actual data; H2 compares the predecessor and the re-anchored map on its full evaluation ball for every datum. | Task 11's uniform minima and buffer retention. H1's open-anchor conclusion alone does not keep a successor in the same compact core. |
| Selection changes at the successor | The old successor and the new selected interpretation represent the same geometric state. S2/S15 give anchor-germ agreement once both patch memberships are known. | The old membership comes from task 11 retention; the new membership from task 13 selection. Task 12 combines the uniform switch bound with H2 to keep an evaluation ball available for subsequent vertices. |
| Same nodes, different policy schedules | S5.`state_eq_of_open_agreement` and S2 derivative uniqueness compare actual successor states. | Agreement on an open neighborhood of each next node. Task 13 obtains it from the uniform switch bound and equal prefixes. |
| Refined paths or different homotopy rows | S11 parameter refinements; S10 ladder proof; S4 evaluation balls. | Tasks 15–16 supply data at inserted/rung vertices, their map agreement and exact boundary transport. S5 alone does not compare different node functions. |
| Global gluing | S12 topological restriction proof and S13 covering recognition. | Tasks 17–18 identify actual rooted endpoints with each terminal supplied germ on a neighborhood and prove overlap compatibility there. |

This route adds no continuity requirement on the global patch selector, no equality of supplied and generic source sets, and no reuse of legacy `JointUniformSuccessorRadiusCertificate` by type coercion. The exact type distinctions are S1/S5 versus S8/S12/S14. All additional certificate fields in the proposed definitions have explicit production targets in tasks 11–12; none remains a final adapter hypothesis.

## Reproduce the target checks

Only definitions/structures and target proposition bodies were elaborated. The following regenerates the scratch file entirely from this report; it does not edit any Lean source. There are 32 theorem targets. The initial scratch attempts are retained under `/tmp/parametrization-plan-3-evidence`: attempt 01 failed because an unnecessary Mathlib metrizability import had no cached olean; attempt 02 failed because grouped structure-field syntax was invalid; attempt 03 passed after fixing fields and enabling `autoImplicit false`; attempt 04 passed with the additional terminal-transport and mesh/anchor targets. These are interface checks, not theorem proofs or a clean rebuild of the import graph.

```sh
python3 - <<'PYPROBE'
from pathlib import Path
import re
report = Path('harness/reports/parametrization-plan-3.md').read_text()
code = '\n\n'.join(re.findall(r'```lean\n(.*?)\n```', report, re.S))
assert len(re.findall(r'(?m)^theorem ', code)) == 32
code = re.sub(r'(?m)^theorem (\w+)(.*?) :',
              r'def \1_spec\2 : Prop :=', code)
Path('/tmp/parametrization-plan-3-report-probe.lean').write_text(code)
PYPROBE
LEAN_NUM_THREADS=1 lake env lean /tmp/parametrization-plan-3-report-probe.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' /tmp/parametrization-plan-3-report-probe.lean
git diff --check
```

The declaration probe checked 60 existing names in `/tmp/parametrization-plan-3-evidence/declarations.lean`. Its first attempt included the nonexistent namespaced spelling `Metric.lebesgue_number_lemma_of_metric`; removing that check left the correct unqualified `lebesgue_number_lemma_of_metric` and all 60 declarations passing. The final successful outputs are `contracts-04.log` and `declarations-02.log`. The report-extracted probe exited 0 with no output; the log is `report-probe-01.log`. The extracted Lean prohibited-token scan had no matches. The final staged diff contains this report only and passes the whitespace check. No source build or root integration audit was run for this analysis-only deliverable.

Exact first orchestrator action: regenerate the report probe at `92f944c671d72d19f7dee20081f19efbfdd42053`, run the displayed Lean command, and review task 12's uniform comparison obligation before freezing tasks 11–12. In particular, do not dispatch a plan in which fixed-anchor eventual equality is silently treated as an already proved uniform switch radius.
