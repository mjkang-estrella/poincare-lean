# Next five chain parametrization tasks

Date: 2026-09-08. Analysis branch: `worker/parametrization-plan-2`.
Base and verified local `main` at start: `64f6fc2d1d0ee5bfa140f2d9a4cc71f8efadb807`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

This is a specification, not an implementation or a proof of H1/H2. The five tasks are numbered 6–10 to continue [the inventory](chain-parametrization-inventory.md). The base is the live Git commit observed at start, not the pending-review language in the older completion reports. The five landed modules are present at this commit. Their declarations and imports were read; the named declarations below were located in source and the entire proposed interface was elaborated in `/tmp`.

At final verification, `main` had advanced to `826021b2c4272a010b0b556168c996588c488955`. The complete diff from the recorded base changes only `HANDOFF.md` and `harness/ledger.json`; all Lean sources, the toolchain, and Lake configuration are identical. Thus the scratch declarations also match that current `main` source tree. This analysis branch remains based on the assigned commit.

## Decisions and limits

Keep `CartanChain.ChainState` as the geometric triple `anchor, target, alignment`. Give its map an explicit interpretation. A retained source patch uses its fixed chart host and its fixed velocity frame. A retained **target** patch uses the same construction on `roundSphereMetric3`; otherwise the new quantitative contracts would still depend on an uncontrolled moving target normal source. The connecting linear map is `J_target⁻¹ ∘ L ∘ J_source`. These are proposed definitions below, based on [S1], [S3], [S4], and [S5]. No new globally jointly regular family is assumed.

The identity-frame generic interpretation recovers the old total forward map. The fixed-patch interpretation has only a fixed-anchor germ comparison with that map. In particular, agreement near predecessor anchor `x` does not establish agreement near an arbitrary successor `z`, and separate neighborhoods for each `L` do not establish one neighborhood for every `L`. These distinctions are visible in [S1].`generic_map_eq`, [S4].`normal_eventuallyEq_generic_in_anchor_frame`, and [S7].`exists_uniform_local_eqOn_differentialSuccessor_all`.

The new data structure retains all thirteen original fields through `CoordinateData`, and adds exact supplied-germ source membership. It also carries an alignment with a proof that it is the actual reanchored derivative. That alignment is not an arbitrary isometry choice: uniqueness of the derivative is the intended witness-independence argument, as in [S5].`Data.alignment_clm_eq_of_reanchoredChartMap_eventuallyEq`. Task 7 must construct these last two fields from `CoordinateData`; accepting only the structure declaration does not discharge that task.

## Source and declaration index

Each source reference below names declarations checked by source search. References to proposed declarations mean the exact type checks in the later sections, not existing proofs.

| Ref | File and verified declarations |
| --- | --- |
| S1 | [CartanSuppliedSourceMap.lean](../../Poincare/Global/CartanSuppliedSourceMap.lean): `CartanSuppliedSourceMap.germ`, `anchor_mem_source`, `germ_anchor`, `germ_apply`, `generic_map_eq`. |
| S2 | [CartanSuppliedSourceGermTransfer.lean](../../Poincare/Global/CartanSuppliedSourceGermTransfer.lean): `CartanSuppliedSourceGermTransfer.germ_eventuallyEq_of_normal_eventuallyEq`, `normal_symm_eventuallyEq_of_normal_eventuallyEq`, `exists_open_common_source_agreement`. |
| S3 | [FixedChartUniformSourceNormal.lean](../../Poincare/Global/FixedChartUniformSourceNormal.lean): `FixedChartUniformSourceNormal.Patch`, `exists_patch`, `Patch.endpoint`, `Patch.normal`, `Patch.normal_source`, `Patch.normal_apply`, `Patch.anchors`, `Patch.isOpen_normal_sourceLocus`, `Patch.continuousOn_normal_eval`, `Patch.rawLocalFamily`, both endpoint/normal anchor laws, `Patch.endpoint_source_position_mem`. [FixedChartEndpointSlices.lean](../../Poincare/Global/FixedChartEndpointSlices.lean): `FixedChartEndpointSlices.slice`, `symm_fst`, `isOpen_slice_sourceLocus`, `isOpen_slice_targetLocus`, `continuousOn_slice_eval`, `continuousOn_slice_symmEval`. |
| S4 | [FixedChartUniformPreferredGermAgreement.lean](../../Poincare/Global/FixedChartUniformPreferredGermAgreement.lean): `FixedChartUniformPreferredGermAgreement.anchorFrame`, `anchorFrame_isInvertible`, `normalized_endpoint_eventuallyEq_expAt`, `normal_eventuallyEq_generic_in_anchor_frame`. |
| S5 | [DifferentialInducedSuccessor.lean](../../Poincare/Global/DifferentialInducedSuccessor.lean): `DifferentialInducedSuccessor.Data`, `Data.alignment`, `Data.hasFDerivAt_reanchoredChartMap`, `Data.alignment_clm_eq_of_reanchoredChartMap_eventuallyEq`, `Data.successor_eq_of_eqOn_open`, `Data.anchor_mem_predecessor_source`, `Data.vector_eq`, `Data.successor_eq`, `Chain.ReachableChain`, `Chain.ReachableChain.state_eq`, `Chain.reachableChainOfStepAvailable`. |
| S6 | [CartanTargetExponentialFamily.lean](../../Poincare/Global/CartanTargetExponentialFamily.lean): `CartanTargetExponential.inducedTangentAlignmentOfCoordinatePullback`; [InducedAlignment.lean](../../Poincare/Global/InducedAlignment.lean): `InducedAlignment.continuousLinearEquivOfInvertible`; [CartanMap.lean](../../Poincare/Global/CartanMap.lean): `CartanMap.TangentAlignment`, `TangentAlignment.toContinuousLinearEquiv`, `TangentAlignment.map_app`. |
| S7 | [DifferentialSuccessorIntervalNaturality.lean](../../Poincare/Global/DifferentialSuccessorIntervalNaturality.lean): `DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`; [DifferentialSuccessorZero.lean](../../Poincare/Global/DifferentialSuccessorZero.lean): `DifferentialSuccessorZero.anchorData`, `exists_data_on_ball`, `successor_eq_of_vector_eq_zero`, `anchorData_successor`. |
| S8 | [DifferentialSuccessorAdjacentContinuation.lean](../../Poincare/Global/DifferentialSuccessorAdjacentContinuation.lean): `DifferentialSuccessorAdjacentContinuation.CrossHistorySuccessorAgreement`, `CoordinateControlledCommonSource`, `crossHistorySuccessorAgreement_of_eqOn_open`, `reachableChains_ladder_invariant`, `reachableChains_endpoint_eq`, `successor_anchor_mem_coordinateControlledCommonSource`, `exists_metricBall_eqOn_coordinateControlled_of_pathIndependence`. |
| S9 | [CartanCanonicalRootedDirectGenericNeighborhoodRecognition.lean](../../Poincare/Global/CartanCanonicalRootedDirectGenericNeighborhoodRecognition.lean): `CartanCanonicalRootedDirectGenericNeighborhoodRecognition.exists_genericRootedRealization_with_wholeCellMesh_of_certificate`, `restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry`. |
| S10 | [CartanGenericSuccessorDataLocalCover.lean](../../Poincare/Global/CartanGenericSuccessorDataLocalCover.lean): `CartanGenericSuccessorDataLocalCover.LocalUniformNormalGenericSuccessorDataOn`, `localGenericSuccessorDataCover_iff_universalSuccessorDataNeighborhood`; [CartanAtlasRootedPathCurvatureSuccessorRadius.lean](../../Poincare/Global/CartanAtlasRootedPathCurvatureSuccessorRadius.lean): `CartanAtlasRootedPathCurvatureSuccessorRadius.exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature`, `UniversalSuccessorDataNeighborhood`. |
| S11 | [DifferentialSuccessorJointEqualityNeighborhood.lean](../../Poincare/Global/DifferentialSuccessorJointEqualityNeighborhood.lean): `DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityLocus`, `UniversalSuccessorEqualityNeighborhood`; [DifferentialUniformSuccessorMesh.lean](../../Poincare/Global/DifferentialUniformSuccessorMesh.lean): `DifferentialUniformSuccessorMesh.UniformSuccessorEqOnBall`. |
| S12 | [TangentAlignmentFiberCompactness.lean](../../Poincare/Global/TangentAlignmentFiberCompactness.lean): `CartanMap.isCompact_tangentAlignmentOperatorFiber`, `exists_pos_uniform_tangentAlignment_operatorNorm_bound`, `exists_pos_uniform_tangentAlignment_inverseOperatorNorm_bound`; [UniformTangentAlignmentRigidity.lean](../../Poincare/Global/UniformTangentAlignmentRigidity.lean): `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`. These are fixed-anchor results, not moving-anchor estimates. |
| S13 | [CartanSourceExponentialFamily.lean](../../Poincare/Global/CartanSourceExponentialFamily.lean): `CartanSourceExponential.Family`, `genericFamily`, `Family.JointlyRegular`; [CartanRestrictedOverlapCompatibility.lean](../../Poincare/Global/CartanRestrictedOverlapCompatibility.lean): `UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3.isLocalHomeomorph_diagonalDevelopment`, `UnitRecognitionNext.globalLocalDevelopment_of_restrictedCompatibleCartanAtlas`. |

The read completion reports are [supplied source map](supplied-source-map_done.md), [germ transfer](supplied-source-germ-transfer_done.md), [endpoint slices](fixed-chart-endpoint-slices_done.md), [uniform source normal](fixed-chart-uniform-source-normal_done.md), and [task 5](parametrization-task-5_done.md). The design also uses [HANDOFF.md, “2026-09-08 Repair track and audit payload caching”](../../HANDOFF.md). The statements in source, especially S3/S4, determine the limits above.

## Shared contract and verification convention

Task 6 starts at the recorded base. Each later implementation task freezes a new base containing its accepted predecessors. Tasks 6→7→8→9→10 are the requested dependency order; task 10's abstract recursion only needs tasks 6–7, while the later geometric dispatcher will need 8–9. Each task owns exactly the one new file named in its heading. All existing Lean files, `Poincare.lean`, audit wiring, and the other tasks' files are forbidden. This report-only attempt owns only this Markdown file; it does not update `HANDOFF.md`.

The following blocks give complete definitions and full theorem signatures. The signatures intentionally have no proof bodies. For declaration/type checking, each `theorem name : P` is transformed into `def name_spec : Prop := P`; no proof placeholder, axiom, or implementation of a target is introduced. Concatenating the blocks in order is the checked scratch contract. The broad existing import envelope below is for that scratch file. Each task's intended imports are specified separately.

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

```

## 6. `Poincare/Global/CartanSuppliedDifferentialSuccessor.lean`

Namespace: `Poincare.CartanSuppliedDifferentialSuccessor`.
Imports: `Poincare.Global.FixedChartUniformPreferredGermAgreement`, `Poincare.Global.DifferentialInducedSuccessor`.

Objective: make the actual supplied map, its coordinates, and its differential witnesses explicit, while retaining the geometric state. Reuse S1's composition formula and generic comparison, S3's exact endpoint/normal domains and anchor laws, S4's frame invertibility, S5's field layout, and S6's continuous-linear-equivalence constructor. `patchFrame` has an identity extension outside the anchors solely to define a total function. No regularity or geometric law is asserted there; quantitative tasks require anchor membership.

`sourceExp` and `targetExp` are the supplied endpoints expressed in explicitly stored host charts. They may have extra domain restrictions and are not definitionally the old exponential charts even for `generic`. `source_mem_oldChart` and `target_mem_oldChart` retain their consumer roles but now refer to those explicit hosts. For `patch C D` these hosts are fixed `x₀,p₀`, not the moving anchors. A port must use those hosts wherever the old proof used `s.anchor,s.target` as coordinate-chart centers. See S5.`Data` and S8.`successor_anchor_mem_coordinateControlledCommonSource`.

```lean
namespace CartanSuppliedDifferentialSuccessor
structure Interpretation (g : ClosedSmoothRiemannianMetric 3 M) where
  sourceAnchors : Set M
  targetAnchors : Set RoundSphere3
  sourceNormal : M → OpenPartialHomeomorph M E
  targetNormal : RoundSphere3 → OpenPartialHomeomorph RoundSphere3 E
  sourceFrame : M → E ≃L[ℝ] E
  targetFrame : RoundSphere3 → E ≃L[ℝ] E
  sourceHost : M → M
  targetHost : RoundSphere3 → RoundSphere3
  source_anchor_mem : ∀ x ∈ sourceAnchors, x ∈ (sourceNormal x).source
  source_anchor_zero : ∀ x ∈ sourceAnchors, sourceNormal x x = 0
  target_anchor_mem : ∀ p ∈ targetAnchors, p ∈ (targetNormal p).source
  target_anchor_zero : ∀ p ∈ targetAnchors, targetNormal p p = 0

def generic (g : ClosedSmoothRiemannianMetric 3 M) : Interpretation g where
  sourceAnchors := univ
  targetAnchors := univ
  sourceNormal := (CartanSourceExponential.genericFamily g).normal
  targetNormal := (CartanSourceExponential.genericFamily roundSphereMetric3).normal
  sourceFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  targetFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  sourceHost := id
  targetHost := id
  source_anchor_mem := fun x _ => (CartanSourceExponential.genericFamily g).anchor_mem_source x
  source_anchor_zero := fun x _ => (CartanSourceExponential.genericFamily g).normal_anchor x
  target_anchor_mem := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).anchor_mem_source p
  target_anchor_zero := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).normal_anchor p

def patchFrame {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) : E ≃L[ℝ] E :=
  @dite _ (x ∈ C.anchors) (Classical.propDecidable _) (fun hx =>
    InducedAlignment.continuousLinearEquivOfInvertible
      (FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x)
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx))
    (fun _ => ContinuousLinearEquiv.refl ℝ E)

def patch {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V) :
    Interpretation g where
  sourceAnchors := C.anchors
  targetAnchors := D.anchors
  sourceNormal := C.normal
  targetNormal := D.normal
  sourceFrame := patchFrame C
  targetFrame := patchFrame D
  sourceHost := fun _ => x₀
  targetHost := fun _ => p₀
  source_anchor_mem := C.anchor_mem_normal_source
  source_anchor_zero := C.normal_anchor
  target_anchor_mem := D.anchor_mem_normal_source
  target_anchor_zero := D.normal_anchor

def linear (Q : Interpretation g) (s : CartanChain.ChainState g) : E ≃L[ℝ] E :=
  ((Q.sourceFrame s.anchor).trans s.alignment.toContinuousLinearEquiv).trans
    (Q.targetFrame s.target).symm

def germ (Q : Interpretation g) (s : CartanChain.ChainState g) :
    OpenPartialHomeomorph M RoundSphere3 :=
  (Q.sourceNormal s.anchor).trans
    ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
      (Q.targetNormal s.target).symm)

def map (Q : Interpretation g) (s : CartanChain.ChainState g) : M → RoundSphere3 :=
  germ Q s

def sourceExp (Q : Interpretation g) (x : M) : OpenPartialHomeomorph E E :=
  (Q.sourceNormal x).symm.trans (chartAt E (Q.sourceHost x))

def targetExp (Q : Interpretation g) (p : RoundSphere3) : OpenPartialHomeomorph E E :=
  (Q.targetNormal p).symm.trans (chartAt E (Q.targetHost p))

def chartMap (Q : Interpretation g) (s : CartanChain.ChainState g) : E → E :=
  fun z => targetExp Q s.target (linear Q s ((sourceExp Q s.anchor).symm z))

def chartDifferential (Q : Interpretation g) (s : CartanChain.ChainState g)
    (A B : E ≃L[ℝ] E) : E →L[ℝ] E :=
  ((A.symm.trans (linear Q s)).trans B : E ≃L[ℝ] E)

def reanchoredChartMap (Q : Interpretation g) (s : CartanChain.ChainState g)
    (z : M) : E → E :=
  fun w => extChartAt I (map Q s z) (map Q s ((extChartAt I z).symm w))

structure CoordinateData (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M) where
  source_anchor_valid : s.anchor ∈ Q.sourceAnchors
  target_anchor_valid : s.target ∈ Q.targetAnchors
  source_mem : z ∈ (germ Q s).source
  v : E
  A : E ≃L[ℝ] E
  B : E ≃L[ℝ] E
  source_vector_mem : v ∈ (sourceExp Q s.anchor).source
  target_vector_mem : linear Q s v ∈ (targetExp Q s.target).source
  source_mem_oldChart : z ∈ (extChartAt I (Q.sourceHost s.anchor)).source
  target_mem_oldChart : map Q s z ∈ (extChartAt I (Q.targetHost s.target)).source
  source_coordinate : extChartAt I (Q.sourceHost s.anchor) z = sourceExp Q s.anchor v
  target_coordinate : extChartAt I (Q.targetHost s.target) (map Q s z) =
    targetExp Q s.target (linear Q s v)
  source_exp_derivative : HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E) v
  target_exp_derivative : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E) (linear Q s v)
  cartan_chart_derivative : HasStrictFDerivAt (chartMap Q s)
    (chartDifferential Q s A B) (sourceExp Q s.anchor v)
  metric_pullback : ∀ u u' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost s.target)
      (targetExp Q s.target (linear Q s v))
      (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
    CovariantDerivative.chartMetric g.inner (Q.sourceHost s.anchor)
      (sourceExp Q s.anchor v) u u'

structure Data (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    extends CoordinateData Q s z where
  alignment : CartanMap.TangentAlignment g z (map Q s z)
  hasFDerivAt_reanchoredChartMap : HasFDerivAt (reanchoredChartMap Q s z)
    (alignment.toContinuousLinearEquiv : E →L[ℝ] E) (extChartAt I z z)

def Data.successor {Q : Interpretation g} {s : CartanChain.ChainState g} {z : M}
    (d : Data Q s z) : CartanChain.ChainState g :=
  ⟨z, map Q s z, d.alignment⟩

-- TARGET 6.1
theorem anchor_laws : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g),
  s.anchor ∈ Q.sourceAnchors → s.target ∈ Q.targetAnchors →
  s.anchor ∈ (germ Q s).source ∧ map Q s s.anchor = s.target
-- TARGET 6.2
theorem generic_map_eq : ∀ (s : CartanChain.ChainState g), map (generic g) s = s.map
-- TARGET 6.3
theorem vector_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.v = Q.sourceNormal s.anchor z
-- TARGET 6.4
theorem successor_fields : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.successor.anchor = z ∧
  d.successor.target = map Q s z ∧ z ∈ (germ Q s).source
-- TARGET 6.5
theorem eq_anchor_of_vector_eq_zero :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z), d.v = 0 → z = s.anchor
end CartanSuppliedDifferentialSuccessor
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All five targets and the displayed definitions compile. In particular, prove total forward-map equality for `generic`, and the stored-vector/source formulas for the supplied map. Stop blocked if a generic comparison can only be obtained by asserting equality of selected source sets; record the exact surviving map/domain goal.

## 7. `Poincare/Global/CartanSuppliedDifferentialTransfer.lean`

Namespace: `Poincare.CartanSuppliedDifferentialTransfer`.
Imports: task 6, `Poincare.Global.DifferentialSuccessorIntervalNaturality`.

Objective: construct an actual differential-induced alignment from coordinate data; prove independence and cross-interpretation congruence; identify the generic instance and transfer fixed-anchor germs. No extra definitions are needed.

Reuse S5's derivative uniqueness and dependent-state equality arguments. S6.`inducedTangentAlignmentOfCoordinatePullback` is a model for the construction, **not** a direct instance for arbitrary fixed hosts: its `L₀` is aligned at its own old-chart anchors and its derivative factors through that `L₀`. Here `linear Q s` is an arbitrary framed equivalence. Re-prove the coordinate-pullback-to-reanchored-isometry construction for the displayed `CoordinateData`, using the invertible source/target chart-transition derivatives, and then construct `Data.alignment`. The metric-pullback hypothesis is retained verbatim in meaning, so this task adds no geometric isometry existence claim.

`ofGeneric` and `toGeneric` are existential adapter theorems, not definitions requiring a new selector. They preserve the normal vector and geometric successor, not equality of source sets or exact analytic witnesses. Use S1.`generic_map_eq` and local inverse-chart identities to move derivatives between the two coordinate presentations. `generic_interval_equality` is the generic consumer instance of S7 after these adapters, with a smaller open neighborhood to retain old and new sources. `local_equality_transfer` states precisely the extra neighborhood agreements needed to apply that instance to an arbitrary interpretation. S4 supplies the successor-anchor comparison when that anchor is retained; it does not by itself supply the predecessor comparison at the successor.

`patch_successor_at_anchor` retains the zero-step law used in S8's endpoint/ladder proofs, via S7.`anchorData_successor` and the patch germ comparison. Task 6's `eq_anchor_of_vector_eq_zero` reduces a zero vector to this anchor case. Do not assert the anchor-successor law for an arbitrary `Interpretation`: its normal charts and frames need not have anchor derivative equal to the stored predecessor alignment. The generic and geometric patch instances do have the needed comparison.

For `patch_germ_eventuallyEq_generic`, apply S4 on **both** retained patches, undo the target frame in the inverse-normal germ, and compose as in S2. The inverse-normal argument must use the partial inverse laws on their domains; do not claim equality of total inverses from S4.

```lean
namespace CartanSuppliedDifferentialTransfer
variable [T2Space M]
open CartanSuppliedDifferentialSuccessor
-- TARGET 7.1
theorem data_of_coordinateData : ∀ (Q : Interpretation g)
  (s : CartanChain.ChainState g) (z : M) (w : CoordinateData Q s z),
  ∃ d : Data Q s z, d.toCoordinateData = w
-- TARGET 7.2
theorem alignment_clm_eq_of_eventuallyEq :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z),
  reanchoredChartMap Q s z =ᶠ[𝓝 (extChartAt I z z)] reanchoredChartMap R t z →
  (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
    (e.alignment.toContinuousLinearEquiv : E →L[ℝ] E)
-- TARGET 7.3
theorem successor_eq_of_eqOn_open :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z) (W : Set M),
    IsOpen W → z ∈ W → EqOn (map Q s) (map R t) W → d.successor = e.successor
-- TARGET 7.4
theorem successor_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d e : Data Q s z), d.successor = e.successor
-- TARGET 7.5
theorem ofGeneric : ∀ (s : CartanChain.ChainState g) (z : M)
    (d : DifferentialInducedSuccessor.Data s z),
    ∃ e : Data (generic g) s z, e.successor = d.successor ∧ e.v = d.v
-- TARGET 7.6
theorem toGeneric : ∀ (s : CartanChain.ChainState g) (z : M)
    (e : Data (generic g) s z),
    ∃ d : DifferentialInducedSuccessor.Data s z, d.successor = e.successor ∧ d.v = e.v
-- TARGET 7.7
theorem patch_germ_eventuallyEq_generic :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (s : CartanChain.ChainState g), s.anchor ∈ C.anchors → s.target ∈ D.anchors →
    map (patch C D) s =ᶠ[𝓝 s.anchor] s.map
-- TARGET 7.8
theorem generic_interval_equality :
  HasConstantSectionalCurvature3 g 1 → ∀ (x : M) (p : RoundSphere3),
  ∃ ρ > (0 : ℝ), ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : Data (generic g) ⟨x, p, L⟩ z), ‖d.v‖ < ρ →
    ∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn (map (generic g) ⟨x, p, L⟩) (map (generic g) d.successor)
        (W ∩ ((germ (generic g) ⟨x, p, L⟩).source ∩
          (germ (generic g) d.successor).source))
-- TARGET 7.9
theorem local_equality_transfer :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : DifferentialInducedSuccessor.Data s z),
    d.successor = e.successor →
    map Q s =ᶠ[𝓝 z] s.map →
    map Q d.successor =ᶠ[𝓝 z] e.successor.map →
    (∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn s.germ e.successor.germ (W ∩ (s.germ.source ∩ e.successor.germ.source))) →
    ∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn (map Q s) (map Q d.successor)
        (W ∩ ((germ Q s).source ∩ (germ Q d.successor).source))
-- TARGET 7.10
theorem patch_successor_at_anchor :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (s : CartanChain.ChainState g)
    (d : Data (patch C D) s s.anchor), d.successor = s
end CartanSuppliedDifferentialTransfer
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialTransfer.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialTransfer.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All ten targets compile, including construction from `CoordinateData`, both generic adapters, and the two-patch germ comparison. Stop blocked at the first unclosed chart-transition, metric-pullback, or inverse-germ goal; retain its complete Lean context. Do not replace construction with an extra alignment premise or replace neighborhood equality with value equality.

## 8. `Poincare/Global/FixedChartLocalSuccessorExistence.lean`

Namespace: `Poincare.FixedChartLocalSuccessorExistence`.
Imports: task 7, `Poincare.Global.TangentAlignmentFiberCompactness`, `Poincare.Global.UniformTangentAlignmentRigidity`.

Objective: prove the patchwise replacement of **H1**. The exact replacement is `exists_radius` below, with `OnCompact` fully expanded by its definition. The radius is chosen before `x,p,L,z`; it produces supplied `Data`, proves actual source membership, and retains both new anchors for the next germ. `K,H` are arbitrary compact subsets of the open retained source/target anchor sets, not just single centers. Positive radius for the singleton centers is consequently a substantive special case.

S3 supplies the joint normal domain and evaluator on each patch, and retains the original compact `K,R,ρ` endpoint clause with separate image and injectivity radii. S4 supplies fixed-anchor germ identification. S7/S10 supply old fixed-anchor data-existence theorems; S12 supplies compact alignment fibers and fixed-anchor operator bounds. These are reusable ingredients, not a proof of this statement. In particular, uniform bounds for framed alignments as `x,p` move over `K,H`, and uniform strict differential/metric-pullback witnesses on the retained domains, must be established in this task. One cannot take a minimum of separately chosen per-anchor radii. S10's `LocalUniformNormalGenericSuccessorDataOn` still concludes old `Data` and is not this H1.

This is deliberately an open mathematical task. The C¹ and germ statements in S3/S4 alone do not prove all the `CoordinateData` fields uniformly. If that is the resisting interface, stop with the exact field and quantified type rather than turning it into an extra premise of `exists_radius`.

```lean
namespace FixedChartLocalSuccessorExistence
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3) (η : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ Q.sourceAnchors ∧ map Q ⟨x, p, L⟩ z ∈ Q.targetAnchors ∧
    z ∈ (germ Q ⟨x, p, L⟩).source ∧ Nonempty (Data Q ⟨x, p, L⟩ z)
-- TARGET 8.1
theorem exists_radius :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    ∃ η > (0 : ℝ), OnCompact (patch C D) K H η
end FixedChartLocalSuccessorExistence
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorExistence.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorExistence.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: Prove `exists_radius` exactly for every compact `K,H` satisfying the displayed inclusions, including actual source membership and `Data` production. Otherwise report the exact uniform field/estimate that resists proof and any compiler-verified weaker result. Per-anchor existence, a conditional radius, or old generic `Data` is not success.

## 9. `Poincare/Global/FixedChartLocalSuccessorEquality.lean`

Namespace: `Poincare.FixedChartLocalSuccessorEquality`.
Imports: task 8, `Poincare.Global.DifferentialSuccessorAdjacentContinuation`.

Objective: prove the patchwise replacement of **H2**, namely `exists_radii` with the displayed `OnCompact`. It retains H1 at the same predecessor-step radius `η` and supplies an independent evaluation radius `ε`. Both are chosen before all moving anchors, alignments, and actual data. Equality is quantified over every witness, not a chosen datum.

The conclusion includes `ball z ε ⊆ old.source ∩ new.source`. Consequently it implies source-intersected equality and supports a later full-ball consumer using a radius at most `min η ε`. Source-intersected equality without this inclusion would not replace S11.`UniformSuccessorEqOnBall`. Taking a minimum here means two already uniform positive numbers, never radii extracted from an unrealized chain.

Use task 8 for existence and task 7 for witness independence and any available local comparison. S7's interval theorem supplies a generic fixed-anchor germ equality only. S8's continuation theorem `exists_metricBall_eqOn_coordinateControlled_of_pathIndependence` has an explicit cross-history/path-independence hypothesis and chooses a ball after the anchors/data; neither that hypothesis nor the quantifier order can be silently removed. A new uniform reanchoring/ODE equality argument on the retained patches is required. S3's joint openness can support the domain part once the framed target maps are controlled; it does not prove the equality part. Do not bootstrap this H2 from a future global chain-independence theorem that itself consumes H2.

```lean
namespace FixedChartLocalSuccessorEquality
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3)
    (η ε : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : Data Q ⟨x, p, L⟩ z), dist z x < η →
      Metric.ball z ε ⊆ (germ Q ⟨x, p, L⟩).source ∩ (germ Q d.successor).source ∧
      EqOn (map Q ⟨x, p, L⟩) (map Q d.successor) (Metric.ball z ε)
-- TARGET 9.1
theorem exists_radii :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    ∃ η > (0 : ℝ), ∃ ε > (0 : ℝ),
      FixedChartLocalSuccessorExistence.OnCompact (patch C D) K H η ∧
      OnCompact (patch C D) K H η ε
end FixedChartLocalSuccessorEquality
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorEquality.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorEquality.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: Prove `exists_radii` exactly, including H1 at `η`, the common-source full-ball inclusion, and equality for every datum on the same `ε` ball. Otherwise record the exact equality or domain goal and missing uniform estimate. An anchor-dependent evaluation neighborhood, component-only equality, or a new path-independence premise is not success.

## 10. `Poincare/Global/CartanSuppliedReachableChain.lean`

Namespace: `Poincare.CartanSuppliedReachableChain`.
Imports: task 7. Tasks 8–9 are the preceding geometric contracts, but abstract recursion should not import their proof modules unnecessarily.

Objective: realize and compare chains under an explicit state-dependent patch policy. `Q n s` selects an interpretation at the actually reached geometric state, including its target. The policy is external to `ChainState`; otherwise equality of states would falsely require equality of patch indices. `ReachableChain` only stores data at reached states, as in S5.`Chain.ReachableChain`. `StepAvailable` is an explicit sufficient recursion hypothesis at nodes, not something this task claims from curvature.

Reuse the induction/choice proofs in S5.`Chain.reachableChainOfStepAvailable`, `Chain.ReachableChain.state_anchor_eq_node`, and `Chain.ReachableChain.state_eq`, substituting task 7's witness-independence theorem. Equal states feed the same policy. Different policies require the open-map agreement in `state_eq_of_open_agreement`, using task 7's cross-interpretation theorem. No patch-label equality is needed.

Tasks 8–9 alone do not instantiate `StepAvailable`: their targets range over `H`, and H1 keeps a successor in the open target patch, not necessarily in the same compact `H`. A later covering/mesh task must choose patches and compact cores covering the reached target, and obtain uniform bounds before recursion. S9's existing whole-cell theorem consumes a joint certificate and chooses subdivision before constructing the chain. This task preserves that ordering but does not claim a new whole-cell theorem. The two remaining chain/mesh/overlap files, restricted-atlas file, and final development adapter remain outside this dispatch.

```lean
namespace CartanSuppliedReachableChain
open CartanSuppliedDifferentialSuccessor
structure ReachableChain (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) where
  state : ℕ → CartanChain.ChainState g
  initial_eq : state 0 = initial
  data : ∀ n, Data (Q n (state n)) (state n) (nodes (n + 1))
  successor_eq : ∀ n, state (n + 1) = (data n).successor

def StepAvailable (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) : Prop :=
  ∀ (n : ℕ) (s : CartanChain.ChainState g), s.anchor = nodes n →
    Nonempty (Data (Q n s) s (nodes (n + 1)))
-- TARGET 10.1
theorem exists_reachableChain :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g),
    initial.anchor = nodes 0 → StepAvailable Q nodes → Nonempty (ReachableChain Q nodes initial)
-- TARGET 10.2
theorem state_anchor_eq_node :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial), initial.anchor = nodes 0 →
    ∀ n, (c.state n).anchor = nodes n
-- TARGET 10.3
theorem node_mem_predecessor_source :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (n : ℕ),
    nodes (n + 1) ∈ (germ (Q n (c.state n)) (c.state n)).source
-- TARGET 10.4
theorem state_eq :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c e : ReachableChain Q nodes initial), ∀ n, c.state n = e.state n
-- TARGET 10.5
theorem state_eq_of_open_agreement :
  ∀ (Q R : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain Q nodes initial) (e : ReachableChain R nodes initial),
    (∀ n, ∃ W : Set M, IsOpen W ∧ nodes (n + 1) ∈ W ∧
      EqOn (map (Q n (c.state n)) (c.state n)) (map (R n (e.state n)) (e.state n)) W) →
    ∀ n, c.state n = e.state n
end CartanSuppliedReachableChain
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedReachableChain.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedReachableChain.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All five targets compile for the displayed state-dependent policies, with data stored only at reached states. Otherwise record the exact dependent-recursion or cross-policy equality goal. Do not claim mesh, overlap, restricted-atlas, or recognition acceptance from this chain file.

```lean
end Poincare
```

## Consumer field audit and reuse boundary

The following inventory comes from the actual `d.*` uses and called declarations in S5/S7/S8/S9, not just from the structure's name.

| Original requirement | Retention in tasks 6–7 | Consumer and treatment |
| --- | --- | --- |
| `v` | Stored; `vector_eq` identifies it with the actual supplied normal evaluator. | S7 tests `‖d.v‖ < rho` and the zero case. S8 uses the vector to enter `CoordinateControlledCommonSource`. Old numeric `rho` transfers only in the generic instance, where both adapters preserve `v`. |
| `A,B` | Stored continuous linear equivalences. | S5 uses these in the derivative/pullback construction behind `d.alignment`; their role is retained even where a downstream proof only calls `hasFDerivAt_reanchoredChartMap`. |
| `source_vector_mem`, `target_vector_mem` | Stored for the supplied coordinate endpoints. | S8 uses the source partial inverse law to recover `d.v`; S5 uses both in predecessor-source membership. The new explicit `source_mem` also retains the actual intrinsic composite domain. |
| `source_mem_oldChart`, `target_mem_oldChart` | Stored in the explicit source/target **host** charts. | S7's chart-transition proof reads both. For patch data these are fixed-chart memberships; a generalized proof must change the coordinate centers, not ask for uncontrolled moving preferred-chart source balls. |
| `source_coordinate`, `target_coordinate` | Stored with `sourceExp`, `targetExp`, `linear`. | S7 identifies the reanchored coordinate point and transported target point from these fields. S8 uses `source_coordinate` with `source_vector_mem` for the normal inverse. |
| `source_exp_derivative`, `target_exp_derivative`, `cartan_chart_derivative` | All three strict derivative fields retained. | S5 derives the actual reanchored derivative through transitions. Task 7 must prove the analogous construction for the new hosts. |
| `metric_pullback` | Stored as equality of host-chart metrics under `chartDifferential`. | S5/S6 use it to construct the metric-preserving alignment; no weakening to invertibility alone is permitted. |
| `alignment`, `hasFDerivAt_reanchoredChartMap` | Explicit fields, required to be constructible from the preceding coordinate witnesses. | S7 consumes this derivative for the initial velocity of the transported ODE. Task 7 re-proves the constructor; differential uniqueness gives its independence. |
| `successor`, `successor_anchor`, `successor_target`, `anchor_mem_predecessor_source`, `successor_eq` | Definition plus `successor_fields` and `successor_eq` targets. | S8's ladder/endpoint arguments and S9's reached-chain construction use these consequences. `successor_fields` is a conjunction replacing the three separate projection lemmas, with no information dropped. |

S9 contains no direct `d.v/A/B` projection in its whole-cell theorem; it uses `Chain.ReachableChain` and its state/anchor consequences. Those are retained by task 10. The geometric certificate in S9 still has the old data/equality types; it is not an instance of the new chain theorem until later certificate/mesh ports are proved.

| Consumer theorem | Reusable instance | Work still required |
| --- | --- | --- |
| S7.`exists_uniform_local_eqOn_differentialSuccessor_all` | Task 7.`generic_interval_equality`, through `generic_map_eq`, `toGeneric`, vector preservation, and shrinking to both old and new sources. | For patch data, S4 and task 7 give only fixed-anchor comparisons. `local_equality_transfer` requires predecessor agreement near the actual `z`. H2's uniform `ε` must be proved anew. |
| S5.`Data.successor_eq_of_eqOn_open`, S8.`crossHistorySuccessorAgreement_of_eqOn_open` | Old theorems remain valid for the generic interpretation after data/state adapters. | Re-prove the interpretation-polymorphic derivative congruence once in task 7; S8's theorem is not polymorphic in the supplied `Data`. |
| S8.`reachableChains_ladder_invariant`, `reachableChains_endpoint_eq` | Generic-chain instances can use the old route after a chain adapter. | Their general supplied versions, controlled-source arguments, and cross-patch continuation require ports. Task 10 supplies the basic recursion and policy comparison only. |
| S9.`exists_genericRootedRealization_with_wholeCellMesh_of_certificate` | Keep using it unchanged for its existing generic certificate. | Reuse its subdivision/strictification proof after defining a supplied joint certificate. There is no direct type-level substitution by task 10; compact-cover uniformity and target-patch selection remain obligations. |
| S9.`restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry` and S13.`globalLocalDevelopment_of_restrictedCompatibleCartanAtlas` | Their old generic input structures remain valid. | Later supply the restricted compatible germs with domain inclusions. The diagonal local-homeomorphism proof is topological, but its current geometric input structure still needs an adapter. |

## Reproduce the type checks

Only declaration bodies for the proposed definitions/structures and proposition bodies for target signatures were elaborated. No target theorem proof was attempted. The first probe reported a missing classical decision for patch membership; the second/third reported a missing `T2Space M` for task 7's curvature statement. The final contract makes both explicit and exits 0 with no output. Logs are retained in `/tmp/parametrization-plan-2-evidence/contracts-{01,02,03,04}.log`; `contracts.lean` contains the combined contracts. The final 22-signature extraction is `/tmp/parametrization-plan-2-report-probe.lean`, with successful output recorded in `report-probe-final.log` in the same evidence directory. A separate 26-declaration `#check` probe, `declarations.lean`, also exited 0; its output is in `declarations.log`.

The following command regenerates a probe from the delivered report itself, so the checked statements do not depend on an uncommitted scratch artifact. The only Lean fenced blocks in this report are the shared preamble, the five contract blocks, and the closing namespace.

```sh
python3 - <<'PYPROBE'
from pathlib import Path
import re
report = Path('harness/reports/parametrization-plan-2.md').read_text()
code = '\n\n'.join(re.findall(r'```lean\n(.*?)\n```', report, re.S))
code = re.sub(r'(?m)^theorem (\w+) :', r'def \1_spec : Prop :=', code)
Path('/tmp/parametrization-plan-2-report-probe.lean').write_text(code)
PYPROBE
LEAN_NUM_THREADS=1 lake env lean /tmp/parametrization-plan-2-report-probe.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' /tmp/parametrization-plan-2-report-probe.lean
git diff --check
```

Report extraction/type check: exit 0, no output. Prohibited-token scan of the extracted Lean: no matches. Diff whitespace check: exit 0. The final diff contains only `harness/reports/parametrization-plan-2.md`; no `.lean` file, root import, or handoff file changed. Full project builds and integration audits were not run for this report-only task.

Exact first orchestrator action: regenerate and run the report probe above at `64f6fc2d1d0ee5bfa140f2d9a4cc71f8efadb807`, then freeze task 6. Type-checking these statements establishes well-formed interfaces only. It does not establish their inhabitance, H1/H2, or Poincaré completion.
