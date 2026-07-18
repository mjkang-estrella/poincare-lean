import Poincare.Global.CartanAtlasRealizedEndpointTransport

/-!
# Cartan atlases from rooted reachable endpoint families

This module replaces the diagnostically useful but geometrically invalid
constant-target specialization with actual path continuation.  A single root
Cartan state is fixed.  For every point `x`, the data retain a path from the
root anchor to `x`, sampled nodes on that path, a realized `ReachableChain`,
and a terminal index whose sample time is `1`.

The target at `x` is the target carried by the reached terminal state.  Its
tangent alignment is the terminal alignment transported across the proved
equality between the terminal state's anchor and `x`; no independent target
or alignment is chosen.  On overlaps, the stronger atlas record retains an
actual strict-factor transport and proves that its common root is the same
fixed root.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare

set_option linter.unusedSectionVars false
namespace CartanAtlasRootedReachableEndpointTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRealizedEndpointTransport
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorReachableChainRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

/-- A genuinely rooted endpoint family obtained by realized continuation
along one chosen path to each source point. -/
structure RootedPathContinuedEndpointFamily
    (g : ClosedSmoothRiemannianMetric 3 M) where
  root : CartanChain.ChainState g
  path : ∀ x : M, Path root.anchor x
  nodeTime : M → ℕ → unitInterval
  nodeTime_zero : ∀ x : M, nodeTime x 0 = 0
  terminalIndex : M → ℕ
  nodeTime_terminal : ∀ x : M, nodeTime x (terminalIndex x) = 1
  chain : ∀ x : M,
    ReachableChain (fun n ↦ path x (nodeTime x n)) root

namespace RootedPathContinuedEndpointFamily

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The sampled node sequence of the chosen root-to-`x` path. -/
def nodes (data : RootedPathContinuedEndpointFamily g) (x : M) : ℕ → M :=
  fun n ↦ data.path x (data.nodeTime x n)

/-- The actual state reached at the retained terminal chain index. -/
def terminalState
    (data : RootedPathContinuedEndpointFamily g) (x : M) :
    CartanChain.ChainState g :=
  (data.chain x).state (data.terminalIndex x)

/-- The terminal state is genuinely anchored at the endpoint `x` of its
chosen path.  This equality is derived from `ReachableChain`, rather than
postulated as an unrelated cast certificate. -/
theorem terminalState_anchor
    (data : RootedPathContinuedEndpointFamily g) (x : M) :
    (data.terminalState x).anchor = x := by
  have hroot : data.root.anchor = data.nodes x 0 := by
    simp [nodes, data.nodeTime_zero x]
  have hstateNode :=
    (data.chain x).state_anchor_eq_node hroot (data.terminalIndex x)
  have hterminalNode : data.nodes x (data.terminalIndex x) = x := by
    simp [nodes, data.nodeTime_terminal x]
  exact hstateNode.trans hterminalNode

/-- The endpoint target is the target carried by the reached chain state. -/
def target (data : RootedPathContinuedEndpointFamily g) (x : M) : RoundSphere3 :=
  (data.terminalState x).target

/-- The endpoint alignment is the reached terminal alignment, transported
only along the derived terminal-anchor equality. -/
def alignment (data : RootedPathContinuedEndpointFamily g) (x : M) :
    CartanMap.TangentAlignment g x (data.target x) :=
  cast
    (congrArg
      (fun anchor : M ↦ CartanMap.TangentAlignment g anchor (data.target x))
      (data.terminalState_anchor x))
    (show CartanMap.TangentAlignment g (data.terminalState x).anchor
        (data.target x) from
      (data.terminalState x).alignment)

/-- Rebuilding an anchored family state from the derived endpoint target and
alignment recovers the actual reached terminal state.  The only dependent
cast is the terminal-anchor equality displayed above. -/
theorem anchoredFamilyState_eq_terminalState
    (data : RootedPathContinuedEndpointFamily g) (x : M) :
    CartanLocalRigidity.anchoredFamilyState g data.target data.alignment x =
      data.terminalState x := by
  change
    CartanChain.ChainState.mk x (data.target x) (data.alignment x) =
      CartanChain.ChainState.mk (data.terminalState x).anchor
        (data.terminalState x).target (data.terminalState x).alignment
  rw [CartanChain.ChainState.mk.injEq]
  refine ⟨(data.terminalState_anchor x).symm, rfl, ?_⟩
  unfold alignment
  exact cast_heq _ _

end RootedPathContinuedEndpointFamily

/-- A strict-factor overlap transport whose internal realized chains start at
the fixed root of the endpoint family. -/
structure FixedRootStrictFactorTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (root left right : CartanChain.ChainState g) (z : M) where
  strictFactor : CommonRootStrictFactorTransport left right z
  root_eq : strictFactor.root = root

/-- The combinatorial and realized-chain part of a strict common refinement
between two members of one rooted endpoint family.

The two prefix fields identify the prescribed predecessor states by the
existing prefix-canonicity theorem, rather than storing those state equalities
again.  The only transport field deliberately omitted is equality across each
actual finite insertion block; `RootedOverlapGapTerminalTransport` below names
that remaining boundary exactly. -/
structure RootedOverlapStrictFactorSchedule
    {g : ClosedSmoothRiemannianMetric 3 M}
    (endpoint : RootedPathContinuedEndpointFamily g)
    (x y z : M) where
  seed : ℕ → M
  refined : ℕ → M
  length : ℕ
  length_pos : 0 < length
  factor : ℕ → ℕ
  factor_zero : factor 0 = 0
  factor_strict : ∀ n < length, factor n < factor (n + 1)
  factor_value : ∀ n ≤ length, refined (factor n) = seed n
  coarseChain : ReachableChain seed endpoint.root
  refinedChain : ReachableChain refined endpoint.root
  insertionChain : ∀ n i : ℕ,
    ReachableChain
      (insertNodeListSchedule
        (factorRefinementStage seed refined factor n) (factor n)
        (factorGapNodes refined factor n) i) endpoint.root
  left_index : length - 1 = endpoint.terminalIndex x
  right_index : factor length - 1 = endpoint.terminalIndex y
  left_prefix : ∀ j < length - 1,
    seed (j + 1) = endpoint.nodes x (j + 1)
  right_prefix : ∀ j < factor length - 1,
    refined (j + 1) = endpoint.nodes y (j + 1)
  left_terminal_node : seed length = z

namespace RootedOverlapStrictFactorSchedule

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M}

/-- Prefix canonicity identifies the coarse predecessor with the actual
terminal state of the first rooted path. -/
theorem left_predecessor
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z) :
    schedule.coarseChain.state (schedule.length - 1) =
      endpoint.terminalState x := by
  have hprefix :=
    ReachableChain.state_eq_of_prefix_nodes
      schedule.coarseChain (endpoint.chain x) (schedule.length - 1) (by
        intro j hj
        simpa [RootedPathContinuedEndpointFamily.nodes] using
          schedule.left_prefix j hj)
  simpa [RootedPathContinuedEndpointFamily.terminalState,
    schedule.left_index] using hprefix

/-- Prefix canonicity identifies the refined predecessor with the actual
terminal state of the second rooted path. -/
theorem right_predecessor
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z) :
    schedule.refinedChain.state (schedule.factor schedule.length - 1) =
      endpoint.terminalState y := by
  have hprefix :=
    ReachableChain.state_eq_of_prefix_nodes
      schedule.refinedChain (endpoint.chain y)
        (schedule.factor schedule.length - 1) (by
          intro j hj
          simpa [RootedPathContinuedEndpointFamily.nodes] using
            schedule.right_prefix j hj)
  simpa [RootedPathContinuedEndpointFamily.terminalState,
    schedule.right_index] using hprefix

/-- The exact residual transport premise for a realized strict-refinement
schedule: every concrete factor-gap insertion block reaches the same terminal
state after the corresponding index shift. -/
def RootedOverlapGapTerminalTransport
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z) : Prop :=
  ∀ n < schedule.length,
    (schedule.insertionChain n 0).state
        (schedule.length + (schedule.factor n - n)) =
      (schedule.insertionChain n
          (factorGapNodes schedule.refined schedule.factor n).length).state
        (schedule.length + (schedule.factor n - n) +
          (factorGapNodes schedule.refined schedule.factor n).length)

/-- Once each realized factor gap has been transported, the rooted schedule is
the fixed-root strict-factor witness required by the atlas consumer. -/
def toFixedRootStrictFactorTransport
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hgap : RootedOverlapGapTerminalTransport schedule) :
    FixedRootStrictFactorTransport endpoint.root
      (endpoint.terminalState x) (endpoint.terminalState y) z where
  strictFactor :=
    { root := endpoint.root
      seed := schedule.seed
      refined := schedule.refined
      length := schedule.length
      length_pos := schedule.length_pos
      factor := schedule.factor
      factor_zero := schedule.factor_zero
      factor_strict := schedule.factor_strict
      factor_value := schedule.factor_value
      coarseChain := schedule.coarseChain
      refinedChain := schedule.refinedChain
      insertionChain := schedule.insertionChain
      gap_terminal_eq := hgap
      left_predecessor := schedule.left_predecessor
      right_predecessor := schedule.right_predecessor
      left_terminal_node := schedule.left_terminal_node }
  root_eq := rfl

/-- Local equality patches attached to the actual predecessor and successor
histories of every single insertion in a rooted strict-refinement schedule.
This is a geometric sufficient premise for the residual gap transport, not an
endpoint-compatibility premise. -/
structure OpenPatchData
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z) where
  patch : ℕ → ℕ → Set M
  isOpen : ∀ n < schedule.length,
    ∀ i < (factorGapNodes schedule.refined schedule.factor n).length,
      IsOpen (patch n i)
  insertedNode_mem : ∀ n < schedule.length,
    ∀ i < (factorGapNodes schedule.refined schedule.factor n).length,
      insertNodeListSchedule
          (factorRefinementStage schedule.seed schedule.refined
            schedule.factor n)
          (schedule.factor n)
          (factorGapNodes schedule.refined schedule.factor n) i
          (schedule.factor n + i + 1) ∈ patch n i
  eqOn : ∀ n < schedule.length,
    ∀ i < (factorGapNodes schedule.refined schedule.factor n).length,
      EqOn
        ((schedule.insertionChain n i).state
          (schedule.factor n + i)).germ
        ((schedule.insertionChain n (i + 1)).state
          (schedule.factor n + i + 1)).germ
        (patch n i)

/-- The finite-insertion theorem turns local patches on realized histories
into exactly the gap terminal equalities required by strict-factor
concatenation. -/
theorem gapTerminalTransport_of_openPatchData
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (patches : OpenPatchData schedule) :
    RootedOverlapGapTerminalTransport schedule := by
  intro n hn
  have hfactorIndex : n ≤ schedule.factor n :=
    strictFactorIndex_le schedule.factor schedule.length
      schedule.factor_zero schedule.factor_strict n (Nat.le_of_lt hn)
  have hterminal :
      schedule.factor n + 1 ≤
        schedule.length + (schedule.factor n - n) := by
    omega
  apply ReachableChain.state_eq_after_insertNodeList_of_eqOn_open
    (coarse := factorRefinementStage schedule.seed schedule.refined
      schedule.factor n)
    (p := schedule.factor n)
    (zs := factorGapNodes schedule.refined schedule.factor n)
    (chain := schedule.insertionChain n)
    (L := schedule.length + (schedule.factor n - n))
    hterminal (U := patches.patch n)
  · intro i hi
    exact patches.isOpen n hn i hi
  · intro i hi
    exact patches.insertedNode_mem n hn i hi
  · intro i hi
    exact patches.eqOn n hn i hi

/-- A rooted strict-refinement schedule with realized local patches directly
constructs the required fixed-root overlap transport. -/
def toFixedRootStrictFactorTransport_of_openPatchData
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (patches : OpenPatchData schedule) :
    FixedRootStrictFactorTransport endpoint.root
      (endpoint.terminalState x) (endpoint.terminalState y) z :=
  schedule.toFixedRootStrictFactorTransport
    (gapTerminalTransport_of_openPatchData schedule patches)

/-- Constant curvature automatically equips the realized schedule with the
existing two-stage adaptive radius certificate.  Turning this conditional
certificate into `RootedOverlapGapTerminalTransport` still requires the
displayed inserted-node and old-next-node closeness tests to hold; the current
repository does not derive those tests from arbitrary independently selected
rooted paths. -/
theorem strictFactorRadiusCertificate_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    DifferentialSuccessorStrictFactorCurvatureTransport.StrictFactorRadiusCertificate
      schedule.seed schedule.refined endpoint.root schedule.length
        schedule.factor schedule.coarseChain schedule.refinedChain
          schedule.insertionChain := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.strictFactorRadiusCertificate_of_curvature
      hcurv schedule.seed schedule.refined schedule.length schedule.factor
        schedule.factor_zero schedule.factor_strict schedule.factor_value
        schedule.coarseChain schedule.refinedChain schedule.insertionChain

end RootedOverlapStrictFactorSchedule

/-- Rooted endpoint paths together with one strict common-refinement schedule
and its exact gap-transport premise on every overlap. -/
structure RootedPathStrictFactorScheduleAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  endpoint : RootedPathContinuedEndpointFamily g
  schedule : ∀ x y z : M,
    z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source →
      RootedOverlapStrictFactorSchedule endpoint x y z
  gapTransport : ∀ x y z : M,
    ∀ hz : z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source,
      RootedOverlapStrictFactorSchedule.RootedOverlapGapTerminalTransport
        (schedule x y z hz)

/-- Atlas-level rooted strict refinements whose residual transport is supplied
by local equality patches on the actual insertion histories. -/
structure RootedPathStrictFactorOpenPatchAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  endpoint : RootedPathContinuedEndpointFamily g
  schedule : ∀ x y z : M,
    z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source →
      RootedOverlapStrictFactorSchedule endpoint x y z
  patches : ∀ x y z : M,
    ∀ hz : z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source,
      RootedOverlapStrictFactorSchedule.OpenPatchData
        (schedule x y z hz)

/-- Realized local insertion patches discharge every residual factor-gap
transport in the corresponding rooted schedule atlas. -/
def RootedPathStrictFactorOpenPatchAtlasData.toScheduleAtlas
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : RootedPathStrictFactorOpenPatchAtlasData g) :
    RootedPathStrictFactorScheduleAtlasData g where
  endpoint := data.endpoint
  schedule := data.schedule
  gapTransport := fun x y z hz ↦
    RootedOverlapStrictFactorSchedule.gapTerminalTransport_of_openPatchData
      (data.schedule x y z hz) (data.patches x y z hz)

/-- Rooted path-continuation data together with genuine strict-factor
path-independence transport on every overlap of the reached endpoint germs. -/
structure RootedPathStrictFactorEndpointTransportAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  endpoint : RootedPathContinuedEndpointFamily g
  transport : ∀ x y z : M,
    z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source →
      FixedRootStrictFactorTransport endpoint.root
        (endpoint.terminalState x) (endpoint.terminalState y) z

/-- Discharge the atlas overlap provider from the explicit rooted schedule
and its per-gap transport. -/
def RootedPathStrictFactorScheduleAtlasData.toEndpointTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : RootedPathStrictFactorScheduleAtlasData g) :
    RootedPathStrictFactorEndpointTransportAtlasData g where
  endpoint := data.endpoint
  transport := fun x y z hz ↦
    (data.schedule x y z hz).toFixedRootStrictFactorTransport
      (data.gapTransport x y z hz)

/-- Atlas-level local insertion patches therefore construct the fixed-root
strict-factor overlap provider consumed downstream. -/
def RootedPathStrictFactorOpenPatchAtlasData.toEndpointTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : RootedPathStrictFactorOpenPatchAtlasData g) :
    RootedPathStrictFactorEndpointTransportAtlasData g :=
  data.toScheduleAtlas.toEndpointTransport

/-- Convert the rooted endpoint family to the existing strict-factor atlas
interface.  The casts from selected anchored states to reached terminal
states are exactly `anchoredFamilyState_eq_terminalState`; the strict-factor
schedule itself is retained unchanged. -/
def RootedPathStrictFactorEndpointTransportAtlasData.toStrictFactor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : RootedPathStrictFactorEndpointTransportAtlasData g) :
    StrictFactorEndpointTransportAtlasData g where
  target := data.endpoint.target
  alignment := data.endpoint.alignment
  transport := by
    intro x y z hz
    have hx := data.endpoint.anchoredFamilyState_eq_terminalState x
    have hy := data.endpoint.anchoredFamilyState_eq_terminalState y
    have hz' :
        z ∈ (data.endpoint.terminalState x).germ.source ∩
          (data.endpoint.terminalState y).germ.source := by
      simpa [hx, hy] using hz
    have strict := (data.transport x y z hz').strictFactor
    simpa [hx, hy] using strict

/-- A rooted path-continued strict-factor provider constructs the compatible
Cartan atlas, with no constant target specialization. -/
theorem compatibleCartanAtlas_of_rootedPathStrictFactorEndpointTransport
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        RootedPathStrictFactorEndpointTransportAtlasData g) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  compatibleCartanAtlas_of_strictFactorEndpointTransport
    (fun g hcurv ↦ (transport g hcurv).toStrictFactor)

/-- Rooted path continuation and strict-factor path independence give unit
constant-curvature sphere recognition on the current manifold. -/
theorem unitConstantCurvatureSphereRecognition3_of_rootedPathStrictFactorEndpointTransport
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        RootedPathStrictFactorEndpointTransportAtlasData g) :
    UnitConstantCurvatureSphereRecognition3 M :=
  unitConstantCurvatureSphereRecognition3_of_strictFactorEndpointTransport
    (fun g hcurv ↦ (transport g hcurv).toStrictFactor)

/-- Universal rooted path-continuation and strict-factor transport data. -/
def UniversalRootedPathStrictFactorEndpointTransportAtlasData :
    Type (u + 1) :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N]
    (g : ClosedSmoothRiemannianMetric 3 N),
      HasConstantSectionalCurvature3 g 1 →
        RootedPathStrictFactorEndpointTransportAtlasData g

/-- The universal rooted provider supplies the unit-recognition interface. -/
theorem universalUnitRecognition_of_rootedPathStrictFactorEndpointTransport
    (transport :
      UniversalRootedPathStrictFactorEndpointTransportAtlasData.{u}) :
    ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (ClosedSmoothModel 3) N]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
      [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
        UnitConstantCurvatureSphereRecognition3 N := by
  intro N _top _t2 _second _charted _manifold _compact _connected _simply
  exact
    unitConstantCurvatureSphereRecognition3_of_rootedPathStrictFactorEndpointTransport
      (fun g hcurv ↦ transport N g hcurv)

/-- Hamilton's positive-Einstein limit together with genuine rooted endpoint
continuation proves the smooth Poincare statement. -/
theorem poincareConjecture_of_hamiltonConvergenceCore_of_rootedPathStrictFactorEndpointTransport
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (transport :
      UniversalRootedPathStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition
    hHamilton
    (universalUnitRecognition_of_rootedPathStrictFactorEndpointTransport
      transport)

end CartanAtlasRootedReachableEndpointTransport
end Poincare
