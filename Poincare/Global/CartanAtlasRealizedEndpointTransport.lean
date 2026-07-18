import Poincare.Global.DifferentialSuccessorAdaptiveFeedbackIteration
import Poincare.Global.CartanChainRigidity
import Poincare.Global.RoundSphereSimpleConnected
import Poincare.Global.EinsteinNormalization
import Poincare.Global.PinchedLimitInterface

/-!
# Compatible Cartan atlases from realized endpoint transport

The compatible-atlas conclusion asks only that two anchored Cartan maps have
the same value at every point of their strict common source.  Consequently,
the final globalization step does not need a full rigid re-anchor on either
overlap, or even a local equality neighborhood.

For two finite realized differential continuations from a common root, append
the same overlap point.  Equality of the two reached terminal states identifies
their target fields, which are definitionally the two carried Cartan-map
values at that overlap point.  This file packages the actual finite chains and
their terminal equality as data, not as an opaque overlap-compatibility
proposition, and constructs the compatible Cartan atlas directly.

The strict-factor radius certificates developed upstream are designed to
produce precisely the `terminal_eq` field below once their two displayed
closeness conditions are verified.  Uniform adaptive closure is therefore
isolated to the construction of these finite witnesses; no additional
Cartan-overlap or chain-rigidity hypothesis remains downstream.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanAtlasRealizedEndpointTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

/-- Two finite realized continuations from a common root, whose predecessor
states are prescribed and whose next nodes are the same point, reach the same
terminal state.  Every field is concrete data that a finite refinement or
homotopy-grid transport theorem can construct. -/
structure CommonRootTerminalTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (left right : CartanChain.ChainState g) (z : M) where
  root : CartanChain.ChainState g
  leftNodes : ℕ → M
  rightNodes : ℕ → M
  leftChain : ReachableChain leftNodes root
  rightChain : ReachableChain rightNodes root
  leftIndex : ℕ
  rightIndex : ℕ
  left_predecessor : leftChain.state leftIndex = left
  right_predecessor : rightChain.state rightIndex = right
  left_next_node : leftNodes (leftIndex + 1) = z
  right_next_node : rightNodes (rightIndex + 1) = z
  terminal_eq :
    leftChain.state (leftIndex + 1) = rightChain.state (rightIndex + 1)

/-- An explicit strict finite refinement joining two prescribed predecessor
states at a common terminal node.

This structure records the factor map, both realized chains, every intermediate
single-insertion chain, and the equality transported across each finite factor
gap.  It deliberately does not store the final terminal equality: that
equality is derived below by the strict-factor concatenation theorem.  Thus
this is the field-level globalization datum produced when the adaptive radius
conditions have actually succeeded, rather than a renamed atlas-compatibility
proposition. -/
structure CommonRootStrictFactorTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (left right : CartanChain.ChainState g) (z : M) where
  root : CartanChain.ChainState g
  seed : ℕ → M
  refined : ℕ → M
  length : ℕ
  length_pos : 0 < length
  factor : ℕ → ℕ
  factor_zero : factor 0 = 0
  factor_strict : ∀ n < length, factor n < factor (n + 1)
  factor_value : ∀ n ≤ length, refined (factor n) = seed n
  coarseChain : ReachableChain seed root
  refinedChain : ReachableChain refined root
  insertionChain : ∀ n i : ℕ,
    ReachableChain
      (insertNodeListSchedule
        (factorRefinementStage seed refined factor n) (factor n)
        (factorGapNodes refined factor n) i) root
  gap_terminal_eq : ∀ n < length,
    (insertionChain n 0).state (length + (factor n - n)) =
      (insertionChain n (factorGapNodes refined factor n).length).state
        (length + (factor n - n) +
          (factorGapNodes refined factor n).length)
  left_predecessor : coarseChain.state (length - 1) = left
  right_predecessor : refinedChain.state (factor length - 1) = right
  left_terminal_node : seed length = z

/-- Concatenating all validated strict-factor gaps constructs the concrete
common-root terminal transport consumed by Cartan atlas compatibility. -/
def CommonRootStrictFactorTransport.toTerminalTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (left right : CartanChain.ChainState g) (z : M)
    (transport : CommonRootStrictFactorTransport left right z) :
    CommonRootTerminalTransport left right z := by
  have hfactor_le : transport.length ≤ transport.factor transport.length :=
    strictFactorIndex_le transport.factor transport.length
      transport.factor_zero transport.factor_strict transport.length le_rfl
  have hfactor_pos : 0 < transport.factor transport.length :=
    transport.length_pos.trans_le hfactor_le
  have hleftIndex : transport.length - 1 + 1 = transport.length := by
    exact Nat.sub_add_cancel transport.length_pos
  have hrightIndex :
      transport.factor transport.length - 1 + 1 =
        transport.factor transport.length := by
    exact Nat.sub_add_cancel hfactor_pos
  refine
    { root := transport.root
      leftNodes := transport.seed
      rightNodes := transport.refined
      leftChain := transport.coarseChain
      rightChain := transport.refinedChain
      leftIndex := transport.length - 1
      rightIndex := transport.factor transport.length - 1
      left_predecessor := transport.left_predecessor
      right_predecessor := transport.right_predecessor
      left_next_node := ?_
      right_next_node := ?_
      terminal_eq := ?_ }
  · rw [hleftIndex]
    exact transport.left_terminal_node
  · rw [hrightIndex]
    exact
      (transport.factor_value transport.length le_rfl).trans
        transport.left_terminal_node
  · rw [hleftIndex, hrightIndex]
    exact
      DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.state_eq_of_strict_factor_of_gap_terminal_eq
        transport.seed transport.refined transport.length transport.factor
        transport.factor_zero transport.factor_strict transport.factor_value
        transport.coarseChain transport.refinedChain transport.insertionChain
        transport.gap_terminal_eq

omit [T2Space M] in
/-- Equal reached terminal states identify the two predecessor Cartan-map
values at their common next node. -/
theorem germ_value_eq_of_commonRootTerminalTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (left right : CartanChain.ChainState g) (z : M)
    (transport : CommonRootTerminalTransport left right z) :
    left.germ z = right.germ z := by
  have htarget := congrArg CartanChain.ChainState.target transport.terminal_eq
  rw [transport.leftChain.state_succ, transport.rightChain.state_succ] at htarget
  change
    (transport.leftChain.state transport.leftIndex).map
        (transport.leftNodes (transport.leftIndex + 1)) =
      (transport.rightChain.state transport.rightIndex).map
        (transport.rightNodes (transport.rightIndex + 1)) at htarget
  rw [transport.left_predecessor, transport.right_predecessor,
    transport.left_next_node, transport.right_next_node] at htarget
  simpa [CartanChain.ChainState.germ, CartanChain.ChainState.map] using htarget

/-- The strict-factor datum therefore identifies the two carried Cartan-map
values at its common terminal node. -/
theorem germ_value_eq_of_commonRootStrictFactorTransport
    {g : ClosedSmoothRiemannianMetric 3 M}
    (left right : CartanChain.ChainState g) (z : M)
    (transport : CommonRootStrictFactorTransport left right z) :
    left.germ z = right.germ z :=
  germ_value_eq_of_commonRootTerminalTransport left right z
    transport.toTerminalTransport

/-- Explicit realized-history data for an all-anchor Cartan family.

For every overlap point, `transport` gives two actual finite differential
chains from a common root.  Their last predecessor states are the selected
anchored states and their common next node is the overlap point.  The terminal
state equality is the exact field supplied by successful adaptive
strict-factor transport. -/
structure RealizedEndpointTransportAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  target : M → RoundSphere3
  alignment : ∀ x : M, CartanMap.TangentAlignment g x (target x)
  transport : ∀ x y z : M,
    z ∈
        (CartanLocalRigidity.anchoredFamilyState
          g target alignment x).germ.source ∩
        (CartanLocalRigidity.anchoredFamilyState
          g target alignment y).germ.source →
      CommonRootTerminalTransport
        (CartanLocalRigidity.anchoredFamilyState g target alignment x)
        (CartanLocalRigidity.anchoredFamilyState g target alignment y) z

/-- The stronger atlas datum produced directly by successful strict-factor
refinement.  Every overlap point carries the complete finite factor schedule
and its validated gap transports; terminal-state equality is not a field. -/
structure StrictFactorEndpointTransportAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  target : M → RoundSphere3
  alignment : ∀ x : M, CartanMap.TangentAlignment g x (target x)
  transport : ∀ x y z : M,
    z ∈
        (CartanLocalRigidity.anchoredFamilyState
          g target alignment x).germ.source ∩
        (CartanLocalRigidity.anchoredFamilyState
          g target alignment y).germ.source →
      CommonRootStrictFactorTransport
        (CartanLocalRigidity.anchoredFamilyState g target alignment x)
        (CartanLocalRigidity.anchoredFamilyState g target alignment y) z

/-- Forget only the internal strict-factor schedule after deriving its terminal
equality by finite insertion concatenation. -/
def StrictFactorEndpointTransportAtlasData.toRealized
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : StrictFactorEndpointTransportAtlasData g) :
    RealizedEndpointTransportAtlasData g where
  target := data.target
  alignment := data.alignment
  transport := fun x y z hz ↦
    (data.transport x y z hz).toTerminalTransport

omit [T2Space M] in
/-- Realized endpoint transport gives pairwise agreement of the selected
anchored Cartan germs, with no component-seed, local-rigidity, chosen-reanchor,
or full-overlap chain hypothesis. -/
theorem RealizedEndpointTransportAtlasData.pairwise_eqOn
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : RealizedEndpointTransportAtlasData g) :
    ∀ x y : M,
      EqOn
        (CartanMap.openPartialHomeomorph
          g x (data.target x) (data.alignment x))
        (CartanMap.openPartialHomeomorph
          g y (data.target y) (data.alignment y))
        ((CartanMap.openPartialHomeomorph
            g x (data.target x) (data.alignment x)).source ∩
          (CartanMap.openPartialHomeomorph
            g y (data.target y) (data.alignment y)).source) := by
  intro x y z hz
  let left := CartanLocalRigidity.anchoredFamilyState
    g data.target data.alignment x
  let right := CartanLocalRigidity.anchoredFamilyState
    g data.target data.alignment y
  have hz' : z ∈ left.germ.source ∩ right.germ.source := by
    simpa [left, right] using hz
  have hvalue := germ_value_eq_of_commonRootTerminalTransport
    left right z (data.transport x y z hz')
  simpa [left, right] using hvalue

/-- Pointwise equality of the two chosen successor states already is the
complete monodromy input required by the compatible-atlas conclusion.

Unlike the older consumer in `CartanChainRigidity`, this theorem does not
retain component seeds, local equality neighborhoods, or chosen re-anchor
rigidity: equality of successor targets is definitionally equality of the two
carried Cartan-map values at the overlap point. -/
theorem compatibleCartanAtlas_of_nextMonodromy
    (h : ∀ g : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g 1 →
        ∃ (p : M → RoundSphere3)
          (L : ∀ x : M, CartanMap.TangentAlignment g x (p x)),
            ∀ x y z : M,
              z ∈ (CartanLocalRigidity.anchoredFamilyState g p L x).germ.source ∩
                  (CartanLocalRigidity.anchoredFamilyState g p L y).germ.source →
                (CartanLocalRigidity.anchoredFamilyState g p L x).next z =
                  (CartanLocalRigidity.anchoredFamilyState g p L y).next z) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  intro g hcurv
  rcases h g hcurv with ⟨p, L, hmonodromy⟩
  refine ⟨p, L, ?_⟩
  intro x y z hz
  exact CartanChainRigidity.germ_value_eq_of_next_eq
    (CartanLocalRigidity.anchoredFamilyState g p L x)
    (CartanLocalRigidity.anchoredFamilyState g p L y) z
    (hmonodromy x y z hz)

/-- A concrete realized endpoint-transport constructor for every unit
constant-curvature metric supplies the repository's compatible Cartan atlas
payload. -/
theorem compatibleCartanAtlas_of_realizedEndpointTransport
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 → RealizedEndpointTransportAtlasData g) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) := by
  intro g hcurv
  let data := transport g hcurv
  exact ⟨data.target, data.alignment, data.pairwise_eqOn⟩

/-- Successful strict finite factor transport on every overlap constructs the
compatible Cartan atlas directly.  The final equality is derived from the
recorded gap transports, not assumed in this theorem's input structure. -/
theorem compatibleCartanAtlas_of_strictFactorEndpointTransport
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        StrictFactorEndpointTransportAtlasData g) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  compatibleCartanAtlas_of_realizedEndpointTransport
    (fun g hcurv ↦ (transport g hcurv).toRealized)

/-- Per-manifold unit-curvature sphere recognition from explicit finite
endpoint transport. -/
theorem unitConstantCurvatureSphereRecognition3_of_realizedEndpointTransport
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 → RealizedEndpointTransportAtlasData g) :
    UnitConstantCurvatureSphereRecognition3 M :=
  RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    (compatibleCartanAtlas_of_realizedEndpointTransport transport)

/-- Unit-curvature sphere recognition from successful strict finite factor
transport on every overlap. -/
theorem unitConstantCurvatureSphereRecognition3_of_strictFactorEndpointTransport
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        StrictFactorEndpointTransportAtlasData g) :
    UnitConstantCurvatureSphereRecognition3 M :=
  RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    (compatibleCartanAtlas_of_strictFactorEndpointTransport transport)

/-- The positive-Einstein core and explicit finite endpoint transport give the
sphere conclusion on the current manifold. -/
theorem sphereConclusion_of_positiveEinstein_of_realizedEndpointTransport
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hEinstein : PositiveEinsteinMetric3 M)
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 → RealizedEndpointTransportAtlasData g) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  sphereConclusion_of_positiveEinstein_of_unitRecognition hEinstein
    (unitConstantCurvatureSphereRecognition3_of_realizedEndpointTransport
      transport)

/-- The positive-Einstein core and successful strict finite factor endpoint
transport give the sphere conclusion on the current manifold. -/
theorem sphereConclusion_of_positiveEinstein_of_strictFactorEndpointTransport
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (hEinstein : PositiveEinsteinMetric3 M)
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        StrictFactorEndpointTransportAtlasData g) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  sphereConclusion_of_positiveEinstein_of_unitRecognition hEinstein
    (unitConstantCurvatureSphereRecognition3_of_strictFactorEndpointTransport
      transport)

/-- Universal reduced Hamilton convergence plus explicit realized endpoint
transport closes the smooth-manifold Poincare statement.  The former supplies
the positive-Einstein/space-form core; the latter constructs the compatible
Cartan atlas instead of assuming it as a packaged proposition. -/
theorem poincareConjecture_of_hamiltonConvergenceCore_of_realizedEndpointTransport
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (transport :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N]
        (g : ClosedSmoothRiemannianMetric 3 N),
          HasConstantSectionalCurvature3 g 1 →
            RealizedEndpointTransportAtlasData g) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition
    hHamilton
    (fun N _ _ _ _ _ _ _ _ ↦
      unitConstantCurvatureSphereRecognition3_of_realizedEndpointTransport
        (transport N))

/-- Universal reduced Hamilton convergence plus successful strict finite
factor endpoint transport closes the smooth-manifold Poincare statement. -/
theorem poincareConjecture_of_hamiltonConvergenceCore_of_strictFactorEndpointTransport
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (transport :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N]
        (g : ClosedSmoothRiemannianMetric 3 N),
          HasConstantSectionalCurvature3 g 1 →
            StrictFactorEndpointTransportAtlasData g) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition
    hHamilton
    (fun N _ _ _ _ _ _ _ _ ↦
      unitConstantCurvatureSphereRecognition3_of_strictFactorEndpointTransport
        (transport N))

end CartanAtlasRealizedEndpointTransport
end Poincare
