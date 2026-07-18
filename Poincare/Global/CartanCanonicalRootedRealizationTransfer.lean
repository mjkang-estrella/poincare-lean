import Poincare.Global.CartanCanonicalFamilyGermComparison
import Poincare.Global.CartanAtlasRootedPathSkeleton

/-!
# Transfer of canonical supplied-family rooted realizations

The canonical target-exponential family supplies the joint-anchor regularity
needed to construct rooted chains.  The existing endpoint-transport pipeline,
however, consumes chains for the generic target exponential.

`CartanTargetExponential.Data canonicalFamily` remembers the canonical target
chart derivative at the aligned normal vector, but deliberately forgets the
two facts needed to regard that datum as generic: membership of the aligned
vector in the generic chart source and equality of the two target-chart germs
at that vector.  `GenericChartGermProvenance` is exactly this missing datum.

The chart provenance identifies the two carried values at each step.  To enter
the existing endpoint pipeline one must additionally retain an actual generic
differential datum and the equality of its successor with the forgotten
canonical successor.  `GenericSuccessorComparison` names precisely that
proof-bearing conversion boundary; retaining it stepwise transfers complete
reachable chains and rooted realizations.  No global equality of the
independently constructed target charts or partial homeomorphisms is asserted.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanCanonicalRootedRealizationTransfer

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanCanonicalFamilyGermComparison

/-- Every property of map values that holds eventually at a canonical state's
anchor transfers both ways to the corresponding generic state.  This is the
germ-level consumer used for local metric identities and terminal overlap
facts; it makes no claim outside the anchor neighborhood. -/
theorem eventually_mapPredicate_iff
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g)
    (P : M → RoundSphere3 → Prop) :
    (∀ᶠ z in nhds s.anchor, P z (s.map z)) ↔
      ∀ᶠ z in nhds s.anchor, P z ((canonicalToGenericState s).map z) := by
  constructor
  · intro hP
    filter_upwards [hP, canonicalState_map_eventuallyEq_genericState s] with
      z hz hmap
    rwa [← hmap]
  · intro hP
    filter_upwards [hP, canonicalState_map_eventuallyEq_genericState s] with
      z hz hmap
    rwa [hmap]

/--
The exact target-chart provenance omitted by canonical supplied-family data.

The source-side data are shared definitionally.  On the target side, generic
source membership makes the generic partial exponential meaningful, while
eventual equality transfers both its value and its strict derivative.
-/
structure GenericChartGermProvenance
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : ChainState canonicalFamily g} {x₁ : M}
    (d : Data canonicalFamily s x₁) : Prop where
  target_vector_mem :
    s.alignment d.v ∈ (genericFamily.chart s.target).source
  chart_eventuallyEq :
    (canonicalFamily.chart s.target : E → E) =ᶠ[nhds (s.alignment d.v)]
      (genericFamily.chart s.target : E → E)

namespace GenericChartGermProvenance

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {s : ChainState canonicalFamily g} {x₁ : M}
variable {d : Data canonicalFamily s x₁}

/-- The retained target-chart germ identifies the two carried values at the
new source anchor. -/
theorem map_eq (h : GenericChartGermProvenance d) :
    s.map x₁ = (canonicalToGenericState s).map x₁ := by
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) s.anchor
  have hsourceCoordinate : (chartAt E s.anchor) x₁ = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hnormal : eM.symm ((chartAt E s.anchor) x₁) = d.v := by
    rw [hsourceCoordinate]
    exact eM.left_inv d.source_vector_mem
  have htargetValue :
      canonicalFamily.chart s.target (s.alignment d.v) =
        genericFamily.chart s.target (s.alignment d.v) :=
    h.chart_eventuallyEq.self_of_nhds
  change
    (chartAt E s.target).symm
        (canonicalFamily.chart s.target
          (s.alignment (eM.symm ((chartAt E s.anchor) x₁)))) =
      (chartAt E s.target).symm
        (genericFamily.chart s.target
          (s.alignment (eM.symm ((chartAt E s.anchor) x₁))))
  rw [hnormal, htargetValue]

end GenericChartGermProvenance

/--
The exact proof-bearing comparison needed to turn one canonical supplied step
into a legacy generic differential step.

`chart` retains the target-chart provenance that canonical `Data` forgets.
The generic datum and successor equality are kept explicitly because neither
is a field of canonical `Data`; in particular, no equality of target charts
away from the displayed aligned-vector germ is inferred.
-/
structure GenericSuccessorComparison
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : ChainState canonicalFamily g} {x₁ : M}
    (d : Data canonicalFamily s x₁) where
  chart : GenericChartGermProvenance d
  genericData :
    DifferentialInducedSuccessor.Data (canonicalToGenericState s) x₁
  successor_eq :
    canonicalToGenericState d.successor = genericData.successor

namespace GenericSuccessorComparison

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {s : ChainState canonicalFamily g} {x₁ : M}
variable {d : Data canonicalFamily s x₁}

/-- The generic differential datum has the same predecessor value at the new
anchor as the canonical supplied datum. -/
theorem predecessor_map_eq (h : GenericSuccessorComparison d) :
    s.map x₁ = (canonicalToGenericState s).map x₁ :=
  h.chart.map_eq

end GenericSuccessorComparison

/-- Stepwise generic-successor comparisons for one realized canonical chain. -/
structure ReachableChainComparison
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : ChainState canonicalFamily g}
    (chain : CartanTargetExponential.Chain.ReachableChain
      canonicalFamily nodes initial) where
  step : ∀ n : ℕ, GenericSuccessorComparison (chain.data n)

namespace ReachableChainComparison

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {nodes : ℕ → M} {initial : ChainState canonicalFamily g}
variable {chain : CartanTargetExponential.Chain.ReachableChain
  canonicalFamily nodes initial}

/-- A canonical supplied-family reachable chain with retained step
comparisons is a genuine legacy generic reachable chain on the same nodes. -/
def toGenericReachableChain (h : ReachableChainComparison chain) :
    DifferentialInducedSuccessor.Chain.ReachableChain nodes
      (canonicalToGenericState initial) where
  state := fun n ↦ canonicalToGenericState (chain.state n)
  initial_eq := congrArg canonicalToGenericState chain.initial_eq
  data := fun n ↦ (h.step n).genericData
  successor_eq := by
    intro n
    rw [chain.successor_eq n]
    exact (h.step n).successor_eq

@[simp]
theorem toGenericReachableChain_state
    (h : ReachableChainComparison chain) (n : ℕ) :
    (h.toGenericReachableChain).state n =
      canonicalToGenericState (chain.state n) :=
  rfl

end ReachableChainComparison

open CartanAtlasRootedPathSkeleton

/-- The retained comparison data for every step of every rooted canonical
path realization. -/
structure RootedRealizationComparison
    {g : ClosedSmoothRiemannianMetric 3 M}
    {skeleton : RootedCartanPathSkeleton g}
    (realization :
      SuppliedRootedPathChainRealization canonicalFamily skeleton) where
  chain : ∀ x : M, ReachableChainComparison (realization.chain x)

namespace RootedRealizationComparison

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}
variable {realization :
  SuppliedRootedPathChainRealization canonicalFamily skeleton}

/-- Transfer a complete canonical supplied-family rooted realization to the
generic realization consumed by rooted endpoint transport. -/
def toGenericRootedPathChainRealization
    (h : RootedRealizationComparison realization) :
    RootedPathChainRealization skeleton where
  nodeTime := realization.nodeTime
  nodeTime_zero := realization.nodeTime_zero
  terminalIndex := realization.terminalIndex
  nodeTime_terminal := realization.nodeTime_terminal
  chain := by
    intro x
    simpa [canonicalToGenericState, ChainState.retarget] using
      (h.chain x).toGenericReachableChain

@[simp]
theorem toGenericRootedPathChainRealization_nodeTime
    (h : RootedRealizationComparison realization) (x : M) (n : ℕ) :
    h.toGenericRootedPathChainRealization.nodeTime x n =
      realization.nodeTime x n :=
  rfl

@[simp]
theorem toGenericRootedPathChainRealization_terminalIndex
    (h : RootedRealizationComparison realization) (x : M) :
    h.toGenericRootedPathChainRealization.terminalIndex x =
      realization.terminalIndex x :=
  rfl

/-- Terminal generic states are exactly the forgotten canonical terminal
states, so the transferred realization enters endpoint transport without any
new terminal cast or independently selected alignment. -/
theorem toGenericRootedPathChainRealization_terminalState
    (h : RootedRealizationComparison realization) (x : M) :
    (h.toGenericRootedPathChainRealization.chain x).state
        (realization.terminalIndex x) =
      canonicalToGenericState
        ((realization.chain x).state (realization.terminalIndex x)) :=
  rfl

/-- The transferred rooted realization produces the existing rooted endpoint
family directly. -/
def toGenericEndpointFamily
    (h : RootedRealizationComparison realization) :
    CartanAtlasRootedReachableEndpointTransport.RootedPathContinuedEndpointFamily g :=
  h.toGenericRootedPathChainRealization.toEndpointFamily

/-- The endpoint family's terminal state is the canonical terminal state with
only its family tag forgotten. -/
theorem toGenericEndpointFamily_terminalState
    (h : RootedRealizationComparison realization) (x : M) :
    (h.toGenericEndpointFamily.terminalState x) =
      canonicalToGenericState
        ((realization.chain x).state (realization.terminalIndex x)) :=
  rfl

/-- Canonical and transferred generic terminal maps agree as germs at the
terminal source anchor. -/
theorem canonical_terminalMap_eventuallyEq_genericEndpoint
    (h : RootedRealizationComparison realization) (x : M) :
    ((realization.chain x).state (realization.terminalIndex x)).map =ᶠ[
        nhds
          ((realization.chain x).state
            (realization.terminalIndex x)).anchor]
      (h.toGenericEndpointFamily.terminalState x).map := by
  rw [h.toGenericEndpointFamily_terminalState x]
  exact
    canonicalState_map_eventuallyEq_genericState
      ((realization.chain x).state (realization.terminalIndex x))

end RootedRealizationComparison

end CartanCanonicalRootedRealizationTransfer
end Poincare
