import Poincare.Global.CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
import Poincare.Global.CartanCanonicalFamilyComparedCanonicalContinuation

/-!
# Direct rooted Cartan recognition from the generic data neighborhood

The canonical target-family route previously entered the legacy rooted
transport pipeline by selecting, at every step, a canonical datum together
with a generic provenance comparison.  That is stronger than the direct
transport consumer needs.

This file constructs the rooted path realization directly from the uniform
generic successor-data certificate already used by the homotopy-grid
argument.  The path subdivision is chosen geometrically, with strict sample
times and whole-cell diameter control; the generic reachable chain is then
reconstructed from the same certificate.  Consequently direct recognition
uses only

* the generic successor-data neighborhood, and
* the actual-successor equality neighborhood.

No `UniversalComparedSuccessorLocus`, `CanonicalComparedStep`, or
`RootedRealizationComparison` occurs in the result.  The final section names
the exact remaining bridge from a canonical-family data neighborhood to the
legacy generic data neighborhood.  This bridge asks only for generic data
existence, not for any comparison between independently selected successors.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedDirectGenericNeighborhoodRecognition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open CartanAtlasRootedPathAdaptiveMeshRealization
open CartanAtlasRootedPathCurvatureSuccessorRadius
open CartanAtlasRootedReachableEndpointTransport
open CartanAtlasRootedPathSkeleton
open CartanCanonicalFamilyComparedWholeCellRealization
open CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanCanonicalRootedUniformSuccessorMeshRecognition
open CartanTargetExponential
open DifferentialSuccessorJointEqualityNeighborhood
open DifferentialSuccessorFiniteSubdivisionRefinement
open DifferentialUniformSuccessorStrictFactorGeometry

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-! ## A geometric whole-cell realization for the generic family -/

/--
The joint generic-data/equality certificate constructs a rooted generic
realization whose selected parameter cells have diameter below its mesh
radius.

The subdivision is chosen without querying any successor data.  Removing
duplicate parameter values makes it strictly increasing up to its terminal
index.  Only after that geometric choice do we use the uniform generic-data
radius to construct the actually reached chain.
-/
theorem exists_genericRootedRealization_with_wholeCellMesh_of_certificate
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (skeleton : RootedCartanPathSkeleton g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization : RootedPathChainRealization skeleton,
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n < realization.terminalIndex x,
        realization.nodeTime x n < realization.nodeTime x (n + 1)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        b ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) <
          certificate.meshRadius := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hhalf : 0 < certificate.meshRadius / 2 :=
    half_pos certificate.meshRadius_pos
  have hpath : ∀ x : M,
      ∃ (r : ℕ → unitInterval) (K : ℕ),
        r 0 = 0 ∧ Monotone r ∧
        (∀ n < K, r n < r (n + 1)) ∧
        (∀ n ≥ K, r n = 1) ∧
        (∀ (n : ℕ) (a b : unitInterval),
          a ∈ Icc (r n) (r (n + 1)) →
          b ∈ Icc (r n) (r (n + 1)) →
          dist (skeleton.path x a) (skeleton.path x b) <
            certificate.meshRadius) ∧
        Nonempty
          (DifferentialInducedSuccessor.Chain.ReachableChain
            (fun n ↦ skeleton.path x (r n)) skeleton.root) := by
    intro x
    rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
        (skeleton.path x).toContinuousMap
        (fun _ ↦ certificate.meshRadius / 2) (fun _ ↦ hhalf) with
      ⟨t, k, center, _eta, htzero, htmono, htone, _heta,
        _hetaLower, hcell⟩
    let V : Finset unitInterval := finiteSubdivisionValues t k
    let S : Finset unitInterval := V.erase 0
    let r : ℕ → unitInterval := finiteSortedSequence S
    let K : ℕ := S.card
    have honeV : (1 : unitInterval) ∈ V := by
      have hmem := mem_finiteSubdivisionValues t k k le_rfl
      simpa [V, htone k le_rfl] using hmem
    have honeS : (1 : unitInterval) ∈ S :=
      Finset.mem_erase.mpr ⟨one_ne_zero, honeV⟩
    have hzeroS : (0 : unitInterval) ∉ S := by simp [S]
    have hrzero : r 0 = 0 := by
      exact finiteSortedSequence_zero S
    have hrmono : Monotone r := by
      simpa [r] using finiteSortedSequence_monotone S
    have hrstrict : ∀ n < K, r n < r (n + 1) := by
      simpa [r, K] using
        finiteSortedSequence_strict_until_card_of_one_mem_zero_not_mem
          S hzeroS honeS
    have hrone : ∀ n ≥ K, r n = 1 := by
      simpa [r, K] using
        finiteSortedSequence_eventually_one_from_card_of_one_mem_zero_not_mem
          S honeS
    have hmem : ∀ i ≤ k, t i = 0 ∨ t i ∈ S := by
      intro i hi
      by_cases hzero : t i = 0
      · exact Or.inl hzero
      · exact Or.inr <| Finset.mem_erase.mpr
          ⟨hzero, mem_finiteSubdivisionValues t k i hi⟩
    have hbracket : ∀ n : ℕ, ∃ j : ℕ,
        t j ≤ r n ∧ r (n + 1) ≤ t (j + 1) := by
      intro n
      simpa only [r] using
        (exists_subdivision_bracket_of_prefix_values S t htzero k htone
          hmem n)
    have hwhole : ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (r n) (r (n + 1)) →
        b ∈ Icc (r n) (r (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) <
          certificate.meshRadius := by
      intro n a b ha hb
      rcases hbracket n with ⟨j, hjleft, hjright⟩
      by_cases hj : j ≤ k
      · let i : Fin (k + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
        have haCenter := hcell i a
          ⟨hjleft.trans ha.1, ha.2.trans hjright⟩
        have hbCenter := hcell i b
          ⟨hjleft.trans hb.1, hb.2.trans hjright⟩
        calc
          dist (skeleton.path x a) (skeleton.path x b) ≤
              dist (skeleton.path x a) (skeleton.path x (center i)) +
                dist (skeleton.path x b) (skeleton.path x (center i)) :=
            dist_triangle_right _ _ _
          _ < certificate.meshRadius / 2 +
                certificate.meshRadius / 2 :=
            add_lt_add haCenter hbCenter
          _ = certificate.meshRadius := by ring
      · have hkj : k ≤ j := le_of_not_ge hj
        have htj : t j = 1 := htone j hkj
        have htjnext : t (j + 1) = 1 :=
          htone (j + 1) (hkj.trans (Nat.le_succ j))
        have ha' : a ∈ Icc (1 : unitInterval) 1 := by
          exact ⟨(by simpa [htj] using (hjleft.trans ha.1)),
            (by simpa [htjnext] using (ha.2.trans hjright))⟩
        have hb' : b ∈ Icc (1 : unitInterval) 1 := by
          exact ⟨(by simpa [htj] using (hjleft.trans hb.1)),
            (by simpa [htjnext] using (hb.2.trans hjright))⟩
        have hab : a = b := by
          apply le_antisymm
          · exact ha'.2.trans hb'.1
          · exact hb'.2.trans ha'.1
        simpa [hab] using certificate.meshRadius_pos
    have hinitial : skeleton.root.anchor = skeleton.path x (r 0) := by
      simp [hrzero]
    have hsmall : ∀ n : ℕ,
        dist (skeleton.path x (r (n + 1)))
          (skeleton.path x (r n)) < certificate.meshRadius := by
      intro n
      have hmono : r n ≤ r (n + 1) := hrmono (Nat.le_succ n)
      simpa [dist_comm] using hwhole n (r n) (r (n + 1))
        ⟨le_rfl, hmono⟩ ⟨hmono, le_rfl⟩
    let chain : DifferentialInducedSuccessor.Chain.ReachableChain
        (fun n ↦ skeleton.path x (r n)) skeleton.root :=
      DifferentialUniformSuccessorStrictFactorGeometry.JointUniformSuccessorRadiusCertificate.realizedChainOfMeshSmall
        certificate (fun n ↦ skeleton.path x (r n)) skeleton.root
          hinitial hsmall
    exact ⟨r, K, hrzero, hrmono, hrstrict, hrone, hwhole, ⟨chain⟩⟩
  choose r K hrzero hrmono hrstrict hrone hwhole hchain using hpath
  let realization : RootedPathChainRealization skeleton :=
    { nodeTime := r
      nodeTime_zero := hrzero
      terminalIndex := K
      nodeTime_terminal := fun x ↦ hrone x (K x) le_rfl
      chain := fun x ↦ Classical.choice (hchain x) }
  exact ⟨realization, hrmono, hrstrict, hrone, hwhole⟩

/-! ## Direct recognition without compared successors -/

/-- The reached generic terminal source, restricted by the schedule-free
short-path distance cutoff.  This is the endpoint-family version of the older
definition whose argument was unnecessarily bundled with a canonical
realization package. -/
def genericScheduleFreeTerminalRestrictedDomain
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) : Set M := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (endpoint.terminalState y).germ.source ∩
      Metric.ball y
        (CartanTerminalShortPathScheduleFree.scheduleFreeTerminalDistanceRadius
          g y hmesh)

theorem isOpen_genericScheduleFreeTerminalRestrictedDomain
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    IsOpen (genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y) := by
  letI : MetricSpace M := g.toMetricSpace
  exact (endpoint.terminalState y).germ.open_source.inter Metric.isOpen_ball

theorem anchor_mem_genericScheduleFreeTerminalRestrictedDomain
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) (y : M) :
    y ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y := by
  letI : MetricSpace M := g.toMetricSpace
  constructor
  · have hmem :
        (endpoint.terminalState y).anchor ∈
          (endpoint.terminalState y).germ.source :=
      CartanMap.anchor_mem_source g
        (endpoint.terminalState y).anchor
        (endpoint.terminalState y).target
        (endpoint.terminalState y).alignment
    simpa only [endpoint.terminalState_anchor y] using hmem
  · exact Metric.mem_ball_self
      (CartanTerminalShortPathScheduleFree.scheduleFreeTerminalDistanceRadius_pos
        g y hmesh)

/-- Membership in the generic terminal restriction supplies the actual short
terminal path consumed by direct boundary subdivision. -/
theorem terminalShortPathCertificate_of_mem_genericRestrictedDomain
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) {y z : M}
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y) :
    Nonempty
      (CartanCanonicalRootedEndpointAssembly.TerminalShortPathCertificate
        g y z mesh) := by
  apply
    CartanTerminalShortPathScheduleFree.terminalShortPathCertificate_of_dist_lt_scheduleFreeTerminalDistanceRadius
      g y hmesh
  simpa only [Metric.mem_ball] using hz.2

/-- An arbitrary generic rooted endpoint family with strict whole-cell mesh
control gives the restricted compatible Cartan atlas directly. -/
noncomputable def
    restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry
    [SimplyConnectedSpace M]
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hnodeMono : ∀ x : M, Monotone (endpoint.nodeTime x))
    (hnodeStrict : ∀ x : M,
      ∀ n < endpoint.terminalIndex x,
        endpoint.nodeTime x n < endpoint.nodeTime x (n + 1))
    (hwholeCell :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        dist (endpoint.path x a) (endpoint.path x b) <
          certificate.meshRadius) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := endpoint.target
  alignment := endpoint.alignment
  domain := genericScheduleFreeTerminalRestrictedDomain endpoint
    certificate.meshRadius_pos
  isOpen_domain :=
    isOpen_genericScheduleFreeTerminalRestrictedDomain endpoint
      certificate.meshRadius_pos
  anchor_mem_domain :=
    anchor_mem_genericScheduleFreeTerminalRestrictedDomain endpoint
      certificate.meshRadius_pos
  domain_subset_source := by
    intro x z hz
    have hterminal : z ∈ (endpoint.terminalState x).germ.source := hz.1
    have hx := endpoint.anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g endpoint.target
        endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    let leftTerminal :
        CartanCanonicalRootedEndpointAssembly.TerminalShortPathCertificate
          g x z certificate.meshRadius :=
      Classical.choice
        (terminalShortPathCertificate_of_mem_genericRestrictedDomain
          endpoint certificate.meshRadius_pos hz.1)
    let rightTerminal :
        CartanCanonicalRootedEndpointAssembly.TerminalShortPathCertificate
          g y z certificate.meshRadius :=
      Classical.choice
        (terminalShortPathCertificate_of_mem_genericRestrictedDomain
          endpoint certificate.meshRadius_pos hz.2)
    let transport :
        CartanAtlasRealizedEndpointTransport.CommonRootTerminalTransport
          (endpoint.terminalState x) (endpoint.terminalState y) z :=
      Classical.choice
        (nonempty_commonRootTerminalTransport_of_directBoundaryGeometry
          certificate endpoint leftTerminal rightTerminal
          (hnodeMono x) (hnodeMono y) (hnodeStrict x) (hnodeStrict y)
          (hwholeCell x) (hwholeCell y))
    have hvalue :=
      CartanAtlasRealizedEndpointTransport.germ_value_eq_of_commonRootTerminalTransport
        (endpoint.terminalState x) (endpoint.terminalState y) z transport
    have hx := endpoint.anchoredFamilyState_eq_terminalState x
    have hy := endpoint.anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g endpoint.target
          endpoint.alignment x).germ z =
        (CartanLocalRigidity.anchoredFamilyState g endpoint.target
          endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/--
The legacy generic successor-data neighborhood and the actual-data equality
neighborhood suffice for direct unit-curvature recognition.

Unlike the previous canonical adapter, this theorem does not first choose a
canonical chain and then prove that every selected step has generic
provenance.  Both the rooted paths and the homotopy grid use the same generic
uniform-data certificate from the outset.
-/
theorem unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (dataStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorEqualityNeighborhood g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  let successor : UniformGenericSuccessorRadiusCertificate g :=
    uniformGenericSuccessorRadiusCertificateOfNeighborhood
      g (dataStability g hcurv)
  rcases exists_uniformSuccessorEqOnBall_of_jointNeighborhood
      g (equalityStability g hcurv) with
    ⟨eta, heta, heq⟩
  let certificate : JointUniformSuccessorRadiusCertificate g :=
    { successorData := successor
      equalityRadius := eta
      equalityRadius_pos := heta
      successorEqOnBall := heq }
  let skeleton := Classical.choice
    (CartanAtlasRootedPathSkeleton.nonempty_rootedCartanPathSkeleton g)
  rcases
      exists_genericRootedRealization_with_wholeCellMesh_of_certificate
        certificate skeleton with
    ⟨realization, hmono, hstrict, _heventual, hwhole⟩
  let endpoint := realization.toEndpointFamily
  have hendpointMono : ∀ x : M,
      Monotone (endpoint.nodeTime x) := hmono
  have hendpointStrict : ∀ x : M,
      ∀ n < endpoint.terminalIndex x,
        endpoint.nodeTime x n < endpoint.nodeTime x (n + 1) := hstrict
  have hendpointWhole :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        dist (endpoint.path x a) (endpoint.path x b) <
          certificate.meshRadius := hwhole
  exact ⟨
    restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry
      certificate endpoint hendpointMono hendpointStrict hendpointWhole⟩

/-! ## The exact canonical-to-generic bridge -/

/--
The remaining conversion boundary after removing compared successors.

It asks only that existence of canonical-family successor data near the full
diagonal imply existence of legacy generic successor data near that diagonal.
There is no selected datum, target-chart germ comparison, or successor-state
equality in this statement.
-/
def CanonicalDataNeighborhoodToGenericDataNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  UniversalSuccessorDataNeighborhood canonicalFamily g →
    CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood g

/-- The former conditional compared-successor continuation implies the new
existence-only bridge.  This one-way projection records formally that the new
recognition route has discarded selected-step comparison data. -/
theorem canonicalDataNeighborhoodToGenericDataNeighborhood_of_comparedContinuation
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcontinuation :
      CartanCanonicalFamilyComparedCanonicalContinuation.CanonicalComparedDiagonalContinuation
        g) :
    CanonicalDataNeighborhoodToGenericDataNeighborhood g := by
  intro hcanonical
  exact
    CartanCanonicalFamilyComparedToGenericSuccessorRadius.universalSuccessorDataNeighborhood_of_comparedNeighborhood
      (CartanCanonicalFamilyComparedCanonicalContinuation.comparedSuccessorLocus_mem_nhdsSet_of_canonicalNeighborhood_of_continuation
        hcanonical hcontinuation)

/--
A canonical data-neighborhood provider plus the strictly weaker
canonical-to-generic existence bridge feeds the direct generic recognition
theorem.  This is the canonical-family adapter with all compared-successor
payload removed.
-/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalDataNeighborhood_genericBridge_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (canonicalStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood canonicalFamily g)
    (genericBridge : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalDataNeighborhoodToGenericDataNeighborhood g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorEqualityNeighborhood g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_jointEqualityNeighborhood
  · intro g hcurv
    exact genericBridge g hcurv (canonicalStability g hcurv)
  · exact equalityStability

end CartanCanonicalRootedDirectGenericNeighborhoodRecognition
end Poincare
