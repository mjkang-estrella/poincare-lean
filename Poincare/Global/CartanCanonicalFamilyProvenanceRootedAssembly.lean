import Poincare.Global.CartanCanonicalFamilyTransitionAgreementAssembly
import Poincare.Global.CartanCanonicalFamilyProvenanceLocalUniformData

/-!
# Rooted canonical realization with retained generic successor provenance

This module repeats the open-cover and finite rooted-chain selection with the
provenance-retaining successor package.  Each selected canonical datum and its
`GenericSuccessorComparison` are chosen together, so the resulting rooted
realization carries `RootedRealizationComparison` by construction.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanCanonicalFamilyProvenanceRootedAssembly

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalFamilyProvenanceLocalUniformData
open CartanCanonicalRootedRealizationTransfer
open CartanAtlasRootedPathSkeleton

/-- The parameter locus where every tangent alignment has a canonical datum
selected together with its generic successor comparison. -/
def UniversalComparedSuccessorLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Set ((M × RoundSphere3) × M) :=
  {q | ∀ L : CartanMap.TangentAlignment g q.1.1 q.1.2,
    Nonempty
      (CanonicalComparedStep
        (ChainState.mk q.1.1 q.1.2 L) q.2)}

/-- A local provenance producer puts its controlled open locus inside the
universal compared-successor locus. -/
theorem controlledSuccessorLocus_subset_compared
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) {rho : ℝ}
    (hdata :
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        (x, z) ∈ A.sourceLocus →
        ‖A.normal (x, z)‖ < rho →
          Nonempty
            (TransferredSuccessorPackage
              (CartanChain.ChainState.mk x p L) z)) :
    A.controlledSuccessorLocus rho ⊆
      UniversalComparedSuccessorLocus g := by
  rintro ⟨⟨x, p⟩, z⟩ hz L
  rcases hdata x p L z hz.1 (by
    simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball, dist_eq_norm]
      using hz.2) with
    ⟨package⟩
  exact ⟨package.toCanonicalComparedStep⟩

/-- An open chart-local cover with retained successor packages proves a
neighborhood of the full source-target diagonal in the compared locus. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_localCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcover : ∀ x : M,
      ∃ A : LocalFamily g,
        x ∈ A.anchors ∧ LocalUniformNormalTransferredSuccessorData A) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  classical
  choose A hxA hlocal using hcover
  choose rho hrho hdata using hlocal
  let W : Set ((M × RoundSphere3) × M) :=
    ⋃ x : M, (A x).controlledSuccessorLocus (rho x)
  have hopenW : IsOpen W :=
    isOpen_iUnion fun x ↦ (A x).isOpen_controlledSuccessorLocus (rho x)
  have hdiagW : successorParameterDiagonal (M := M) ⊆ W := by
    rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    change (x, x) ∈ (A x).sourceLocus ∧
      (A x).normal (x, x) ∈ Metric.ball (0 : E) (rho x)
    constructor
    · exact (A x).diagonal_mem x (hxA x)
    · rw [(A x).normal_diagonal x (hxA x)]
      exact Metric.mem_ball_self (hrho x)
  have hWcompared : W ⊆ UniversalComparedSuccessorLocus g := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨x, hx⟩
    exact controlledSuccessorLocus_subset_compared (A x) (hdata x) hx
  exact Filter.mem_of_superset (hopenW.mem_nhdsSet.mpr hdiagW) hWcompared

section Compact

variable [CompactSpace M] [ConnectedSpace M]

/-- Compactness of the diagonal turns the open compared-successor cover into
one uniform metric radius. -/
theorem exists_uniform_comparedSuccessor_radius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hneighborhood : UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (CanonicalComparedStep (ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      (Metric.hasBasis_nhdsSet_cthickening
        (isCompact_successorParameterDiagonal (M := M))).mem_iff.mp
        hneighborhood with
    ⟨epsilon, hepsilon, hthick⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro x p L z hdist
  let graphPoint : (M × RoundSphere3) × M := ((x, p), x)
  have hgraphPoint : graphPoint ∈ successorParameterDiagonal (M := M) :=
    ⟨(x, p), Set.mem_univ _, rfl⟩
  have hmem :
      ((x, p), z) ∈ Metric.cthickening epsilon
        (successorParameterDiagonal (M := M)) := by
    apply Metric.mem_cthickening_of_dist_le
      (((x, p), z) : (M × RoundSphere3) × M) graphPoint epsilon
        (successorParameterDiagonal (M := M)) hgraphPoint
    simpa [graphPoint, Prod.dist_eq] using le_of_lt hdist
  exact (hthick hmem) L

/-- A canonical reachable chain paired definitionally with the comparison of
every datum actually selected by its recursion. -/
structure ComparedReachableChain
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : ChainState canonicalFamily g) where
  chain : CartanTargetExponential.Chain.ReachableChain
    canonicalFamily nodes initial
  comparison : ReachableChainComparison chain

/-- Build a compared reachable chain from packages available only at the
states actually reached. -/
def comparedReachableChain_of_anchored_step_supply
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : ChainState canonicalFamily g)
    (hinitial : initial.anchor = nodes 0)
    (hstep : ∀ (n : ℕ) (s : ChainState canonicalFamily g),
      s.anchor = nodes n →
        Nonempty (CanonicalComparedStep s (nodes (n + 1)))) :
    ComparedReachableChain nodes initial := by
  classical
  let stepPackage : ∀ (n : ℕ) (s : ChainState canonicalFamily g),
      s.anchor = nodes n → CanonicalComparedStep s (nodes (n + 1)) := by
    intro n s hs
    exact Classical.choice (hstep n s hs)
  let state : ∀ n : ℕ,
      {s : ChainState canonicalFamily g // s.anchor = nodes n} := by
    intro n
    induction n with
    | zero => exact ⟨initial, hinitial⟩
    | succ n state_n =>
        let package := stepPackage n state_n.1 state_n.2
        exact ⟨package.canonicalData.successor,
          package.canonicalData.successor_anchor⟩
  let chain : CartanTargetExponential.Chain.ReachableChain
      canonicalFamily nodes initial :=
    { state := fun n ↦ (state n).1
      initial_eq := rfl
      data := fun n ↦
        (stepPackage n (state n).1 (state n).2).canonicalData
      successor_eq := by
        intro n
        rfl }
  let comparison : ReachableChainComparison chain :=
    { step := fun n ↦
        (stepPackage n (state n).1 (state n).2).comparison }
  exact ⟨chain, comparison⟩

/-- A uniform compared-successor radius realizes every rooted path with the
same prescribed mesh and automatically retains `RootedRealizationComparison`.
-/
theorem exists_comparedRootedRealization_with_prescribed_mesh_of_uniformRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdata :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty (CanonicalComparedStep (ChainState.mk x p L) z))
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let radius : ℝ := min epsilon mesh
  have hradius : 0 < radius := lt_min hepsilon hmesh
  have hpath : ∀ x : M,
      ∃ (t : ℕ → unitInterval) (k : ℕ),
        0 < k ∧ t 0 = 0 ∧ Monotone t ∧
        (∀ n ≥ k, t n = 1) ∧
        (∀ n : ℕ,
          dist (skeleton.path x (t n))
            (skeleton.path x (t (n + 1))) < mesh) ∧
        Nonempty
          (ComparedReachableChain
            (fun n ↦ skeleton.path x (t n))
            (ChainState.retarget canonicalFamily skeleton.root)) := by
    intro x
    rcases CartanChain.exists_monotone_unitInterval_subdivision_dist_lt
        (γ := (skeleton.path x).toContinuousMap) hradius with
      ⟨t, htzero, htmono, ⟨m, hterminal⟩, hclose⟩
    let k : ℕ := max m 1
    have hmk : m ≤ k := le_max_left _ _
    have honeK : 1 ≤ k := le_max_right _ _
    have hk : 0 < k := Nat.zero_lt_one.trans_le honeK
    have htone : ∀ n ≥ k, t n = 1 := by
      intro n hn
      exact hterminal n (hmk.trans hn)
    have hsmall : ∀ n : ℕ,
        dist (skeleton.path x (t n))
          (skeleton.path x (t (n + 1))) < mesh := by
      intro n
      exact (hclose n).trans_le (min_le_right _ _)
    have hstep : ∀ (n : ℕ) (s : ChainState canonicalFamily g),
        s.anchor = skeleton.path x (t n) →
          Nonempty
            (CanonicalComparedStep s (skeleton.path x (t (n + 1)))) := by
      intro n s hs
      have hdist :
          dist (skeleton.path x (t (n + 1))) s.anchor < epsilon := by
        rw [hs]
        simpa [dist_comm] using
          (hclose n).trans_le (min_le_left epsilon mesh)
      have package := hdata s.anchor s.target s.alignment
        (skeleton.path x (t (n + 1))) hdist
      have heta : ChainState.mk s.anchor s.target s.alignment = s := by
        cases s
        rfl
      exact heta ▸ package
    have hinitial :
        (ChainState.retarget canonicalFamily skeleton.root).anchor =
          skeleton.path x (t 0) := by
      rw [htzero]
      simp
    exact ⟨t, k, hk, htzero, htmono, htone, hsmall,
      ⟨comparedReachableChain_of_anchored_step_supply
        (fun n ↦ skeleton.path x (t n))
        (ChainState.retarget canonicalFamily skeleton.root)
        hinitial hstep⟩⟩
  choose t k hk htzero htmono htone hsmall hchain using hpath
  let realization : SuppliedRootedPathChainRealization
      canonicalFamily skeleton :=
    { nodeTime := t
      nodeTime_zero := htzero
      terminalIndex := k
      nodeTime_terminal := fun x ↦ htone x (k x) le_rfl
      chain := fun x ↦ (Classical.choice (hchain x)).chain }
  let comparison : RootedRealizationComparison realization :=
    { chain := fun x ↦ (Classical.choice (hchain x)).comparison }
  exact ⟨realization, comparison, hk, htmono, htone, hsmall⟩

/-- An open compared-successor neighborhood gives the complete selected rooted
realization and its automatic comparison. -/
theorem exists_comparedRootedRealization_with_prescribed_mesh_of_neighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    (hneighborhood : UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)))
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_comparedSuccessor_radius hneighborhood with
    ⟨epsilon, hepsilon, hdata⟩
  exact exists_comparedRootedRealization_with_prescribed_mesh_of_uniformRadius
    skeleton hepsilon hdata mesh hmesh

end Compact

section TransitionAgreement

variable [CompactSpace M] [ConnectedSpace M]

/-- A positive jointly lower-semicontinuous admissible provenance radius and
the fixed-chart transition packages produce a compared-successor
neighborhood.  This is the direct consumer used by the locally stable radius
envelope; it does not compare against an arbitrary classically chosen radius. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_admissibleRadius_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hadmissible : ∀ (x : M) (p : RoundSphere3),
      TransferredNormalRadiusAdmissible g x p (pairRadius x p))
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply comparedSuccessorLocus_mem_nhdsSet_of_localCover
  intro x₀
  rcases
      exists_chartLocal_genericNormal_transferredPackage_of_admissible
        pairRadius hpositive hlower hadmissible x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius, hgenericPackage⟩
  rcases htransition x₀ with ⟨C, ⟨P⟩⟩
  rcases
      FixedChartAnchorEndpointPackage.TransitionAgreementPackage.exists_localFamily
        C P with
    ⟨A, hx₀A, localRadius, hlocalRadius, hendpoint⟩
  let radius : ℝ := min localRadius genericRadius
  have hradius : 0 < radius := lt_min hlocalRadius hgenericRadius
  let B : LocalFamily g := A.restrictAnchors U hU
  have hx₀B : x₀ ∈ B.anchors := ⟨hx₀A, hx₀U⟩
  have hendpointB : B.GenericEndpointAgreement radius :=
    (hendpoint.mono_radius (min_le_left _ _)).restrictAnchors U hU
  have hanchors : B.anchors ⊆ U := fun _x hx ↦ hx.2
  have hpackageB : LocalUniformNormalTransferredSuccessorData B := by
    apply localUniformTransferredData_of_genericEndpointAgreement
      B hradius hanchors hendpointB
    intro x hx p L z hzSource hzNorm
    exact hgenericPackage x hx p L z hzSource
      (hzNorm.trans_le (min_le_right _ _))
  exact ⟨B, hx₀B, hpackageB⟩

/-- The canonical locally stable radius envelope discharges all radius-choice
and lower-semicontinuity premises.  Only positive local stability of actual
admissible radii and the varying-anchor transition packages remain. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_localStability_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply
    comparedSuccessorLocus_mem_nhdsSet_of_admissibleRadius_of_transitionAgreementPackages
      (fun x p ↦
        canonicalLocallyUniformTransferredAnchorTargetRadius g x p)
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_pos hstable
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_lowerSemicontinuous g
  · exact
      canonicalLocallyUniformTransferredAnchorTargetRadius_admissible hstable
  · exact htransition

/-- The fixed-chart transition packages and the provenance radius minorant
produce a compared-successor neighborhood. -/
theorem comparedSuccessorLocus_mem_nhdsSet_of_joint_minorant_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        canonicalTransferredAnchorTargetRadius hcurv x p)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage) :
    UniversalComparedSuccessorLocus g ∈
      nhdsSet (successorParameterDiagonal (M := M)) := by
  apply comparedSuccessorLocus_mem_nhdsSet_of_localCover
  intro x₀
  rcases
      exists_chartLocal_genericNormal_transferredPackage_of_joint_minorant
        hcurv pairRadius hpositive hlower hminorant x₀ with
    ⟨U, hU, hx₀U, genericRadius, hgenericRadius, hgenericPackage⟩
  rcases htransition x₀ with ⟨C, ⟨P⟩⟩
  rcases
      FixedChartAnchorEndpointPackage.TransitionAgreementPackage.exists_localFamily
        C P with
    ⟨A, hx₀A, localRadius, hlocalRadius, hendpoint⟩
  let radius : ℝ := min localRadius genericRadius
  have hradius : 0 < radius := lt_min hlocalRadius hgenericRadius
  let B : LocalFamily g := A.restrictAnchors U hU
  have hx₀B : x₀ ∈ B.anchors := ⟨hx₀A, hx₀U⟩
  have hendpointB : B.GenericEndpointAgreement radius :=
    (hendpoint.mono_radius (min_le_left _ _)).restrictAnchors U hU
  have hanchors : B.anchors ⊆ U := fun _x hx ↦ hx.2
  have hpackageB : LocalUniformNormalTransferredSuccessorData B := by
    apply localUniformTransferredData_of_genericEndpointAgreement
      B hradius hanchors hendpointB
    intro x hx p L z hzSource hzNorm
    exact hgenericPackage x hx p L z hzSource
      (hzNorm.trans_le (min_le_right _ _))
  exact ⟨B, hx₀B, hpackageB⟩

/-- The canonical transition-agreement construction now selects a prescribed
mesh realization with `RootedRealizationComparison` automatically retained. -/
theorem exists_comparedCanonicalRootedRealization_with_prescribed_mesh_of_joint_minorant_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (pairRadius : M → RoundSphere3 → ℝ)
    (hpositive : ∀ (x : M) (p : RoundSphere3), 0 < pairRadius x p)
    (hlower : LowerSemicontinuous
      (fun xp : M × RoundSphere3 ↦ pairRadius xp.1 xp.2))
    (hminorant : ∀ (x : M) (p : RoundSphere3),
      pairRadius x p ≤
        canonicalTransferredAnchorTargetRadius hcurv x p)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton : RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  let hneighborhood :=
    comparedSuccessorLocus_mem_nhdsSet_of_joint_minorant_of_transitionAgreementPackages
      hcurv pairRadius hpositive hlower hminorant htransition
  exact exists_comparedRootedRealization_with_prescribed_mesh_of_neighborhood
    skeleton hneighborhood mesh hmesh

/-- A locally stable positive provenance radius at every source-target pair
selects a prescribed-mesh rooted realization with its generic comparison.
The lower-semicontinuous radius used internally is the canonical capped
supremum envelope, not a `Classical.choose` witness. -/
theorem exists_comparedCanonicalRootedRealization_with_prescribed_mesh_of_localStability_of_transitionAgreementPackages
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hstable : TransferredNormalRadiusLocalStability g)
    (htransition : ∀ x₀ : M,
      ∃ C : FixedChartAnchorEndpointPackage g x₀,
        Nonempty C.TransitionAgreementPackage)
    (skeleton : RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh := by
  let hneighborhood :=
    comparedSuccessorLocus_mem_nhdsSet_of_localStability_of_transitionAgreementPackages
      hstable htransition
  exact exists_comparedRootedRealization_with_prescribed_mesh_of_neighborhood
    skeleton hneighborhood mesh hmesh

end TransitionAgreement

end CartanCanonicalFamilyProvenanceRootedAssembly
end Poincare
