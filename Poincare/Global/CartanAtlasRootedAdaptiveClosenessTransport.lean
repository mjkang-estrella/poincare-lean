import Poincare.Global.CartanAtlasRootedReachableEndpointTransport

/-!
# Rooted Cartan transport from the actual adaptive closeness tests

Constant curvature already supplies, in the correct dependent order, a
positive first radius for every realized insertion history and then a
positive second radius after the first tests have succeeded.  This file
connects those radii directly to the rooted endpoint-atlas consumer.

The resulting interface does not assume equality of germs or equality of
terminal states.  It retains exactly the two finite families of metric
closeness inequalities produced by adaptive refinement.  Proving that a
globally chosen refinement satisfies those inequalities is still the genuine
compact-history gap.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare
namespace CartanAtlasRootedAdaptiveClosenessTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedReachableEndpointTransport
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport
open DifferentialSuccessorAdaptiveFeedbackIteration

namespace RootedOverlapStrictFactorSchedule

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M}

/-- A strict factor is monotone as long as both indices stay inside the
realized finite schedule. -/
theorem factor_le_factor_of_le
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ schedule.length) :
    schedule.factor a ≤ schedule.factor b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
      exact
        (ih (by omega) (by omega)).trans
          (schedule.factor_strict (a + d) (by omega)).le

/-- The node introduced at one actual insertion step is exactly the
corresponding refined node. -/
theorem insertedNode_eq_refined
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (n : Fin schedule.length)
    (i : Fin (factorGapNodes schedule.refined schedule.factor n).length) :
    insertNodeListSchedule
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n)
        (factorGapNodes schedule.refined schedule.factor n) (i + 1)
          (schedule.factor n + i + 1) =
      schedule.refined (schedule.factor n + i + 1) := by
  rw [insertNodeListSchedule_succ_inserted _ _ _ i i.isLt]
  simpa only [List.get_eq_getElem, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
      factorGapNodes_get schedule.refined schedule.factor n i

/-- Immediately before an insertion, the displayed old next node is the
retained coarse node on the right of the current factor gap. -/
theorem oldNextNode_eq_seed_succ
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (n : Fin schedule.length)
    (i : Fin (factorGapNodes schedule.refined schedule.factor n).length) :
    insertNodeListSchedule
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n)
        (factorGapNodes schedule.refined schedule.factor n) i
          (schedule.factor n + i + 1) =
      schedule.seed (n + 1) := by
  let gap := factorGapNodes schedule.refined schedule.factor n
  have hiGap : (i : ℕ) < gap.length := by
    simpa [gap] using i.isLt
  have htake : (gap.take (i : ℕ)).length = i := by
    simp only [List.length_take, Nat.min_eq_left hiGap.le]
  have hshift :=
    insertNodeList_shifted
      (factorRefinementStage schedule.seed schedule.refined schedule.factor n)
      (schedule.factor n) 0 (gap.take (i : ℕ))
  have htail :=
    (factorRefinementStage_prefix_tail schedule.seed schedule.refined
      schedule.factor schedule.length schedule.factor_zero
      schedule.factor_strict schedule.factor_value n n.isLt.le).2 1
  change
    insertNodeList
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n) (gap.take (i : ℕ))
          (schedule.factor n + i + 1) = schedule.seed (n + 1)
  calc
    _ = factorRefinementStage schedule.seed schedule.refined schedule.factor n
          (schedule.factor n + 1) := by
      simpa [htake, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
    _ = schedule.seed (n + 1) := by simpa using htail

/-- The predecessor node retained by an actual insertion history is the
corresponding refined node.  This is the node-level statement; the state at
index zero still has the independently supplied root anchor. -/
theorem insertionPredecessorNode_eq_refined
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (n : Fin schedule.length)
    (i : Fin (factorGapNodes schedule.refined schedule.factor n).length) :
    insertNodeListSchedule
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n)
        (factorGapNodes schedule.refined schedule.factor n) (i + 1)
          (schedule.factor n + i) =
      schedule.refined (schedule.factor n + i) := by
  let gap := factorGapNodes schedule.refined schedule.factor n
  have hiGap : (i : ℕ) < gap.length := by
    simpa [gap] using i.isLt
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · have hpreserve :=
      insertNodeListSchedule_succ_eq_of_le
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n) gap 0 (schedule.factor n)
          (by omega) (by omega)
    have hprefix :=
      (factorRefinementStage_prefix_tail schedule.seed schedule.refined
        schedule.factor schedule.length schedule.factor_zero
        schedule.factor_strict schedule.factor_value n n.isLt.le).1
          (schedule.factor n) le_rfl
    simpa [gap, hi] using hpreserve.trans hprefix
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have hjlt : j < gap.length := by
      omega
    have hipreserve :=
      insertNodeListSchedule_succ_eq_of_le
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n) gap (j + 1)
          (schedule.factor n + (j + 1))
          (by omega) (by omega)
    have hinserted :=
      insertNodeListSchedule_succ_inserted
        (factorRefinementStage schedule.seed schedule.refined
          schedule.factor n) (schedule.factor n) gap j hjlt
    rw [hj]
    calc
      _ = insertNodeListSchedule
          (factorRefinementStage schedule.seed schedule.refined
            schedule.factor n) (schedule.factor n) gap (j + 1)
            (schedule.factor n + j + 1) := by
        simpa [Nat.add_assoc] using hipreserve
      _ = gap[j] := by simpa [Nat.add_assoc] using hinserted
      _ = schedule.refined (schedule.factor n + (j + 1)) := by
        simp [gap, factorGapNodes, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

/-- At every positive predecessor index, the realized insertion-chain state
is anchored at the corresponding refined node.  The zero-index case is
deliberately excluded because it is anchored at `endpoint.root`. -/
theorem insertionPredecessorAnchor_eq_refined_of_pos
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (n : Fin schedule.length)
    (i : Fin (factorGapNodes schedule.refined schedule.factor n).length)
    (hpos : 0 < schedule.factor n + i) :
    ((schedule.insertionChain n (i + 1)).state
        (schedule.factor n + i)).anchor =
      schedule.refined (schedule.factor n + i) := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hq]
  have hnode := insertionPredecessorNode_eq_refined schedule n i
  exact
    ((schedule.insertionChain n (i + 1)).state_succ_anchor q).trans
      (by simpa [hq] using hnode)

/-- A terminal equality for the two realized strict-factor chains gives the
actual common-root terminal transport consumed by Cartan compatibility. -/
def toCommonRootTerminalTransport_of_terminal_eq
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hterminal :
      schedule.coarseChain.state schedule.length =
        schedule.refinedChain.state (schedule.factor schedule.length)) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z := by
  have hfactor_le : schedule.length ≤ schedule.factor schedule.length :=
    strictFactorIndex_le schedule.factor schedule.length
      schedule.factor_zero schedule.factor_strict schedule.length le_rfl
  have hfactor_pos : 0 < schedule.factor schedule.length :=
    schedule.length_pos.trans_le hfactor_le
  refine
    { root := endpoint.root
      leftNodes := schedule.seed
      rightNodes := schedule.refined
      leftChain := schedule.coarseChain
      rightChain := schedule.refinedChain
      leftIndex := schedule.length - 1
      rightIndex := schedule.factor schedule.length - 1
      left_predecessor := schedule.left_predecessor
      right_predecessor := schedule.right_predecessor
      left_next_node := ?_
      right_next_node := ?_
      terminal_eq := ?_ }
  · simpa [Nat.sub_add_cancel schedule.length_pos] using
      schedule.left_terminal_node
  · have hvalue := schedule.factor_value schedule.length le_rfl
    simpa [Nat.sub_add_cancel hfactor_pos] using
      hvalue.trans schedule.left_terminal_node
  · simpa [Nat.sub_add_cancel schedule.length_pos,
      Nat.sub_add_cancel hfactor_pos] using hterminal

/-- Constant curvature supplies two common positive scalar radii for a fixed
realized schedule.  Meeting the first common mesh bound unlocks the second;
meeting the second constructs the common-root terminal transport.  This is
the finite-history minimum result, before any uniformity across changing
refinement stages is requested. -/
theorem exists_commonAdaptiveRadii_commonRootTerminalTransport_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ((∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          dist
              (insertNodeListSchedule
                (factorRefinementStage schedule.seed schedule.refined
                  schedule.factor n) (schedule.factor n)
                (factorGapNodes schedule.refined schedule.factor n) (i + 1)
                  (schedule.factor n + i + 1))
              ((schedule.insertionChain n (i + 1)).state
                (schedule.factor n + i)).anchor < epsilon) →
        ∃ radius > (0 : ℝ),
          ((∀ n : Fin schedule.length,
            ∀ i : Fin
              (factorGapNodes schedule.refined schedule.factor n).length,
              dist
                  (insertNodeListSchedule
                    (factorRefinementStage schedule.seed schedule.refined
                      schedule.factor n) (schedule.factor n)
                    (factorGapNodes schedule.refined schedule.factor n) i
                      (schedule.factor n + i + 1))
                  (insertNodeListSchedule
                    (factorRefinementStage schedule.seed schedule.refined
                      schedule.factor n) (schedule.factor n)
                    (factorGapNodes schedule.refined schedule.factor n) (i + 1)
                      (schedule.factor n + i + 1)) < radius) →
            Nonempty (CommonRootTerminalTransport
              (endpoint.terminalState x) (endpoint.terminalState y) z))) := by
  letI : MetricSpace M := g.toMetricSpace
  have hcert :=
    DifferentialSuccessorAdaptiveFeedbackIteration.ReachableChain.strictFactorCommonRadiusCertificate_of_curvature
      hcurv schedule.seed schedule.refined schedule.length schedule.factor
        schedule.factor_zero schedule.factor_strict schedule.factor_value
        schedule.coarseChain schedule.refinedChain schedule.insertionChain
  rcases hcert with ⟨epsilon, hepsilon, hafterFirst⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hfirst
  rcases hafterFirst hfirst with ⟨radius, hradius, hafterSecond⟩
  refine ⟨radius, hradius, ?_⟩
  intro hsecond
  exact ⟨toCommonRootTerminalTransport_of_terminal_eq schedule
    (hafterSecond hsecond)⟩

/-- The first adaptive radius family chosen from the curvature certificate of
one realized rooted strict-factor schedule. -/
def adaptiveFirstRadius
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      Fin (factorGapNodes schedule.refined schedule.factor n).length → ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose (schedule.strictFactorRadiusCertificate_of_curvature hcurv)

/-- Every chosen first adaptive radius is positive. -/
theorem adaptiveFirstRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
        0 < adaptiveFirstRadius schedule hcurv n i := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (schedule.strictFactorRadiusCertificate_of_curvature hcurv)).1

/-- The concrete first-stage insertion-node tests for the chosen curvature
certificate. -/
def AdaptiveFirstCloseness
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1) : Prop := by
  letI : MetricSpace M := g.toMetricSpace
  exact ∀ n : Fin schedule.length,
    ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
      dist
          (insertNodeListSchedule
            (factorRefinementStage schedule.seed schedule.refined
              schedule.factor n) (schedule.factor n)
            (factorGapNodes schedule.refined schedule.factor n) (i + 1)
              (schedule.factor n + i + 1))
          ((schedule.insertionChain n (i + 1)).state
            (schedule.factor n + i)).anchor <
        adaptiveFirstRadius schedule hcurv n i

/-- After the first tests hold, the curvature certificate supplies the second
positive radius family. -/
def adaptiveSecondRadius
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      Fin (factorGapNodes schedule.refined schedule.factor n).length → ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  have hafterFirst :=
    (Classical.choose_spec
      (schedule.strictFactorRadiusCertificate_of_curvature hcurv)).2
  exact Classical.choose (hafterFirst hfirst)

/-- Every chosen second adaptive radius is positive. -/
theorem adaptiveSecondRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n : Fin schedule.length,
      ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
        0 < adaptiveSecondRadius schedule hcurv hfirst n i := by
  letI : MetricSpace M := g.toMetricSpace
  have hafterFirst :=
    (Classical.choose_spec
      (schedule.strictFactorRadiusCertificate_of_curvature hcurv)).2
  exact (Classical.choose_spec (hafterFirst hfirst)).1

/-- The concrete second-stage old-next-node tests, with their required
dependence on a proof that the first tests succeeded. -/
def AdaptiveSecondCloseness
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv) : Prop := by
  letI : MetricSpace M := g.toMetricSpace
  exact ∀ n : Fin schedule.length,
    ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
      dist
          (insertNodeListSchedule
            (factorRefinementStage schedule.seed schedule.refined
              schedule.factor n) (schedule.factor n)
            (factorGapNodes schedule.refined schedule.factor n) i
              (schedule.factor n + i + 1))
          (insertNodeListSchedule
            (factorRefinementStage schedule.seed schedule.refined
              schedule.factor n) (schedule.factor n)
            (factorGapNodes schedule.refined schedule.factor n) (i + 1)
              (schedule.factor n + i + 1)) <
        adaptiveSecondRadius schedule hcurv hfirst n i

/-- The second-stage defect is exactly the chord from the newly inserted
refined node to the retained right endpoint of the factor gap. -/
theorem secondDefect_eq_refinedChord
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (n : Fin schedule.length)
    (i : Fin (factorGapNodes schedule.refined schedule.factor n).length) :
    letI : MetricSpace M := g.toMetricSpace
    dist
        (insertNodeListSchedule
          (factorRefinementStage schedule.seed schedule.refined
            schedule.factor n) (schedule.factor n)
          (factorGapNodes schedule.refined schedule.factor n) i
            (schedule.factor n + i + 1))
        (insertNodeListSchedule
          (factorRefinementStage schedule.seed schedule.refined
            schedule.factor n) (schedule.factor n)
          (factorGapNodes schedule.refined schedule.factor n) (i + 1)
            (schedule.factor n + i + 1)) =
      dist
        (schedule.refined (schedule.factor (n + 1)))
        (schedule.refined (schedule.factor n + i + 1)) := by
  letI : MetricSpace M := g.toMetricSpace
  rw [oldNextNode_eq_seed_succ schedule n i,
    insertedNode_eq_refined schedule n i,
    schedule.factor_value (n + 1) n.isLt]

/-- A uniform Lipschitz estimate for the complete refined node sequence,
including its final edge from the endpoint path to the overlap point, reduces
all dependent second-stage tests to scalar index-distance inequalities. -/
theorem adaptiveSecondCloseness_of_refined_lipschitz
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv)
    (K : ℝ≥0)
    (hLip :
      letI : MetricSpace M := g.toMetricSpace
      LipschitzWith K schedule.refined)
    (hscalar :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n : Fin schedule.length,
        ∀ i : Fin (factorGapNodes schedule.refined schedule.factor n).length,
          K * dist (schedule.factor (n + 1))
              (schedule.factor n + i + 1) <
            adaptiveSecondRadius schedule hcurv hfirst n i) :
    AdaptiveSecondCloseness schedule hcurv hfirst := by
  letI : MetricSpace M := g.toMetricSpace
  intro n i
  rw [secondDefect_eq_refinedChord schedule n i]
  exact (hLip.dist_le_mul _ _).trans_lt (hscalar n i)

/-- The two actual adaptive closeness stages imply equality of the realized
terminal states. -/
theorem terminal_eq_of_adaptiveCloseness
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv)
    (hsecond : AdaptiveSecondCloseness schedule hcurv hfirst) :
    schedule.coarseChain.state schedule.length =
      schedule.refinedChain.state (schedule.factor schedule.length) := by
  letI : MetricSpace M := g.toMetricSpace
  have hafterFirst :=
    (Classical.choose_spec
      (schedule.strictFactorRadiusCertificate_of_curvature hcurv)).2
  exact (Classical.choose_spec (hafterFirst hfirst)).2 hsecond

/-- The two metric closeness stages therefore construct the concrete rooted
terminal transport, without assuming a state or germ equality. -/
def toCommonRootTerminalTransport_of_adaptiveCloseness
    [CompactSpace M] [ConnectedSpace M]
    (schedule : RootedOverlapStrictFactorSchedule endpoint x y z)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : AdaptiveFirstCloseness schedule hcurv)
    (hsecond : AdaptiveSecondCloseness schedule hcurv hfirst) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z :=
  toCommonRootTerminalTransport_of_terminal_eq schedule
    (terminal_eq_of_adaptiveCloseness schedule hcurv hfirst hsecond)

end RootedOverlapStrictFactorSchedule

/-- Atlas data whose only analytic transport fields are the two adaptive
families of strict metric inequalities. -/
structure RootedPathAdaptiveClosenessAtlasData
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) where
  endpoint : RootedPathContinuedEndpointFamily g
  schedule : ∀ x y z : M,
    z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source →
      RootedOverlapStrictFactorSchedule endpoint x y z
  firstClose : ∀ x y z : M,
    ∀ hz : z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source,
      RootedOverlapStrictFactorSchedule.AdaptiveFirstCloseness
        (schedule x y z hz) hcurv
  secondClose : ∀ x y z : M,
    ∀ hz : z ∈ (endpoint.terminalState x).germ.source ∩
        (endpoint.terminalState y).germ.source,
      RootedOverlapStrictFactorSchedule.AdaptiveSecondCloseness
        (schedule x y z hz) hcurv (firstClose x y z hz)

/-- Adaptive metric closeness on every rooted overlap constructs the existing
realized endpoint-transport atlas interface. -/
def RootedPathAdaptiveClosenessAtlasData.toRealized
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    (data : RootedPathAdaptiveClosenessAtlasData g hcurv) :
    RealizedEndpointTransportAtlasData g where
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
    have transport :=
      RootedOverlapStrictFactorSchedule.toCommonRootTerminalTransport_of_adaptiveCloseness
        (data.schedule x y z hz') hcurv (data.firstClose x y z hz')
          (data.secondClose x y z hz')
    simpa [hx, hy] using transport

/-- Universal rooted adaptive-closeness data supplies the compatible Cartan
atlas, with the remaining gap stated only as finite metric inequalities. -/
theorem compatibleCartanAtlas_of_rootedPathAdaptiveCloseness
    [CompactSpace M] [ConnectedSpace M]
    (data : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        RootedPathAdaptiveClosenessAtlasData g hcurv) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  compatibleCartanAtlas_of_realizedEndpointTransport
    (fun g hcurv ↦ (data g hcurv).toRealized)

end CartanAtlasRootedAdaptiveClosenessTransport
end Poincare
