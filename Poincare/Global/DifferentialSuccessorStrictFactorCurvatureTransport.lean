import Poincare.Global.DifferentialSuccessorStrictFactorInsertionTransport
import Poincare.Global.DifferentialSuccessorPostRealizationRefiningCandidate

/-!
# Constant-curvature transport across strict finite refinements

`DifferentialSuccessorStrictFactorInsertionTransport` turns a strictly
increasing factor map into actual single-node insertions.  This file supplies
the analytic consumer for that schedule.  Constant curvature chooses one
positive radius at every realized predecessor state.  Only after the inserted
anchors meet those first bounds does it choose the second finite radius
family, whose bounds on the old next anchors imply terminal-state transport.

The final theorem attaches this two-stage certificate to the genuinely
refining post-realization homotopy grid.  It does not claim that the grid made
small for an earlier history automatically meets the later, state-dependent
radii: the required inequalities remain explicit and in their true adaptive
quantifier order.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorStrictFactorCurvatureTransport

universe u

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorReachableChainRefinement
open DifferentialSuccessorStrictFactorInsertionTransport
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveGridRefinement
open DifferentialSuccessorPostRealizationMeshCertificate

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- If every factor gap has already been transported across its explicit
insertion block, those block equalities concatenate to the full strict-factor
state transport. -/
theorem ReachableChain.state_eq_of_strict_factor_of_gap_terminal_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (hgap : ∀ n < k,
      (chain n 0).state (k + (e n - n)) =
        (chain n (factorGapNodes refined e n).length).state
          (k + (e n - n) + (factorGapNodes refined e n).length)) :
    coarseChain.state k = refinedChain.state (e k) := by
  have hstage : ∀ n ≤ k,
      coarseChain.state k =
        (chain n 0).state (k + (e n - n)) := by
    intro n hn
    induction n with
    | zero =>
        have hnodes : ∀ j < k,
            seed (j + 1) =
              insertNodeListSchedule
                (factorRefinementStage seed refined e 0) (e 0)
                (factorGapNodes refined e 0) 0 (j + 1) := by
          intro j hj
          simp [heZero]
        simpa [heZero] using
          ReachableChain.state_eq_of_prefix_nodes
            coarseChain (chain 0 0) k hnodes
    | succ n ih =>
        have hnlt : n < k := by omega
        let gap := factorGapNodes refined e n
        let L := k + (e n - n)
        have hblock :
            (chain n 0).state L =
              (chain n gap.length).state (L + gap.length) := by
          simpa [L, gap] using hgap n hnlt
        have hendpointNodes : ∀ j < L + gap.length,
            insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n) gap
                gap.length (j + 1) =
              insertNodeListSchedule
                (factorRefinementStage seed refined e (n + 1)) (e (n + 1))
                (factorGapNodes refined e (n + 1)) 0 (j + 1) := by
          intro j hj
          dsimp [gap]
          simp only [insertNodeListSchedule_length,
            insertNodeListSchedule_zero]
        have hconnect := ReachableChain.state_eq_of_prefix_nodes
          (chain n gap.length) (chain (n + 1) 0)
          (L + gap.length) hendpointNodes
        have hen : n ≤ e n :=
          strictFactorIndex_le e k heZero heStrict n
            (Nat.le_of_lt hnlt)
        have hindex : L + gap.length =
            k + (e (n + 1) - (n + 1)) := by
          dsimp [L, gap]
          rw [factorGapNodes_length]
          have hstrict := heStrict n hnlt
          omega
        calc
          coarseChain.state k = (chain n 0).state L :=
            ih (Nat.le_of_lt hnlt)
          _ = (chain n gap.length).state (L + gap.length) := hblock
          _ = (chain (n + 1) 0).state (L + gap.length) := hconnect
          _ = (chain (n + 1) 0).state
                (k + (e (n + 1) - (n + 1))) := by rw [hindex]
  have hcoarseToTerminal := hstage k le_rfl
  have hkIndex : k ≤ e k :=
    strictFactorIndex_le e k heZero heStrict k le_rfl
  have hcount : k + (e k - k) = e k := by omega
  have hterminalPrefix := factorRefinementStage_factor_prefix
    seed refined e k heZero heStrict heValue
  have hfinalNodes : ∀ j < e k,
      insertNodeListSchedule
          (factorRefinementStage seed refined e k) (e k)
          (factorGapNodes refined e k) 0 (j + 1) = refined (j + 1) := by
    intro j hj
    simp only [insertNodeListSchedule_zero]
    exact hterminalPrefix (j + 1) (by omega)
  have hterminalToRefined := ReachableChain.state_eq_of_prefix_nodes
    (chain k 0) refinedChain (e k) hfinalNodes
  rw [hcount] at hcoarseToTerminal
  exact hcoarseToTerminal.trans hterminalToRefined

/-- Constant curvature supplies two finite dependent radius families for all
single-node insertions encoded by a strict factor map.

The first family is chosen from the already-realized predecessor histories.
Only after every inserted anchor satisfies that family is the second family
chosen.  Meeting the second family then identifies the coarse terminal state
with the refined state at the retained factor index. -/
theorem ReachableChain.exists_strictFactor_radii_state_eq_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon : ∀ n : Fin k,
        Fin (factorGapNodes refined e n).length → ℝ,
      (∀ n : Fin k,
        ∀ i : Fin (factorGapNodes refined e n).length,
          0 < epsilon n i) ∧
      ((∀ n : Fin k,
        ∀ i : Fin (factorGapNodes refined e n).length,
        dist
            (insertNodeListSchedule
              (factorRefinementStage seed refined e n) (e n)
              (factorGapNodes refined e n) (i + 1) (e n + i + 1))
            ((chain n (i + 1)).state (e n + i)).anchor < epsilon n i) →
        ∃ radius : ∀ n : Fin k,
            Fin (factorGapNodes refined e n).length → ℝ,
          (∀ n : Fin k,
            ∀ i : Fin (factorGapNodes refined e n).length,
              0 < radius n i) ∧
          ((∀ n : Fin k,
            ∀ i : Fin (factorGapNodes refined e n).length,
            dist
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) i (e n + i + 1))
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) (i + 1)
                    (e n + i + 1)) < radius n i) →
            coarseChain.state k = refinedChain.state (e k))) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hlocal : ∀ n : Fin k,
      ∃ epsilon : Fin (factorGapNodes refined e n).length → ℝ,
        (∀ i : Fin (factorGapNodes refined e n).length,
          0 < epsilon i) ∧
        ((∀ i : Fin (factorGapNodes refined e n).length,
          dist
              (insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n)
                (factorGapNodes refined e n) (i + 1) (e n + i + 1))
              ((chain n (i + 1)).state (e n + i)).anchor < epsilon i) →
          ∃ radius : Fin (factorGapNodes refined e n).length → ℝ,
            (∀ i : Fin (factorGapNodes refined e n).length,
              0 < radius i) ∧
            ((∀ i : Fin (factorGapNodes refined e n).length,
              dist
                  (insertNodeListSchedule
                    (factorRefinementStage seed refined e n) (e n)
                    (factorGapNodes refined e n) i (e n + i + 1))
                  (insertNodeListSchedule
                    (factorRefinementStage seed refined e n) (e n)
                    (factorGapNodes refined e n) (i + 1)
                      (e n + i + 1)) < radius i) →
              (chain n 0).state (k + (e n - n)) =
                (chain n (factorGapNodes refined e n).length).state
                  (k + (e n - n) +
                    (factorGapNodes refined e n).length))) := by
    intro n
    have hen : (n : ℕ) ≤ e n :=
      strictFactorIndex_le e k heZero heStrict n n.isLt.le
    have hterminal : e n + 1 ≤ k + (e n - n) := by omega
    exact
      ReachableChain.exists_radii_state_eq_after_insertNodeList_of_curvature
        hcurv (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) (chain n)
          (k + (e n - n)) hterminal
  choose epsilon hepsilon hafterInsert using hlocal
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hinsert
  have hsecond : ∀ n : Fin k,
      ∃ radius : Fin (factorGapNodes refined e n).length → ℝ,
        (∀ i : Fin (factorGapNodes refined e n).length,
          0 < radius i) ∧
        ((∀ i : Fin (factorGapNodes refined e n).length,
          dist
              (insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n)
                (factorGapNodes refined e n) i (e n + i + 1))
              (insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n)
                (factorGapNodes refined e n) (i + 1)
                  (e n + i + 1)) < radius i) →
          (chain n 0).state (k + (e n - n)) =
            (chain n (factorGapNodes refined e n).length).state
              (k + (e n - n) +
                (factorGapNodes refined e n).length)) := by
    intro n
    exact hafterInsert n (hinsert n)
  choose radius hradius hafterNext using hsecond
  refine ⟨radius, hradius, ?_⟩
  intro hnext
  apply ReachableChain.state_eq_of_strict_factor_of_gap_terminal_eq
    seed refined k e heZero heStrict heValue coarseChain refinedChain chain
  intro n hn
  let fn : Fin k := ⟨n, hn⟩
  exact hafterNext fn (hnext fn)

/-- The two-stage radius certificate attached to one strict factor schedule.
This abbreviation keeps the post-realization grid theorem readable while its
defining proposition retains every radius and closeness quantifier. -/
def StrictFactorRadiusCertificate
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) (initial : CartanChain.ChainState g)
    (k : ℕ) (e : ℕ → ℕ)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ epsilon : ∀ n : Fin k,
      Fin (factorGapNodes refined e n).length → ℝ,
    (∀ n : Fin k,
      ∀ i : Fin (factorGapNodes refined e n).length,
        0 < epsilon n i) ∧
    ((∀ n : Fin k,
      ∀ i : Fin (factorGapNodes refined e n).length,
      dist
          (insertNodeListSchedule
            (factorRefinementStage seed refined e n) (e n)
            (factorGapNodes refined e n) (i + 1) (e n + i + 1))
          ((chain n (i + 1)).state (e n + i)).anchor < epsilon n i) →
      ∃ radius : ∀ n : Fin k,
          Fin (factorGapNodes refined e n).length → ℝ,
        (∀ n : Fin k,
          ∀ i : Fin (factorGapNodes refined e n).length,
            0 < radius n i) ∧
        ((∀ n : Fin k,
          ∀ i : Fin (factorGapNodes refined e n).length,
          dist
              (insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n)
                (factorGapNodes refined e n) i (e n + i + 1))
              (insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n)
                (factorGapNodes refined e n) (i + 1)
                  (e n + i + 1)) < radius n i) →
          coarseChain.state k = refinedChain.state (e k)))

/-- Constant curvature inhabits the readable strict-factor radius
certificate. -/
theorem ReachableChain.strictFactorRadiusCertificate_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorRadiusCertificate seed refined initial k e coarseChain
      refinedChain chain := by
  letI : MetricSpace M := g.toMetricSpace
  simpa [StrictFactorRadiusCertificate] using
    (ReachableChain.exists_strictFactor_radii_state_eq_of_curvature
      hcurv seed refined k e heZero heStrict heValue coarseChain refinedChain
        chain)

/-- A fixed realized homotopy grid admits a genuinely refining, cover-small
response whose strict factor map carries an adaptive constant-curvature state
transport certificate on every row.

The old-grid disjunction is retained verbatim.  Independently, for every row
`m` and every actual realization of the insertion histories from the old row
`m` to the refined row `e m`, the returned continuation chooses the two
positive radius families from those realized histories.  If their displayed
closeness conditions hold, the old row state at column `k` equals the refined
row state at column `e k`.

The small-edge bounds use the earlier post-realization radius `eta`; they are
not asserted to imply the later state-dependent insertion bounds. -/
theorem exists_postRealization_refining_grid_with_row_transport_certificates_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0) (htmono : Monotone t)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (htstrict : ∀ n < k, t n < t (n + 1))
    (rowChain : ∀ m : Fin (k + 2),
      ReachableChain (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      Data (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (((∀ alternateRowChain : ∀ m : Fin (k + 2),
            ReachableChain (homotopyGridRow F t m) initial,
          (alternateRowChain 0).state (k + 1) =
            (alternateRowChain (Fin.last (k + 1))).state (k + 1)) ∨
        (∃ m : Fin (k + 2), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j)) ∨
        (∃ m : Fin (k + 1), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)))) ∧
      ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
        0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
          Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
          (∀ n, r (e n) = t n) ∧
          (∀ n < k, e n < e (n + 1)) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F r n (m + 1))
              (homotopyGridRow F r n m) < eta) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F r (n + 1) (m + 1))
              (homotopyGridRow F r n (m + 1)) < eta) ∧
          ∀ (m : ℕ)
            (coarseRowChain : ReachableChain
              (homotopyGridRow F t m) initial)
            (refinedRowChain : ReachableChain
              (homotopyGridRow F r (e m)) initial)
            (insertionChain : ∀ n i : ℕ,
              ReachableChain
                (insertNodeListSchedule
                  (factorRefinementStage
                    (homotopyGridRow F t m)
                    (homotopyGridRow F r (e m)) e n)
                  (e n)
                  (factorGapNodes (homotopyGridRow F r (e m)) e n) i)
                initial),
            StrictFactorRadiusCertificate
              (homotopyGridRow F t m) (homotopyGridRow F r (e m))
              initial k e coarseRowChain refinedRowChain insertionChain) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_postRealization_mesh_certificate_and_adapted_candidate_of_curvature
        hcurv F initial hinitial t htzero k htone rowChain rungData
          bottomAtUpper rungAtNext with
    ⟨eta, heta, hcertificate, _candidate, _candidateK,
      _hcandidateZero, _hcandidateMono, _hcandidateOne,
      _hcandidateHorizontal, _hcandidateVertical⟩
  rcases exists_refining_homotopy_grid_adjacent_dist_lt_strict_factor
      g F heta t htzero htmono k htone htstrict with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, heStrict, hhorizontal, hvertical⟩
  refine ⟨eta, heta, hcertificate, r, K, e, hK, hrZero, hrMono, hrOne,
    heMono, heZero, heBound, heValue, heStrict, hhorizontal, hvertical, ?_⟩
  intro m coarseRowChain refinedRowChain insertionChain
  apply ReachableChain.strictFactorRadiusCertificate_of_curvature
    hcurv (homotopyGridRow F t m) (homotopyGridRow F r (e m))
      k e heZero heStrict
  · intro n hn
    simp [homotopyGridRow, heValue]

end DifferentialSuccessorStrictFactorCurvatureTransport
end Poincare
