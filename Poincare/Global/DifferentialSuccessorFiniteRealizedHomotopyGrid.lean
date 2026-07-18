import Poincare.Global.DifferentialSuccessorFiniteAnchorRadius

/-!
# Finite homotopy ladders from realized differential successors

The primitive recursive differential-chain API asks for successor data at
every counterfactual state.  A `ReachableChain`, by contrast, stores only the
data actually used along one trajectory.  This file gives the bounded ladder
and endpoint comparison directly for such realized chains.

All rung and cross-history hypotheses are indexed by their exact finite
support.  In particular, an endpoint comparison through column `N + 1`
requires bottom cells in `Fin (N + 1)` and only the preceding rung cells in
`Fin N`.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorFiniteRealizedHomotopyGrid

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation

/-- Bounded rectangular ladder invariant for realized differential chains.

Only the vertical data at columns `0, ..., N` and the actual bottom/rung
agreements used before the endpoint occur.  No differential data policy over
unreached states is assumed. -/
theorem reachableChains_ladder_invariant_le
    {g : ClosedSmoothRiemannianMetric 3 M}
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (N : ℕ)
    (rungData : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (hbottom : ∀ j : Fin (N + 1),
      CrossHistorySuccessorAgreement
        (lowerChain.state j) (lowerChain.state (j + 1)) (upper (j + 1)))
    (hrung : ∀ j : Fin N,
      CrossHistorySuccessorAgreement
        (lowerChain.state (j + 1))
        (rungData j.castSucc).successor (upper (j + 2))) :
    ∀ (n : ℕ) (hn : n ≤ N),
      upperChain.state (n + 1) =
        (rungData ⟨n, Nat.lt_succ_iff.mpr hn⟩).successor := by
  intro n
  induction n with
  | zero =>
      intro hn
      let j0 : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
      have hzero : upperChain.state 0 = lowerChain.state 0 :=
        upperChain.initial_eq.trans lowerChain.initial_eq.symm
      have hcross : CrossHistorySuccessorAgreement
          (upperChain.state 0) (lowerChain.state 1) (upper 1) := by
        rw [hzero]
        simpa [j0] using hbottom j0
      calc
        upperChain.state (0 + 1) = (upperChain.data 0).successor :=
          upperChain.state_succ 0
        _ = (rungData j0).successor :=
          successor_eq_of_crossHistoryAgreement
            hcross (upperChain.data 0) (rungData j0)
        _ = (rungData ⟨0, Nat.lt_succ_iff.mpr hn⟩).successor := by
          congr
  | succ n ih =>
      intro hn
      have hnlt : n < N := Nat.lt_of_succ_le hn
      have hnle : n ≤ N := hnlt.le
      let j : Fin N := ⟨n, hnlt⟩
      have hit : upperChain.state (n + 1) =
          (rungData j.castSucc).successor := by
        simpa [j] using ih hnle
      have hrung' : CrossHistorySuccessorAgreement
          (lowerChain.state (n + 1)) (upperChain.state (n + 1))
          (upper (n + 2)) := by
        rw [hit]
        simpa [j] using hrung j
      have hcross : CrossHistorySuccessorAgreement
          (upperChain.state (n + 1)) (lowerChain.state (n + 2))
          (upper (n + 2)) := by
        apply hrung'.symm.trans
        simpa [j, Nat.add_assoc] using hbottom j.succ
      calc
        upperChain.state (n.succ + 1) =
            (upperChain.data (n + 1)).successor := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            upperChain.state_succ (n + 1)
        _ = (rungData j.succ).successor :=
          successor_eq_of_crossHistoryAgreement
            hcross (upperChain.data (n + 1)) (rungData j.succ)
        _ =
            (rungData
              ⟨n.succ, Nat.lt_succ_iff.mpr hn⟩).successor := by
          congr

/-- Endpoint comparison for two realized chains across one finite ladder.

The final rung is based at the common endpoint.  Its normal vector is
therefore zero, so the bounded ladder invariant identifies the two reached
endpoint states. -/
theorem reachableChains_endpoint_eq_finite
    {g : ClosedSmoothRiemannianMetric 3 M}
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (N : ℕ)
    (rungData : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (hbottom : ∀ j : Fin (N + 1),
      CrossHistorySuccessorAgreement
        (lowerChain.state j) (lowerChain.state (j + 1)) (upper (j + 1)))
    (hrung : ∀ j : Fin N,
      CrossHistorySuccessorAgreement
        (lowerChain.state (j + 1))
        (rungData j.castSucc).successor (upper (j + 2)))
    (hend : lower (N + 1) = upper (N + 1)) :
    lowerChain.state (N + 1) = upperChain.state (N + 1) := by
  let jN : Fin (N + 1) := Fin.last N
  let b := lowerChain.state (N + 1)
  let d := rungData jN
  have hdzero : d.v = 0 := by
    apply DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq d
    simpa [d, jN] using hend.symm
  have hrungZero : d.successor = b :=
    DifferentialSuccessorZero.successor_eq_of_vector_eq_zero d hdzero
  have hinvariant := reachableChains_ladder_invariant_le
    lowerChain upperChain N rungData hbottom hrung N le_rfl
  calc
    lowerChain.state (N + 1) = b := rfl
    _ = d.successor := hrungZero.symm
    _ = upperChain.state (N + 1) := by
      simpa [d, jN] using hinvariant.symm

/-- Finite metric-ball consumer for two realized chain rows.

Besides the two realized row chains, this theorem asks only for the actual
vertical data and the two finite families of data used to compare histories
at opposite cell vertices. -/
theorem reachableChains_endpoint_eq_of_finite_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (N : ℕ)
    (rungData : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (bottomAtUpper : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state j) (upper (j + 1)))
    (rungAtNext : ∀ j : Fin N,
      DifferentialInducedSuccessor.Data
        (rungData j.castSucc).successor (upper (j + 2)))
    (hend : lower (N + 1) = upper (N + 1))
    (rBottom : Fin (N + 1) → ℝ) (rRung : Fin N → ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ j : Fin (N + 1),
      EqOn (lowerChain.state j).germ (lowerChain.state (j + 1)).germ
        (Metric.ball (lower (j + 1)) (rBottom j))) →
    (∀ j : Fin (N + 1),
      upper (j + 1) ∈ Metric.ball (lower (j + 1)) (rBottom j)) →
    (∀ j : Fin N,
      EqOn (lowerChain.state (j + 1)).germ
        (rungData j.castSucc).successor.germ
        (Metric.ball (upper (j + 1)) (rRung j))) →
    (∀ j : Fin N,
      upper (j + 2) ∈ Metric.ball (upper (j + 1)) (rRung j)) →
    lowerChain.state (N + 1) = upperChain.state (N + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomEq hbottomMem hrungEq hrungMem
  apply reachableChains_endpoint_eq_finite
    lowerChain upperChain N rungData
  · intro j
    exact crossHistorySuccessorAgreement_of_eqOn_open
      (bottomAtUpper j) (rungData j) Metric.isOpen_ball
      (hbottomMem j) (hbottomEq j)
  · intro j
    exact crossHistorySuccessorAgreement_of_eqOn_open
      (bottomAtUpper j.succ) (rungAtNext j) Metric.isOpen_ball
      (hrungMem j) (hrungEq j)
  · exact hend

/-- Curvature gives a common equality-ball radius for all actual successor
steps used by one finite realized ladder.

The input radius `epsilon` is selected after the two realized rows and their
finite cross-cell data have been fixed.  The equality radius `r` is selected
only after the actual successor centers satisfy that input bound.  This
quantifier order deliberately makes no state-uniform mesh claim. -/
theorem exists_common_patch_radius_for_realized_ladder_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (N : ℕ)
    (rungData : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (bottomAtUpper : ∀ j : Fin (N + 1),
      DifferentialInducedSuccessor.Data
        (lowerChain.state j) (upper (j + 1)))
    (rungAtNext : ∀ j : Fin N,
      DifferentialInducedSuccessor.Data
        (rungData j.castSucc).successor (upper (j + 2)))
    (hend : lower (N + 1) = upper (N + 1)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      (∀ j : Fin (N + 1),
        dist (lower (j + 1)) (lowerChain.state j).anchor < epsilon) →
      (∀ j : Fin N,
        dist (upper (j + 1))
          (lowerChain.state (j + 1)).anchor < epsilon) →
      ∃ r > (0 : ℝ),
        (∀ j : Fin (N + 1),
          dist (upper (j + 1)) (lower (j + 1)) < r) →
        (∀ j : Fin N,
          dist (upper (j + 2)) (upper (j + 1)) < r) →
        lowerChain.state (N + 1) = upperChain.state (N + 1) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let Patch := Fin (N + 1) ⊕ Fin N
  let patchState : Patch → CartanChain.ChainState g
    | Sum.inl j => lowerChain.state j
    | Sum.inr j => lowerChain.state (j + 1)
  let center : Patch → M
    | Sum.inl j => lower (j + 1)
    | Sum.inr j => upper (j + 1)
  let x : Patch → M := fun i ↦ (patchState i).anchor
  let p : Patch → RoundSphere3 := fun i ↦ (patchState i).target
  let L : ∀ i : Patch, CartanMap.TangentAlignment g (x i) (p i) :=
    fun i ↦ (patchState i).alignment
  have chainState_eta (s : CartanChain.ChainState g) :
      CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
    cases s
    rfl
  let datum : ∀ i : Patch,
      DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk (x i) (p i) (L i)) (center i) := by
    intro i
    cases i with
    | inl j =>
        change DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk
            (lowerChain.state j).anchor (lowerChain.state j).target
            (lowerChain.state j).alignment) (lower (j + 1))
        rw [chainState_eta]
        exact lowerChain.data j
    | inr j =>
        change DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk
            (lowerChain.state (j + 1)).anchor
            (lowerChain.state (j + 1)).target
            (lowerChain.state (j + 1)).alignment) (upper (j + 1))
        rw [chainState_eta]
        exact rungData j.castSucc
  rcases
      DifferentialSuccessorFiniteAnchorRadius.exists_uniform_distance_radius_and_common_eqOn_ball_for_finite_data
        g hcurv x p with
    ⟨epsilon, hepsilon, hpatch⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hbottomSmall hrungSmall
  have hsmall : ∀ i : Patch, dist (center i) (x i) < epsilon := by
    intro i
    cases i with
    | inl j => simpa [center, x, patchState] using hbottomSmall j
    | inr j => simpa [center, x, patchState] using hrungSmall j
  rcases hpatch L center datum hsmall with ⟨r, hr, hEq⟩
  refine ⟨r, hr, ?_⟩
  intro hbottomOpposite hrungOpposite
  apply reachableChains_endpoint_eq_of_finite_metricBall_patches
    lowerChain upperChain N rungData bottomAtUpper rungAtNext hend
      (fun _ ↦ r) (fun _ ↦ r)
  · intro j
    rw [lowerChain.state_succ j]
    simpa [x, p, L, center, patchState, datum] using hEq (Sum.inl j)
  · intro j
    rw [Metric.mem_ball]
    exact hbottomOpposite j
  · intro j
    have h := hEq (Sum.inr j)
    change EqOn
      (CartanChain.ChainState.mk
        (lowerChain.state (j + 1)).anchor
        (lowerChain.state (j + 1)).target
        (lowerChain.state (j + 1)).alignment).germ
      (rungData j.castSucc).successor.germ
      (Metric.ball (upper (j + 1)) r) at h
    rw [chainState_eta] at h
    exact h
  · intro j
    rw [Metric.mem_ball]
    exact hrungOpposite j

/-- Finite row induction for a realized differential homotopy grid.

The input contains exactly the `k + 2` realized row chains participating in
the comparison.  For each of the `k + 1` adjacent row pairs, one radius is
shared by all bottom and rung patches in that ladder.  No successor policy on
unreached states, and no state-uniform radius beyond this fixed finite grid,
is assumed. -/
theorem reachableHomotopyGridChains_endpoint_eq_of_finite_common_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M} {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (t : ℕ → unitInterval)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2)))
    (radius : Fin (k + 1) → ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      EqOn
        ((rowChain m.castSucc).state j).germ
        ((rowChain m.castSucc).state (j + 1)).germ
        (Metric.ball
          (homotopyGridRow F t m (j + 1)) (radius m))) →
    (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      homotopyGridRow F t (m + 1) (j + 1) ∈
        Metric.ball
          (homotopyGridRow F t m (j + 1)) (radius m)) →
    (∀ m : Fin (k + 1), ∀ j : Fin k,
      EqOn
        ((rowChain m.castSucc).state (j + 1)).germ
        (rungData m j.castSucc).successor.germ
        (Metric.ball
          (homotopyGridRow F t (m + 1) (j + 1)) (radius m))) →
    (∀ m : Fin (k + 1), ∀ j : Fin k,
      homotopyGridRow F t (m + 1) (j + 2) ∈
        Metric.ball
          (homotopyGridRow F t (m + 1) (j + 1)) (radius m)) →
    (rowChain 0).state (k + 1) =
      (rowChain (Fin.last (k + 1))).state (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomEq hbottomMem hrungEq hrungMem
  have hk_le : k ≤ k + 1 := Nat.le_add_right k 1
  have htK : t (k + 1) = 1 := htone (k + 1) hk_le
  have hadj : ∀ m : Fin (k + 1),
      (rowChain m.castSucc).state (k + 1) =
        (rowChain m.succ).state (k + 1) := by
    intro m
    apply reachableChains_endpoint_eq_of_finite_metricBall_patches
      (rowChain m.castSucc) (rowChain m.succ) k
      (rungData m) (bottomAtUpper m) (rungAtNext m)
      (by
        simp only [homotopyGridRow, htK]
        exact (F.target (t m)).trans (F.target (t (m + 1))).symm)
      (fun _ ↦ radius m) (fun _ ↦ radius m)
    · intro j
      simpa using hbottomEq m j
    · intro j
      simpa using hbottomMem m j
    · intro j
      simpa using hrungEq m j
    · intro j
      simpa using hrungMem m j
  have hiterate : ∀ n : ℕ, ∀ hn : n ≤ k + 1,
      (rowChain 0).state (k + 1) =
        (rowChain ⟨n, Nat.lt_succ_iff.mpr hn⟩).state (k + 1) := by
    intro n
    induction n with
    | zero =>
        intro _hn
        congr
    | succ n ih =>
        intro hn
        have hnle : n ≤ k := Nat.le_of_succ_le_succ hn
        let m : Fin (k + 1) :=
          ⟨n, Nat.lt_succ_iff.mpr hnle⟩
        calc
          (rowChain 0).state (k + 1) =
              (rowChain m.castSucc).state (k + 1) := by
            simpa [m] using ih (hnle.trans hk_le)
          _ = (rowChain m.succ).state (k + 1) := hadj m
          _ =
              (rowChain
                ⟨n + 1, Nat.lt_succ_iff.mpr hn⟩).state (k + 1) := by
            congr
  simpa using hiterate (k + 1) le_rfl

/-- Constant curvature supplies post-realization patch radii for a fixed
finite realized homotopy grid.

The predecessor-distance bounds `epsilon m` are chosen only after all row
chains and cross-cell data have been fixed.  After the actual successor
centers satisfy those bounds, a common equality radius `radius m` is selected
for each adjacent row pair.  Only then are the opposite-vertex distance
bounds requested.  Thus this theorem does not claim that a homotopy mesh can
be chosen before the recursively reached states and their local radii are
known. -/
theorem exists_perRow_patch_radii_for_realized_homotopyGrid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (t : ℕ → unitInterval)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon : Fin (k + 1) → ℝ,
      (∀ m : Fin (k + 1), 0 < epsilon m) ∧
      ((∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t m (j + 1))
            ((rowChain m.castSucc).state j).anchor < epsilon m) →
        (∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 1))
            ((rowChain m.castSucc).state (j + 1)).anchor < epsilon m) →
        ∃ radius : Fin (k + 1) → ℝ,
          (∀ m : Fin (k + 1), 0 < radius m) ∧
          ((∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
              dist (homotopyGridRow F t (m + 1) (j + 1))
                (homotopyGridRow F t m (j + 1)) < radius m) →
            (∀ m : Fin (k + 1), ∀ j : Fin k,
              dist (homotopyGridRow F t (m + 1) (j + 2))
                (homotopyGridRow F t (m + 1) (j + 1)) < radius m) →
            (rowChain 0).state (k + 1) =
              (rowChain (Fin.last (k + 1))).state (k + 1))) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let Patch := Fin (k + 1) ⊕ Fin k
  let patchState : Fin (k + 1) → Patch → CartanChain.ChainState g
    | m, Sum.inl j => (rowChain m.castSucc).state j
    | m, Sum.inr j => (rowChain m.castSucc).state (j + 1)
  let sourceAnchor : Fin (k + 1) → Patch → M := fun m i ↦
    (patchState m i).anchor
  let targetAnchor : Fin (k + 1) → Patch → RoundSphere3 := fun m i ↦
    (patchState m i).target
  let center : Fin (k + 1) → Patch → M
    | m, Sum.inl j => homotopyGridRow F t m (j + 1)
    | m, Sum.inr j => homotopyGridRow F t (m + 1) (j + 1)
  let L : ∀ (m : Fin (k + 1)) (i : Patch),
      CartanMap.TangentAlignment g (sourceAnchor m i) (targetAnchor m i) :=
    fun m i ↦ (patchState m i).alignment
  have chainState_eta (s : CartanChain.ChainState g) :
      CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
    cases s
    rfl
  let datum : ∀ (m : Fin (k + 1)) (i : Patch),
      DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk
          (sourceAnchor m i) (targetAnchor m i) (L m i))
        (center m i) := by
    intro m i
    cases i with
    | inl j =>
        change DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk
            ((rowChain m.castSucc).state j).anchor
            ((rowChain m.castSucc).state j).target
            ((rowChain m.castSucc).state j).alignment)
          (homotopyGridRow F t m (j + 1))
        rw [chainState_eta]
        exact (rowChain m.castSucc).data j
    | inr j =>
        change DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk
            ((rowChain m.castSucc).state (j + 1)).anchor
            ((rowChain m.castSucc).state (j + 1)).target
            ((rowChain m.castSucc).state (j + 1)).alignment)
          (homotopyGridRow F t (m + 1) (j + 1))
        rw [chainState_eta]
        exact rungData m j.castSucc
  have hperRow : ∀ m : Fin (k + 1),
      ∃ epsilon > (0 : ℝ),
        ∀ (Lm : ∀ i : Patch,
            CartanMap.TangentAlignment g
              (sourceAnchor m i) (targetAnchor m i))
          (z : Patch → M)
          (d : ∀ i : Patch,
            DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk
                (sourceAnchor m i) (targetAnchor m i) (Lm i))
              (z i)),
          (∀ i : Patch, dist (z i) (sourceAnchor m i) < epsilon) →
            ∃ r > (0 : ℝ), ∀ i : Patch,
              EqOn
                (CartanChain.ChainState.mk
                  (sourceAnchor m i) (targetAnchor m i) (Lm i)).germ
                (d i).successor.germ (Metric.ball (z i) r) := by
    intro m
    exact
      DifferentialSuccessorFiniteAnchorRadius.exists_uniform_distance_radius_and_common_eqOn_ball_for_finite_data
        g hcurv (sourceAnchor m) (targetAnchor m)
  choose epsilon hepsilon hpatch using hperRow
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hbottomSmall hrungSmall
  have hsmall : ∀ (m : Fin (k + 1)) (i : Patch),
      dist (center m i) (sourceAnchor m i) < epsilon m := by
    intro m i
    cases i with
    | inl j =>
        simpa [center, sourceAnchor, patchState] using hbottomSmall m j
    | inr j =>
        simpa [center, sourceAnchor, patchState] using hrungSmall m j
  have hrowEq : ∀ m : Fin (k + 1), ∃ r > (0 : ℝ), ∀ i : Patch,
      EqOn
        (CartanChain.ChainState.mk
          (sourceAnchor m i) (targetAnchor m i) (L m i)).germ
        (datum m i).successor.germ (Metric.ball (center m i) r) := by
    intro m
    exact hpatch m (L m) (center m) (datum m) (hsmall m)
  choose radius hradius hEq using hrowEq
  refine ⟨radius, hradius, ?_⟩
  intro hbottomOpposite hrungOpposite
  apply
    reachableHomotopyGridChains_endpoint_eq_of_finite_common_metricBall_patches
      F initial t k htone rowChain rungData bottomAtUpper rungAtNext radius
  · intro m j
    rw [(rowChain m.castSucc).state_succ j]
    simpa [sourceAnchor, targetAnchor, L, center, patchState, datum] using
      hEq m (Sum.inl j)
  · intro m j
    rw [Metric.mem_ball]
    exact hbottomOpposite m j
  · intro m j
    have h := hEq m (Sum.inr j)
    change EqOn
      (CartanChain.ChainState.mk
        ((rowChain m.castSucc).state (j + 1)).anchor
        ((rowChain m.castSucc).state (j + 1)).target
        ((rowChain m.castSucc).state (j + 1)).alignment).germ
      (rungData m j.castSucc).successor.germ
      (Metric.ball (homotopyGridRow F t (m + 1) (j + 1)) (radius m)) at h
    rw [chainState_eta] at h
    exact h
  · intro m j
    rw [Metric.mem_ball]
    exact hrungOpposite m j

end DifferentialSuccessorFiniteRealizedHomotopyGrid
end Poincare
