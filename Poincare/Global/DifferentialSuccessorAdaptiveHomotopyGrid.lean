import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.DifferentialSuccessorIntervalNaturalityFiniteFamily

/-!
# Finite adaptive grids for differential-successor homotopy continuation

The row-indexed differential homotopy theorem is driven by equality balls
whose radii depend on the recursively generated chain histories.  This file
extracts the genuinely finite interface hidden in that theorem.

For an endpoint comparison at column `N + 1`, bottom patches are consumed only
for `j ≤ N`, while rung patches are consumed only for `j < N`.  Likewise, a
homotopy comparison ending at row `k + 1` uses only the adjacent row pairs
`m ≤ k`.  Once local equality balls have been produced for those finitely many
recursive states, their radii have a positive finite minimum.  Consequently a
single mesh inequality discharges every opposite-vertex membership premise.

This is fixed-point compatible in the precise finite sense: the local patches
may be generated after the finite recursive histories are known, and the
consumer remembers only one common positive mesh bound.  Constructing the
grid without any further hypothesis still requires a uniform lower bound (or
lower-semicontinuity on a compact space) for the equality radii over all
reachable continuation states; compactness of the manifold alone does not
provide that state-space uniformity.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorAdaptiveHomotopyGrid

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation

/-- Finite form of the differential ladder invariant.

To identify the invariant through column `N + 1`, bottom comparisons are
needed at `0, ..., N`, whereas rung comparisons are needed only at
`0, ..., N - 1`.  No hypotheses about the stationary tail of an encoded
subdivision are used. -/
theorem differentialChain_ladder_invariant_le
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (N : ℕ)
    (hbottom : ∀ j : ℕ, j ≤ N →
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j)
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (upper (j + 1)))
    (hrung : ∀ j : ℕ, j < N →
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (DifferentialInducedSuccessor.successorOfNonempty
          (DifferentialInducedSuccessor.Chain.chainState
            lower initial stepLower (j + 1))
          (upper (j + 1))
          (stepUpper j
            (DifferentialInducedSuccessor.Chain.chainState
              lower initial stepLower (j + 1))))
        (upper (j + 2))) :
    ∀ n : ℕ, n ≤ N →
      DifferentialInducedSuccessor.Chain.chainState
          upper initial stepUpper (n + 1) =
        DifferentialInducedSuccessor.successorOfNonempty
          (DifferentialInducedSuccessor.Chain.chainState
            lower initial stepLower (n + 1))
          (upper (n + 1))
          (stepUpper n
            (DifferentialInducedSuccessor.Chain.chainState
              lower initial stepLower (n + 1))) := by
  intro n
  induction n with
  | zero =>
      intro _hzero
      change
        DifferentialInducedSuccessor.successorOfNonempty initial (upper 1)
            (stepUpper 0 initial) =
          DifferentialInducedSuccessor.successorOfNonempty
            (DifferentialInducedSuccessor.Chain.chainState
              lower initial stepLower 1)
            (upper 1)
            (stepUpper 0
              (DifferentialInducedSuccessor.Chain.chainState
                lower initial stepLower 1))
      exact successorOfNonempty_eq_of_crossHistoryAgreement
        (stepUpper 0 initial)
        (stepUpper 0
          (DifferentialInducedSuccessor.Chain.chainState
            lower initial stepLower 1))
        (by simpa using hbottom 0 (Nat.zero_le N))
  | succ n ih =>
      intro hn
      have hnlt : n < N := Nat.lt_of_succ_le hn
      have hnle : n ≤ N := hnlt.le
      let b₁ := DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (n + 1)
      let b₂ := DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (n + 2)
      let t₁ := DifferentialInducedSuccessor.Chain.chainState
        upper initial stepUpper (n + 1)
      let rung₁ := DifferentialInducedSuccessor.successorOfNonempty
        b₁ (upper (n + 1)) (stepUpper n b₁)
      have hit : t₁ = rung₁ := by
        simpa [b₁, t₁, rung₁] using ih hnle
      have hrung' : CrossHistorySuccessorAgreement
          b₁ t₁ (upper (n + 2)) := by
        rw [hit]
        simpa [b₁, rung₁] using hrung n hnlt
      calc
        DifferentialInducedSuccessor.Chain.chainState
            upper initial stepUpper (n.succ + 1) =
            DifferentialInducedSuccessor.successorOfNonempty
              t₁ (upper (n + 2)) (stepUpper (n + 1) t₁) := by
          simpa [t₁, Nat.succ_eq_add_one, Nat.add_assoc] using
            DifferentialInducedSuccessor.Chain.chainState_succ
              upper initial stepUpper (n + 1)
        _ = DifferentialInducedSuccessor.successorOfNonempty
              b₁ (upper (n + 2)) (stepUpper (n + 1) b₁) :=
          successorOfNonempty_eq_of_crossHistoryAgreement
            (stepUpper (n + 1) t₁) (stepUpper (n + 1) b₁)
            hrung'.symm
        _ = DifferentialInducedSuccessor.successorOfNonempty
              b₂ (upper (n + 2)) (stepUpper (n + 1) b₂) :=
          successorOfNonempty_eq_of_crossHistoryAgreement
            (stepUpper (n + 1) b₁) (stepUpper (n + 1) b₂)
            (by simpa [b₁, b₂] using hbottom (n + 1) hn)
        _ = DifferentialInducedSuccessor.successorOfNonempty
              (DifferentialInducedSuccessor.Chain.chainState
                lower initial stepLower (n.succ + 1))
              (upper (n.succ + 1))
              (stepUpper n.succ
                (DifferentialInducedSuccessor.Chain.chainState
                  lower initial stepLower (n.succ + 1))) := by
          simp only [b₂, Nat.succ_eq_add_one, Nat.add_assoc]

/-- Finite endpoint comparison for two differential-induced chains.

This is the exact bounded-index replacement for
`differentialChains_endpoint_eq`: it consumes no cross-history data beyond the
last column participating in the comparison. -/
theorem differentialChains_endpoint_eq_finite
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (N : ℕ)
    (hbottom : ∀ j : ℕ, j ≤ N →
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j)
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (upper (j + 1)))
    (hrung : ∀ j : ℕ, j < N →
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (DifferentialInducedSuccessor.successorOfNonempty
          (DifferentialInducedSuccessor.Chain.chainState
            lower initial stepLower (j + 1))
          (upper (j + 1))
          (stepUpper j
            (DifferentialInducedSuccessor.Chain.chainState
              lower initial stepLower (j + 1))))
        (upper (j + 2)))
    (hend : lower (N + 1) = upper (N + 1)) :
    DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (N + 1) =
      DifferentialInducedSuccessor.Chain.chainState
        upper initial stepUpper (N + 1) := by
  let b := DifferentialInducedSuccessor.Chain.chainState
    lower initial stepLower (N + 1)
  let d : DifferentialInducedSuccessor.Data b (upper (N + 1)) :=
    Classical.choice (stepUpper N b)
  have hbAnchor : b.anchor = lower (N + 1) := by
    simpa [b] using
      differentialChain_chainState_succ_anchor
        lower initial stepLower N
  have hdAtAnchor : upper (N + 1) = b.anchor :=
    hend.symm.trans hbAnchor.symm
  have hdzero : d.v = 0 :=
    DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq d hdAtAnchor
  have hrungZero :
      DifferentialInducedSuccessor.successorOfNonempty
          b (upper (N + 1)) (stepUpper N b) = b := by
    calc
      DifferentialInducedSuccessor.successorOfNonempty
          b (upper (N + 1)) (stepUpper N b) = d.successor :=
        DifferentialInducedSuccessor.successorOfNonempty_eq
          (stepUpper N b) d
      _ = b :=
        DifferentialSuccessorZero.successor_eq_of_vector_eq_zero d hdzero
  have hinvariant := differentialChain_ladder_invariant_le
    initial lower upper stepLower stepUpper N hbottom hrung N le_rfl
  calc
    DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (N + 1) = b := rfl
    _ = DifferentialInducedSuccessor.successorOfNonempty
          b (upper (N + 1)) (stepUpper N b) := hrungZero.symm
    _ = DifferentialInducedSuccessor.Chain.chainState
          upper initial stepUpper (N + 1) := by
      simpa [b] using hinvariant.symm

/-- Finite metric-ball consumer for two chain rows.

The index types record the exact support: `Fin (N + 1)` for bottom patches and
`Fin N` for rung patches. -/
theorem differentialChains_endpoint_eq_of_finite_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (N : ℕ) (hend : lower (N + 1) = upper (N + 1))
    (rBottom : Fin (N + 1) → ℝ) (rRung : Fin N → ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ j : Fin (N + 1),
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j).germ
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1)).germ
        (Metric.ball (lower (j + 1)) (rBottom j))) →
    (∀ j : Fin (N + 1),
      upper (j + 1) ∈ Metric.ball (lower (j + 1)) (rBottom j)) →
    (∀ j : Fin N,
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1)).germ
        (DifferentialInducedSuccessor.successorOfNonempty
          (DifferentialInducedSuccessor.Chain.chainState
            lower initial stepLower (j + 1))
          (upper (j + 1))
          (stepUpper j
            (DifferentialInducedSuccessor.Chain.chainState
              lower initial stepLower (j + 1)))).germ
        (Metric.ball (upper (j + 1)) (rRung j))) →
    (∀ j : Fin N,
      upper (j + 2) ∈ Metric.ball (upper (j + 1)) (rRung j)) →
    DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (N + 1) =
      DifferentialInducedSuccessor.Chain.chainState
        upper initial stepUpper (N + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomEq hbottomMem hrungEq hrungMem
  apply differentialChains_endpoint_eq_finite
    initial lower upper stepLower stepUpper N
  · intro j hj
    let jf : Fin (N + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
    let b₀ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower j
    let b₁ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower (j + 1)
    let d₀ : DifferentialInducedSuccessor.Data b₀ (upper (j + 1)) :=
      Classical.choice (stepUpper j b₀)
    let d₁ : DifferentialInducedSuccessor.Data b₁ (upper (j + 1)) :=
      Classical.choice (stepUpper j b₁)
    exact crossHistorySuccessorAgreement_of_eqOn_open
      d₀ d₁ Metric.isOpen_ball (by simpa [jf] using hbottomMem jf)
      (by simpa [b₀, b₁, jf] using hbottomEq jf)
  · intro j hj
    let jf : Fin N := ⟨j, hj⟩
    let b₁ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower (j + 1)
    let rung := DifferentialInducedSuccessor.successorOfNonempty
      b₁ (upper (j + 1)) (stepUpper j b₁)
    let d₁ : DifferentialInducedSuccessor.Data b₁ (upper (j + 2)) :=
      Classical.choice (stepUpper (j + 1) b₁)
    let dr : DifferentialInducedSuccessor.Data rung (upper (j + 2)) :=
      Classical.choice (stepUpper (j + 1) rung)
    exact crossHistorySuccessorAgreement_of_eqOn_open
      d₁ dr Metric.isOpen_ball (by simpa [jf] using hrungMem jf)
      (by simpa [b₁, rung, jf] using hrungEq jf)
  · exact hend

/-- Finite-support row-indexed homotopy comparison.

Only the adjacent row pairs `m : Fin (k + 1)`, bottom columns
`j : Fin (k + 1)`, and rung columns `j : Fin k` occur. -/
theorem differentialHomotopyGrid_chain_endpoint_eq_of_finite_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M} {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (t : ℕ → unitInterval)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rBottom : Fin (k + 1) → Fin (k + 1) → ℝ)
    (rRung : Fin (k + 1) → Fin k → ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) j).germ
        (DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) (j + 1)).germ
        (Metric.ball
          (homotopyGridRow F t m (j + 1)) (rBottom m j))) →
    (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      homotopyGridRow F t (m + 1) (j + 1) ∈
        Metric.ball
          (homotopyGridRow F t m (j + 1)) (rBottom m j)) →
    (∀ m : Fin (k + 1), ∀ j : Fin k,
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) (j + 1)).germ
        (DifferentialInducedSuccessor.successorOfNonempty
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) (j + 1))
          (homotopyGridRow F t (m + 1) (j + 1))
          (step (m + 1) j
            (DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t m) initial (step m) (j + 1)))).germ
        (Metric.ball
          (homotopyGridRow F t (m + 1) (j + 1)) (rRung m j))) →
    (∀ m : Fin (k + 1), ∀ j : Fin k,
      homotopyGridRow F t (m + 1) (j + 2) ∈
        Metric.ball
          (homotopyGridRow F t (m + 1) (j + 1)) (rRung m j)) →
    DifferentialInducedSuccessor.Chain.chainState
        (homotopyGridRow F t 0) initial (step 0) (k + 1) =
      DifferentialInducedSuccessor.Chain.chainState
        (homotopyGridRow F t (k + 1)) initial (step (k + 1))
          (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomEq hbottomMem hrungEq hrungMem
  let endpointState : ℕ → CartanChain.ChainState g := fun m ↦
    DifferentialInducedSuccessor.Chain.chainState
      (homotopyGridRow F t m) initial (step m) (k + 1)
  have hk_le : k ≤ k + 1 := Nat.le_add_right k 1
  have htK : t (k + 1) = 1 := htone (k + 1) hk_le
  have hadj : ∀ m : ℕ, m ≤ k → endpointState m = endpointState (m + 1) := by
    intro m hm
    let mf : Fin (k + 1) := ⟨m, Nat.lt_succ_iff.mpr hm⟩
    refine differentialChains_endpoint_eq_of_finite_metricBall_patches
      initial (homotopyGridRow F t m) (homotopyGridRow F t (m + 1))
      (step m) (step (m + 1)) k ?_
      (rBottom mf) (rRung mf)
      (by intro j; simpa [mf] using hbottomEq mf j)
      (by intro j; simpa [mf] using hbottomMem mf j)
      (by intro j; simpa [mf] using hrungEq mf j)
      (by intro j; simpa [mf] using hrungMem mf j)
    simp only [homotopyGridRow, htK]
    exact (F.target (t m)).trans (F.target (t (m + 1))).symm
  have hiterate : ∀ m : ℕ, m ≤ k + 1 →
      endpointState 0 = endpointState m := by
    intro m
    induction m with
    | zero =>
        intro _hzero
        rfl
    | succ m ih =>
        intro hm
        have hmle : m ≤ k := Nat.le_of_succ_le_succ hm
        exact (ih (hmle.trans hk_le)).trans
          (by simpa [Nat.succ_eq_add_one] using hadj m hmle)
  simpa [endpointState] using hiterate (k + 1) le_rfl

/-- An open local differential-successor equality seed contains a positive
metric ball about the successor anchor on which the two germs agree outright. -/
private theorem exists_metricBall_eqOn_of_local_eqOn_differentialSuccessor
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {z : M}
    (d : DifferentialInducedSuccessor.Data s z) :
    letI : MetricSpace M := g.toMetricSpace
    ∀ {V : Set M}, IsOpen V → z ∈ V →
      EqOn s.germ d.successor.germ
        (V ∩ (s.germ.source ∩ d.successor.germ.source)) →
      ∃ r > (0 : ℝ),
        EqOn s.germ d.successor.germ (Metric.ball z r) := by
  letI : MetricSpace M := g.toMetricSpace
  intro V hVopen hzV hlocal
  have hzOld : z ∈ s.germ.source := d.anchor_mem_predecessor_source
  have hzNew : z ∈ d.successor.germ.source := by
    simpa [DifferentialInducedSuccessor.Data.successor] using
      CartanAdjacentContinuation.chainAdjacent_anchor_mem_successor_source
        s z d.alignment
  have hopen : IsOpen
      (V ∩ (s.germ.source ∩ d.successor.germ.source)) :=
    hVopen.inter (s.germ.open_source.inter d.successor.germ.open_source)
  have hz : z ∈ V ∩ (s.germ.source ∩ d.successor.germ.source) :=
    ⟨hzV, hzOld, hzNew⟩
  rcases (Metric.isOpen_iff.mp hopen) z hz with ⟨r, hr, hball⟩
  exact ⟨r, hr, fun _q hq ↦ hlocal (hball hq)⟩

/-- Finite local equality patches have one common positive mesh radius.

The patch hypotheses are existential and are indexed by the actual recursive
chain histories on the chosen finite grid.  The proof selects those patches,
takes the minimum over the exact finite support, and turns two uniform distance
bounds into all opposite-vertex ball memberships needed by the finite row
comparison. -/
theorem exists_mesh_radius_for_recursive_local_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M} {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (t : ℕ → unitInterval)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      ∃ r > (0 : ℝ),
        EqOn
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) j).germ
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) (j + 1)).germ
          (Metric.ball (homotopyGridRow F t m (j + 1)) r)) →
    (∀ m : Fin (k + 1), ∀ j : Fin k,
      ∃ r > (0 : ℝ),
        EqOn
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) (j + 1)).germ
          (DifferentialInducedSuccessor.successorOfNonempty
            (DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t m) initial (step m) (j + 1))
            (homotopyGridRow F t (m + 1) (j + 1))
            (step (m + 1) j
              (DifferentialInducedSuccessor.Chain.chainState
                (homotopyGridRow F t m) initial (step m) (j + 1)))).germ
          (Metric.ball (homotopyGridRow F t (m + 1) (j + 1)) r)) →
    ∃ δ > (0 : ℝ),
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < δ) →
      (∀ m : Fin (k + 1), ∀ j : Fin k,
        dist (homotopyGridRow F t (m + 1) (j + 2))
          (homotopyGridRow F t (m + 1) (j + 1)) < δ) →
      DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t 0) initial (step 0) (k + 1) =
        DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t (k + 1)) initial (step (k + 1))
            (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomLocal hrungLocal
  choose rBottom hrBottomPos hbottomEq using hbottomLocal
  choose rRung hrRungPos hrungEq using hrungLocal
  let radius :
      ((Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin k)) → ℝ
    | Sum.inl i => rBottom i.1 i.2
    | Sum.inr i => rRung i.1 i.2
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hδ : 0 < δ := by
    dsimp [δ]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    cases i with
    | inl i => exact hrBottomPos i.1 i.2
    | inr i => exact hrRungPos i.1 i.2
  have hδBottom : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      δ ≤ rBottom m j := by
    intro m j
    dsimp [δ]
    exact Finset.inf'_le radius (Finset.mem_univ (Sum.inl (m, j)))
  have hδRung : ∀ m : Fin (k + 1), ∀ j : Fin k,
      δ ≤ rRung m j := by
    intro m j
    dsimp [δ]
    exact Finset.inf'_le radius (Finset.mem_univ (Sum.inr (m, j)))
  refine ⟨δ, hδ, ?_⟩
  intro hbottomMesh hrungMesh
  apply
    differentialHomotopyGrid_chain_endpoint_eq_of_finite_metricBall_patches
      F initial t step k htone rBottom rRung hbottomEq
  · intro m j
    rw [Metric.mem_ball]
    exact (hbottomMesh m j).trans_le (hδBottom m j)
  · exact hrungEq
  · intro m j
    rw [Metric.mem_ball]
    exact (hrungMesh m j).trans_le (hδRung m j)

/--
Curvature automatically supplies every local equality patch used by a fixed
finite recursive homotopy grid, provided the actual bottom and rung successor
coordinates lie in the common finite-family predecessor radius.  After those
two finite coordinate bounds, only the two mesh-distance families remain.
-/
theorem exists_mesh_radius_for_recursive_grid_of_curvature_and_small_successors
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (t : ℕ → unitInterval)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ rho > (0 : ℝ),
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        ‖(Classical.choice
          (step m j
            (DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t m) initial (step m) j))).v‖ < rho) →
      (∀ m : Fin (k + 1), ∀ j : Fin k,
        ‖(Classical.choice
          (step (m + 1) j
            (DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t m) initial (step m) (j + 1)))).v‖ < rho) →
      ∃ δ > (0 : ℝ),
        (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) < δ) →
        (∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 2))
            (homotopyGridRow F t (m + 1) (j + 1)) < δ) →
        DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t 0) initial (step 0) (k + 1) =
          DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t (k + 1)) initial (step (k + 1))
              (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  let patchState :
      ((Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin k)) →
        CartanChain.ChainState g
    | Sum.inl mj =>
        DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t mj.1) initial (step mj.1) mj.2
    | Sum.inr mj =>
        DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t mj.1) initial (step mj.1) (mj.2 + 1)
  rcases
      DifferentialSuccessorIntervalNaturalityFiniteFamily.exists_uniform_local_eqOn_differentialSuccessor_all_on_finite_family
        (ι :=
          (Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin k))
        g hcurv (fun i ↦ (patchState i).anchor)
          (fun i ↦ (patchState i).target) with
    ⟨rho, hrho, hlocal⟩
  refine ⟨rho, hrho, ?_⟩
  intro hbottomSmall hrungSmall
  apply exists_mesh_radius_for_recursive_local_patches
    F initial t step k htone
  · intro m j
    let b := DifferentialInducedSuccessor.Chain.chainState
      (homotopyGridRow F t m) initial (step m) j
    let hstep := step m j b
    let d : DifferentialInducedSuccessor.Data b
        (homotopyGridRow F t m (j + 1)) := Classical.choice hstep
    have hdSmall : ‖d.v‖ < rho := by
      simpa [b, hstep, d] using hbottomSmall m j
    rcases hlocal (Sum.inl (m, j)) b.alignment d
        (by simpa [patchState, b] using hdSmall) with
      ⟨V, hVopen, hzV, hEq⟩
    rcases exists_metricBall_eqOn_of_local_eqOn_differentialSuccessor
        b d hVopen hzV hEq with ⟨r, hr, hEqBall⟩
    refine ⟨r, hr, ?_⟩
    have hsucc : d.successor =
        DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) (j + 1) := by
      calc
        d.successor =
            DifferentialInducedSuccessor.successorOfNonempty b
              (homotopyGridRow F t m (j + 1)) hstep :=
          (DifferentialInducedSuccessor.successorOfNonempty_eq hstep d).symm
        _ = DifferentialInducedSuccessor.Chain.chainState
              (homotopyGridRow F t m) initial (step m) (j + 1) := by
          simpa [b, hstep] using
            (DifferentialInducedSuccessor.Chain.chainState_succ
              (homotopyGridRow F t m) initial (step m) j).symm
    simpa [b, hsucc] using hEqBall
  · intro m j
    let b := DifferentialInducedSuccessor.Chain.chainState
      (homotopyGridRow F t m) initial (step m) (j + 1)
    let hstep := step (m + 1) j b
    let d : DifferentialInducedSuccessor.Data b
        (homotopyGridRow F t (m + 1) (j + 1)) := Classical.choice hstep
    have hdSmall : ‖d.v‖ < rho := by
      simpa [b, hstep, d] using hrungSmall m j
    rcases hlocal (Sum.inr (m, j)) b.alignment d
        (by simpa [patchState, b] using hdSmall) with
      ⟨V, hVopen, hzV, hEq⟩
    rcases exists_metricBall_eqOn_of_local_eqOn_differentialSuccessor
        b d hVopen hzV hEq with ⟨r, hr, hEqBall⟩
    refine ⟨r, hr, ?_⟩
    have hsucc : d.successor =
        DifferentialInducedSuccessor.successorOfNonempty b
          (homotopyGridRow F t (m + 1) (j + 1)) hstep :=
      (DifferentialInducedSuccessor.successorOfNonempty_eq hstep d).symm
    simpa [b, hstep, hsucc] using hEqBall

end DifferentialSuccessorAdaptiveHomotopyGrid
end Poincare
