import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.CartanAdjacentContinuation
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.UnitInterval

/-!
# Adjacent continuation from differential-successor local seeds

The interval naturality theorem gives honest local equality between a Cartan
state and its differential-induced successor.  This file feeds those local
seeds into the existing adjacent-overlap continuation theorem.

The remaining global premise is stated without hiding it: away from the
original seed anchor, whenever the two adjacent germs have the same value,
their sufficiently small nonzero differential-induced successors at that
point must be the same state.  This is precisely the differential
path-independence input needed to identify the two local recenterings.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorAdjacentContinuation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The exact cross-history monodromy datum at one common source point: one
differential-induced successor from each history gives the same continuation
state.  Successor canonicity makes the particular data witnesses irrelevant. -/
def CrossHistorySuccessorAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (q : M) : Prop :=
  ∃ (d₁ : DifferentialInducedSuccessor.Data s₁ q)
    (d₂ : DifferentialInducedSuccessor.Data s₂ q),
      d₁.successor = d₂.successor

/-- The part of a strict common source lying in the two normal-coordinate
balls on which differential data and local successor naturality are known. -/
def CoordinateControlledCommonSource
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (ρ₁ ρ₂ : ℝ) : Set M :=
  {q | q ∈ s₁.germ.source ∩ s₂.germ.source ∧
    ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s₁.anchor).symm ((chartAt E s₁.anchor) q)‖ < ρ₁ ∧
    ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s₂.anchor).symm ((chartAt E s₂.anchor) q)‖ < ρ₂}

/-- The coordinate-controlled common source is open.  Each normal-coordinate
map is an open partial homeomorphism on a domain containing the corresponding
Cartan source, so the norm bounds are relatively open there. -/
theorem coordinateControlledCommonSource_isOpen
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (ρ₁ ρ₂ : ℝ) :
    IsOpen (CoordinateControlledCommonSource s₁ s₂ ρ₁ ρ₂) := by
  let e₁ := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s₁.anchor
  let e₂ := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s₂.anchor
  let c₁ : OpenPartialHomeomorph M E := (chartAt E s₁.anchor).trans e₁.symm
  let c₂ : OpenPartialHomeomorph M E := (chartAt E s₂.anchor).trans e₂.symm
  have hsub₁ : s₁.germ.source ⊆ c₁.source := by
    intro q hq
    simp only [CartanChain.ChainState.germ, CartanMap.openPartialHomeomorph,
      OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hq
    change q ∈ ((chartAt E s₁.anchor).trans e₁.symm).source
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨hq.1, hq.2.1⟩
  have hsub₂ : s₂.germ.source ⊆ c₂.source := by
    intro q hq
    simp only [CartanChain.ChainState.germ, CartanMap.openPartialHomeomorph,
      OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage] at hq
    change q ∈ ((chartAt E s₂.anchor).trans e₂.symm).source
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨hq.1, hq.2.1⟩
  have hcont₁ : ContinuousOn
      (fun q : M ↦ e₁.symm ((chartAt E s₁.anchor) q)) s₁.germ.source := by
    simpa [c₁] using c₁.continuousOn.mono hsub₁
  have hcont₂ : ContinuousOn
      (fun q : M ↦ e₂.symm ((chartAt E s₂.anchor) q)) s₂.germ.source := by
    simpa [c₂] using c₂.continuousOn.mono hsub₂
  have hopen₁ : IsOpen
      (s₁.germ.source ∩
        (fun q : M ↦ e₁.symm ((chartAt E s₁.anchor) q)) ⁻¹'
          Metric.ball (0 : E) ρ₁) :=
    hcont₁.isOpen_inter_preimage s₁.germ.open_source Metric.isOpen_ball
  have hopen₂ : IsOpen
      (s₂.germ.source ∩
        (fun q : M ↦ e₂.symm ((chartAt E s₂.anchor) q)) ⁻¹'
          Metric.ball (0 : E) ρ₂) :=
    hcont₂.isOpen_inter_preimage s₂.germ.open_source Metric.isOpen_ball
  have hset : CoordinateControlledCommonSource s₁ s₂ ρ₁ ρ₂ =
      (s₁.germ.source ∩
          (fun q : M ↦ e₁.symm ((chartAt E s₁.anchor) q)) ⁻¹'
            Metric.ball (0 : E) ρ₁) ∩
        (s₂.germ.source ∩
          (fun q : M ↦ e₂.symm ((chartAt E s₂.anchor) q)) ⁻¹'
            Metric.ball (0 : E) ρ₂) := by
    ext q
    change
      (q ∈ s₁.germ.source ∩ s₂.germ.source ∧
          ‖e₁.symm ((chartAt E s₁.anchor) q)‖ < ρ₁ ∧
          ‖e₂.symm ((chartAt E s₂.anchor) q)‖ < ρ₂) ↔
        ((q ∈ s₁.germ.source ∧
            e₁.symm ((chartAt E s₁.anchor) q) ∈ Metric.ball 0 ρ₁) ∧
          (q ∈ s₂.germ.source ∧
            e₂.symm ((chartAt E s₂.anchor) q) ∈ Metric.ball 0 ρ₂))
    simp only [mem_inter_iff, Metric.mem_ball, dist_zero_right]
    tauto
  rw [hset]
  exact hopen₁.inter hopen₂

/-- Manifold local connectedness makes the anchor component of the controlled
source an open neighborhood whenever it contains the anchor. -/
theorem coordinateControlled_anchorComponent_isOpen
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s₁ s₂ : CartanChain.ChainState g) (ρ₁ ρ₂ : ℝ) (z : M) :
    IsOpen (connectedComponentIn
      (CoordinateControlledCommonSource s₁ s₂ ρ₁ ρ₂) z) := by
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  exact (coordinateControlledCommonSource_isOpen s₁ s₂ ρ₁ ρ₂).connectedComponentIn

/-- Constant curvature supplies positive coordinate radii on which both
histories carry differential successor data at every point of their controlled
common source. -/
theorem exists_coordinateControlledCommonSource_data
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s₁ s₂ : CartanChain.ChainState g) :
    ∃ ρ₁ > (0 : ℝ), ∃ ρ₂ > (0 : ℝ),
      ∀ q ∈ CoordinateControlledCommonSource s₁ s₂ ρ₁ ρ₂,
        Nonempty (DifferentialInducedSuccessor.Data s₁ q) ∧
          Nonempty (DifferentialInducedSuccessor.Data s₂ q) := by
  rcases DifferentialSuccessorZero.exists_data_on_ball g hcurv s₁ with
    ⟨ρ₁, hρ₁, hdata₁⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball g hcurv s₂ with
    ⟨ρ₂, hρ₂, hdata₂⟩
  refine ⟨ρ₁, hρ₁, ρ₂, hρ₂, ?_⟩
  intro q hq
  exact ⟨hdata₁ q hq.1.1 hq.2.1, hdata₂ q hq.1.2 hq.2.2⟩

/-- A cross-history agreement witness identifies every pair of differential
successors at that point. -/
theorem successor_eq_of_crossHistoryAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q : M}
    (h : CrossHistorySuccessorAgreement s₁ s₂ q)
    (d₁ : DifferentialInducedSuccessor.Data s₁ q)
    (d₂ : DifferentialInducedSuccessor.Data s₂ q) :
    d₁.successor = d₂.successor := by
  rcases h with ⟨d₁', d₂', h'⟩
  calc
    d₁.successor = d₁'.successor := d₁.successor_eq d₁'
    _ = d₂'.successor := h'
    _ = d₂.successor := d₂'.successor_eq d₂

/-- A differential successor history agrees with itself at every point where
data are available. -/
theorem crossHistorySuccessorAgreement_refl
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {q : M}
    (d : DifferentialInducedSuccessor.Data s q) :
    CrossHistorySuccessorAgreement s s q := by
  exact ⟨d, d, rfl⟩

/-- Cross-history successor agreement is symmetric. -/
theorem CrossHistorySuccessorAgreement.symm
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q : M}
    (h : CrossHistorySuccessorAgreement s₁ s₂ q) :
    CrossHistorySuccessorAgreement s₂ s₁ q := by
  rcases h with ⟨d₁, d₂, hsuccessor⟩
  exact ⟨d₂, d₁, hsuccessor.symm⟩

/-- Cross-history successor agreement is transitive.  The two witnesses in
the middle history need not be the same: within-history successor canonicity
identifies them. -/
theorem CrossHistorySuccessorAgreement.trans
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ s₃ : CartanChain.ChainState g} {q : M}
    (h₁₂ : CrossHistorySuccessorAgreement s₁ s₂ q)
    (h₂₃ : CrossHistorySuccessorAgreement s₂ s₃ q) :
    CrossHistorySuccessorAgreement s₁ s₃ q := by
  rcases h₁₂ with ⟨d₁, d₂, hsuccessor₁₂⟩
  rcases h₂₃ with ⟨d₂', d₃, hsuccessor₂₃⟩
  exact ⟨d₁, d₃,
    hsuccessor₁₂.trans ((d₂.successor_eq d₂').trans hsuccessor₂₃)⟩

/-- With data witnesses fixed, cross-history agreement is exactly equality of
their successor states.  This eliminates all classical-choice dependence at
chain-comparison call sites. -/
theorem crossHistorySuccessorAgreement_iff
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q : M}
    (d₁ : DifferentialInducedSuccessor.Data s₁ q)
    (d₂ : DifferentialInducedSuccessor.Data s₂ q) :
    CrossHistorySuccessorAgreement s₁ s₂ q ↔
      d₁.successor = d₂.successor := by
  constructor
  · intro h
    exact successor_eq_of_crossHistoryAgreement h d₁ d₂
  · intro h
    exact ⟨d₁, d₂, h⟩

/-- Cross-history agreement identifies the canonical successors selected from
any two nonemptiness proofs. -/
theorem successorOfNonempty_eq_of_crossHistoryAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q : M}
    (h₁ : Nonempty (DifferentialInducedSuccessor.Data s₁ q))
    (h₂ : Nonempty (DifferentialInducedSuccessor.Data s₂ q))
    (hcross : CrossHistorySuccessorAgreement s₁ s₂ q) :
    DifferentialInducedSuccessor.successorOfNonempty s₁ q h₁ =
      DifferentialInducedSuccessor.successorOfNonempty s₂ q h₂ := by
  rcases hcross with ⟨d₁, d₂, hsuccessor⟩
  calc
    DifferentialInducedSuccessor.successorOfNonempty s₁ q h₁ =
        d₁.successor :=
      DifferentialInducedSuccessor.successorOfNonempty_eq h₁ d₁
    _ = d₂.successor := hsuccessor
    _ = DifferentialInducedSuccessor.successorOfNonempty s₂ q h₂ :=
      (DifferentialInducedSuccessor.successorOfNonempty_eq h₂ d₂).symm

/-- Equality of two carried maps on an open neighborhood produces
cross-history successor agreement at every point where both data packages are
available. -/
theorem crossHistorySuccessorAgreement_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q : M}
    (d₁ : DifferentialInducedSuccessor.Data s₁ q)
    (d₂ : DifferentialInducedSuccessor.Data s₂ q)
    {U : Set M} (hU : IsOpen U) (hq : q ∈ U)
    (hEq : EqOn s₁.germ s₂.germ U) :
    CrossHistorySuccessorAgreement s₁ s₂ q := by
  refine ⟨d₁, d₂, ?_⟩
  apply d₁.successor_eq_of_eqOn_open d₂ hU hq
  intro x hx
  simpa [CartanChain.ChainState.germ, CartanChain.ChainState.map] using
    hEq hx

/-- The new anchor has automatic cross-history successor agreement: the old
history uses the step data itself, while the new history uses its canonical
zero-vector anchor data. -/
theorem crossHistorySuccessorAgreement_at_successor_anchor
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z) :
    CrossHistorySuccessorAgreement s d.successor z := by
  let dn : DifferentialInducedSuccessor.Data d.successor z := by
    simpa using DifferentialSuccessorZero.anchorData d.successor
  refine ⟨d, dn, ?_⟩
  simpa [dn] using
    (DifferentialSuccessorZero.anchorData_successor d.successor).symm

/-- Differential single-insertion independence in its minimal algebraic form.
Cross-history agreement at the endpoint identifies the direct successor with
the successor obtained after inserting one intermediate anchor.  This is the
cell-comparison rule needed by differential homotopy ladders. -/
theorem endpoint_successor_eq_insert_of_crossHistoryAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {y z : M}
    (dy : DifferentialInducedSuccessor.Data s y)
    (dz : DifferentialInducedSuccessor.Data s z)
    (dyz : DifferentialInducedSuccessor.Data dy.successor z)
    (hcross : CrossHistorySuccessorAgreement s dy.successor z) :
    dz.successor = dyz.successor :=
  successor_eq_of_crossHistoryAgreement hcross dz dyz

@[simp]
theorem differentialChain_chainState_succ_anchor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (step : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) nodes) (n : ℕ) :
    (DifferentialInducedSuccessor.Chain.chainState
      nodes initial step (n + 1)).anchor = nodes (n + 1) := by
  rw [DifferentialInducedSuccessor.Chain.chainState_succ]
  rfl

/-- The positive-index anchor rule for a realized differential chain.  No
successor data at states outside the realized trajectory are required. -/
@[simp]
theorem reachableChain_state_succ_anchor
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : CartanChain.ChainState g}
    (chain : DifferentialInducedSuccessor.Chain.ReachableChain nodes initial)
    (n : ℕ) :
    (chain.state (n + 1)).anchor = nodes (n + 1) :=
  chain.state_succ_anchor n

/-- Rectangular ladder invariant for realized differential-induced chains.

`rungData j` is the one vertical datum actually used at column `j`: it starts
at the reached lower-row state and is anchored at the corresponding upper-row
node.  The row chains themselves likewise store data only at reached states.
Thus this version has no `StepAvailable` premise over counterfactual states. -/
theorem reachableChains_ladder_invariant
    {g : ClosedSmoothRiemannianMetric 3 M}
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (rungData : ∀ j : ℕ,
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (hbottom : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (lowerChain.state j) (lowerChain.state (j + 1)) (upper (j + 1)))
    (hrung : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (lowerChain.state (j + 1)) (rungData j).successor (upper (j + 2))) :
    ∀ n : ℕ, upperChain.state (n + 1) = (rungData n).successor := by
  intro n
  induction n with
  | zero =>
      have hzero : upperChain.state 0 = lowerChain.state 0 :=
        upperChain.initial_eq.trans lowerChain.initial_eq.symm
      have hcross : CrossHistorySuccessorAgreement
          (upperChain.state 0) (lowerChain.state 1) (upper 1) := by
        rw [hzero]
        simpa using hbottom 0
      calc
        upperChain.state (0 + 1) = (upperChain.data 0).successor :=
          upperChain.state_succ 0
        _ = (rungData 0).successor :=
          successor_eq_of_crossHistoryAgreement
            hcross (upperChain.data 0) (rungData 0)
  | succ n ih =>
      have hrung' : CrossHistorySuccessorAgreement
          (lowerChain.state (n + 1)) (upperChain.state (n + 1))
          (upper (n + 2)) := by
        rw [ih]
        exact hrung n
      have hcross : CrossHistorySuccessorAgreement
          (upperChain.state (n + 1)) (lowerChain.state (n + 2))
          (upper (n + 2)) :=
        hrung'.symm.trans (hbottom (n + 1))
      calc
        upperChain.state (n.succ + 1) =
            (upperChain.data (n + 1)).successor := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            upperChain.state_succ (n + 1)
        _ = (rungData (n + 1)).successor :=
          successor_eq_of_crossHistoryAgreement
            hcross (upperChain.data (n + 1)) (rungData (n + 1))
        _ = (rungData n.succ).successor := by
          rw [Nat.succ_eq_add_one]

/-- Endpoint comparison for two realized chains across a finite ladder.  If
the two node rows have the same endpoint, the last realized rung is based at
the lower state's anchor and hence has zero normal vector. -/
theorem reachableChains_endpoint_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {initial : CartanChain.ChainState g} {lower upper : ℕ → M}
    (lowerChain :
      DifferentialInducedSuccessor.Chain.ReachableChain lower initial)
    (upperChain :
      DifferentialInducedSuccessor.Chain.ReachableChain upper initial)
    (rungData : ∀ j : ℕ,
      DifferentialInducedSuccessor.Data
        (lowerChain.state (j + 1)) (upper (j + 1)))
    (hbottom : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (lowerChain.state j) (lowerChain.state (j + 1)) (upper (j + 1)))
    (hrung : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (lowerChain.state (j + 1)) (rungData j).successor (upper (j + 2)))
    (N : ℕ) (hend : lower (N + 1) = upper (N + 1)) :
    lowerChain.state (N + 1) = upperChain.state (N + 1) := by
  let b := lowerChain.state (N + 1)
  let d := rungData N
  have hbAnchor : b.anchor = lower (N + 1) := by
    simpa [b] using lowerChain.state_succ_anchor N
  have hdAtAnchor : upper (N + 1) = b.anchor :=
    hend.symm.trans hbAnchor.symm
  have hdzero : d.v = 0 :=
    DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq d hdAtAnchor
  have hrungZero : d.successor = b :=
    DifferentialSuccessorZero.successor_eq_of_vector_eq_zero d hdzero
  have hinvariant := reachableChains_ladder_invariant
    lowerChain upperChain rungData hbottom hrung N
  calc
    lowerChain.state (N + 1) = b := rfl
    _ = d.successor := hrungZero.symm
    _ = upperChain.state (N + 1) := by
      simpa [d] using hinvariant.symm

/-- Rectangular ladder invariant for differential-induced chains.

The lower row is advanced by its own differential policy.  At each positive
column, `stepUpper` also supplies the vertical successor of the lower state.
The first cross-history hypothesis inserts the next lower edge; the second
removes the preceding vertical rung.  Hence the upper-row state is exactly the
vertical successor of the lower-row state after every positive column.

Unlike the older Cartan-chain ladder, this statement carries no globally
chosen tangent alignments and no full-overlap `RigidStepCompatible` fields. -/
theorem differentialChain_ladder_invariant
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (hbottom : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j)
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (upper (j + 1)))
    (hrung : ∀ j : ℕ,
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
    ∀ n : ℕ,
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
        (by simpa using hbottom 0)
  | succ n ih =>
      let b₁ := DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (n + 1)
      let b₂ := DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (n + 2)
      let t₁ := DifferentialInducedSuccessor.Chain.chainState
        upper initial stepUpper (n + 1)
      let rung₁ := DifferentialInducedSuccessor.successorOfNonempty
        b₁ (upper (n + 1)) (stepUpper n b₁)
      have hit : t₁ = rung₁ := by
        simpa [b₁, t₁, rung₁] using ih
      have hrung' : CrossHistorySuccessorAgreement
          b₁ t₁ (upper (n + 2)) := by
        rw [hit]
        simpa [b₁, rung₁] using hrung n
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
            (by simpa [b₁, b₂] using hbottom (n + 1))
        _ = DifferentialInducedSuccessor.successorOfNonempty
              (DifferentialInducedSuccessor.Chain.chainState
                lower initial stepLower (n.succ + 1))
              (upper (n.succ + 1))
              (stepUpper n.succ
                (DifferentialInducedSuccessor.Chain.chainState
                  lower initial stepLower (n.succ + 1))) := by
          simp only [b₂, Nat.succ_eq_add_one, Nat.add_assoc]

/-- Endpoint comparison for two differential-induced chains across a finite
ladder.  When the two node rows end at the same point, the final vertical
successor is based at the lower state's own anchor; its stored normal vector
is therefore zero, so the ladder invariant identifies the two endpoint
states. -/
theorem differentialChains_endpoint_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (hbottom : ∀ j : ℕ,
      CrossHistorySuccessorAgreement
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j)
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1))
        (upper (j + 1)))
    (hrung : ∀ j : ℕ,
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
    (N : ℕ) (hend : lower (N + 1) = upper (N + 1)) :
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
  have hinvariant := differentialChain_ladder_invariant
    initial lower upper stepLower stepUpper hbottom hrung N
  calc
    DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (N + 1) = b := rfl
    _ = DifferentialInducedSuccessor.successorOfNonempty
          b (upper (N + 1)) (stepUpper N b) := hrungZero.symm
    _ = DifferentialInducedSuccessor.Chain.chainState
          upper initial stepUpper (N + 1) := by
      simpa [b] using hinvariant.symm

/-- Metric-ball patches discharge both cross-history hypotheses of the
differential ladder.

For a lower horizontal edge, the first patch identifies the state before and
after that edge on a ball centered at its endpoint; membership of the upper
grid vertex then gives `hbottom`.  For a vertical rung, the second patch does
the same one column later and gives `hrung`.  Differential-data policies supply
the two pointwise data witnesses, while open-set equality identifies their
successors canonically.

Consequently the only remaining geometric subdivision problem is to arrange
the two displayed metric-ball memberships. -/
theorem differentialChains_endpoint_eq_of_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (initial : CartanChain.ChainState g) (lower upper : ℕ → M)
    (stepLower : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) lower)
    (stepUpper : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) upper)
    (rBottom rRung : ℕ → ℝ)
    (N : ℕ) (hend : lower (N + 1) = upper (N + 1)) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ j : ℕ,
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower j).germ
        (DifferentialInducedSuccessor.Chain.chainState
          lower initial stepLower (j + 1)).germ
        (Metric.ball (lower (j + 1)) (rBottom j))) →
    (∀ j : ℕ,
      upper (j + 1) ∈ Metric.ball (lower (j + 1)) (rBottom j)) →
    (∀ j : ℕ,
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
    (∀ j : ℕ,
      upper (j + 2) ∈ Metric.ball (upper (j + 1)) (rRung j)) →
    DifferentialInducedSuccessor.Chain.chainState
        lower initial stepLower (N + 1) =
      DifferentialInducedSuccessor.Chain.chainState
        upper initial stepUpper (N + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottomEq hbottomMem hrungEq hrungMem
  apply differentialChains_endpoint_eq
    initial lower upper stepLower stepUpper
  · intro j
    let b₀ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower j
    let b₁ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower (j + 1)
    let d₀ : DifferentialInducedSuccessor.Data b₀ (upper (j + 1)) :=
      Classical.choice (stepUpper j b₀)
    let d₁ : DifferentialInducedSuccessor.Data b₁ (upper (j + 1)) :=
      Classical.choice (stepUpper j b₁)
    exact crossHistorySuccessorAgreement_of_eqOn_open
      d₀ d₁ Metric.isOpen_ball (hbottomMem j)
      (by simpa [b₀, b₁] using hbottomEq j)
  · intro j
    let b₁ := DifferentialInducedSuccessor.Chain.chainState
      lower initial stepLower (j + 1)
    let rung := DifferentialInducedSuccessor.successorOfNonempty
      b₁ (upper (j + 1)) (stepUpper j b₁)
    let d₁ : DifferentialInducedSuccessor.Data b₁ (upper (j + 2)) :=
      Classical.choice (stepUpper (j + 1) b₁)
    let dr : DifferentialInducedSuccessor.Data rung (upper (j + 2)) :=
      Classical.choice (stepUpper (j + 1) rung)
    exact crossHistorySuccessorAgreement_of_eqOn_open
      d₁ dr Metric.isOpen_ball (hrungMem j)
      (by simpa [b₁, rung] using hrungEq j)
  · exact hend

/-- A continuous homotopy rectangle admits a finite monotone grid subordinate
to any metric-ball cover of its image.

This is the exact compactness/Lebesgue-number interface needed after producing
local differential-successor `EqOn` balls: once those balls cover the homotopy
image, every closed grid cell maps into one patch ball.  The proof pulls the
ball cover back to the compact parameter square and applies the existing
two-dimensional unit-interval subdivision theorem. -/
theorem exists_homotopy_metricBall_grid
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (H : C(unitInterval × unitInterval, M))
    {J : Type*} (center : J → M) (radius : J → ℝ) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ q : unitInterval × unitInterval,
      ∃ j : J, H q ∈ Metric.ball (center j) (radius j)) →
    ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧
        Monotone t ∧
          (∃ k, ∀ n ≥ k, t n = 1) ∧
            ∀ n m, ∃ j : J,
              ∀ s ∈ Icc (t n) (t (n + 1)),
                ∀ u ∈ Icc (t m) (t (m + 1)),
                  H (s, u) ∈ Metric.ball (center j) (radius j) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hcover
  let c : J → Set (unitInterval × unitInterval) := fun j ↦
    H ⁻¹' Metric.ball (center j) (radius j)
  have hcOpen : ∀ j : J, IsOpen (c j) := by
    intro j
    exact Metric.isOpen_ball.preimage H.continuous
  have hcCover : (Set.univ : Set (unitInterval × unitInterval)) ⊆
      ⋃ j, c j := by
    intro q _hq
    rcases hcover q with ⟨j, hj⟩
    exact mem_iUnion.2 ⟨j, hj⟩
  rcases exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      hcOpen hcCover with
    ⟨t, ht0, htmono, hteventual, hcell⟩
  refine ⟨t, ht0, htmono, hteventual, ?_⟩
  intro n m
  rcases hcell n m with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro s hs u hu
  exact hj ⟨hs, hu⟩

/-- The discrete row of a homotopy rectangle selected by one common unit-
interval subdivision. -/
def homotopyGridRow {x y : M} {p₀ p₁ : Path x y}
    (F : p₀.Homotopy p₁) (t : ℕ → unitInterval) (m : ℕ) : ℕ → M :=
  fun n ↦ F (t m, t n)

/-- Row-indexed differential homotopy ladder driven by state-dependent equality
patches.

For each adjacent pair of homotopy rows, `rBottom m j` is an equality ball for
the two lower-row histories before and after column `j`, while `rRung m j` is
an equality ball after inserting the vertical rung.  The two membership
hypotheses say that the opposite vertices needed by the cell comparison lie in
those particular balls.  Thus the radii and `EqOn` certificates may depend on
the recursively generated row state; no history-independent cover is assumed.

The eventual value `t = 1` closes every adjacent-row ladder at the common path
endpoint and also makes row `k + 1` the target boundary row.  Iterating the
adjacent-row equality compares the two boundary continuations. -/
theorem differentialHomotopyGrid_chain_endpoint_eq_of_metricBall_patches
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M} {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (t : ℕ → unitInterval)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (rBottom rRung : ℕ → ℕ → ℝ)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ m j : ℕ,
      EqOn
        (DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) j).germ
        (DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t m) initial (step m) (j + 1)).germ
        (Metric.ball
          (homotopyGridRow F t m (j + 1)) (rBottom m j))) →
    (∀ m j : ℕ,
      homotopyGridRow F t (m + 1) (j + 1) ∈
        Metric.ball
          (homotopyGridRow F t m (j + 1)) (rBottom m j)) →
    (∀ m j : ℕ,
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
    (∀ m j : ℕ,
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
  have hadj : ∀ m : ℕ, endpointState m = endpointState (m + 1) := by
    intro m
    refine differentialChains_endpoint_eq_of_metricBall_patches
      initial (homotopyGridRow F t m) (homotopyGridRow F t (m + 1))
      (step m) (step (m + 1)) (rBottom m) (rRung m) k ?_
      (hbottomEq m) (hbottomMem m) (hrungEq m) (hrungMem m)
    simp only [homotopyGridRow, htK]
    exact (F.target (t m)).trans (F.target (t (m + 1))).symm
  have hiterate : ∀ m : ℕ, endpointState 0 = endpointState m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        exact ih.trans (by simpa [Nat.succ_eq_add_one] using hadj m)
  simpa [endpointState] using hiterate (k + 1)

/-- The successor anchor lies in every coordinate-controlled common source
whose predecessor radius contains the step vector and whose successor radius
is positive. -/
theorem successor_anchor_mem_coordinateControlledCommonSource
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {rhoS rhoN : ℝ} (hd : ‖d.v‖ < rhoS) (hrhoN : 0 < rhoN) :
    z ∈ CoordinateControlledCommonSource s d.successor rhoS rhoN := by
  have hzOld : z ∈ s.germ.source := d.anchor_mem_predecessor_source
  have hzNew : z ∈ d.successor.germ.source := by
    simpa [DifferentialInducedSuccessor.Data.successor] using
      CartanAdjacentContinuation.chainAdjacent_anchor_mem_successor_source
        s z d.alignment
  have hzSourceCoordinate :
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor).symm ((chartAt E s.anchor) z) = d.v := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor
    change eM.symm ((chartAt E s.anchor) z) = d.v
    rw [show (chartAt E s.anchor) z = eM d.v by
      simpa [eM, extChartAt_coe] using d.source_coordinate]
    exact eM.left_inv d.source_vector_mem
  have hzNewCoordinate :
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) d.successor.anchor).symm
          ((chartAt E d.successor.anchor) z) = 0 := by
    change
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) z).symm ((chartAt E z) z) = 0
    exact
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
        g z
  exact ⟨⟨hzOld, hzNew⟩,
    by simpa [hzSourceCoordinate] using hd,
    by
      rw [hzNewCoordinate]
      simpa using hrhoN⟩

/--
The local interval-naturalness seeds close an entire preconnected adjacent
overlap once differential-induced recentering is path-independent at every
other equality point.

The returned radii are the honest normal radii supplied separately
for the predecessor and its successor.  The last premise is the exact
remaining globalization condition: at a non-seed equality point, choose data
inside those radii for both histories and require the induced successor states
to coincide.
-/
theorem exists_eqOn_common_source_of_preconnected_of_successor_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            IsPreconnected (s.germ.source ∩ d.successor.germ.source) →
            (∀ q ∈ s.germ.source ∩ d.successor.germ.source,
              s.germ q = d.successor.germ q → q ≠ z →
                ∃ (ds : DifferentialInducedSuccessor.Data s q)
                  (dn : DifferentialInducedSuccessor.Data d.successor q),
                    ‖ds.v‖ < rhoS ∧ ‖dn.v‖ < rhoN ∧
                    ds.successor = dn.successor) →
              EqOn s.germ d.successor.germ
                (s.germ.source ∩ d.successor.germ.source) := by
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv s with
    ⟨rhoS, hrhoS, hlocalS⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hlocalS d hd with
    ⟨Vseed, hVseedOpen, hzVseed, hseedLocal⟩
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv d.successor with
    ⟨rhoN, hrhoN, hlocalN⟩
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpre hpath
  have hfull :
      EqOn s.germ
        (InducedAlignment.CompatibleStep.nextWithAlignment
          s z d.alignment).germ
        (s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment
            s z d.alignment).germ.source) := by
    apply
      CartanAdjacentContinuation.chainAdjacent_eqOn_of_preconnected_overlap_of_local_rigidity
        s z d.alignment d.anchor_mem_predecessor_source
        (by simpa [DifferentialInducedSuccessor.Data.successor] using hpre)
    intro q hq hEq
    have hq' : q ∈ s.germ.source ∩ d.successor.germ.source := by
      simpa [DifferentialInducedSuccessor.Data.successor] using hq
    have hEq' : s.germ q = d.successor.germ q := by
      simpa [DifferentialInducedSuccessor.Data.successor] using hEq
    by_cases hqz : q = z
    · subst q
      exact ⟨Vseed, hVseedOpen, hzVseed, by
        simpa [DifferentialInducedSuccessor.Data.successor] using hseedLocal⟩
    · rcases hpath q hq' hEq' hqz with
        ⟨ds, dn, hds, hdn, hsucc⟩
      rcases hlocalS ds hds with ⟨Vs, hVsOpen, hqVs, hEqS⟩
      rcases hlocalN dn hdn with ⟨Vn, hVnOpen, hqVn, hEqN⟩
      let W : Set M :=
        (Vs ∩ Vn) ∩
          (ds.successor.germ.source ∩ dn.successor.germ.source)
      have hqDs : q ∈ ds.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor,
          InducedAlignment.CompatibleStep.nextWithAlignment,
          CartanChain.ChainState.germ] using
          CartanMap.anchor_mem_source g q (s.map q) ds.alignment
      have hqDn : q ∈ dn.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor,
          InducedAlignment.CompatibleStep.nextWithAlignment,
          CartanChain.ChainState.germ] using
          CartanMap.anchor_mem_source g q (d.successor.map q) dn.alignment
      refine ⟨W,
        (hVsOpen.inter hVnOpen).inter
          (ds.successor.germ.open_source.inter dn.successor.germ.open_source),
        ⟨⟨hqVs, hqVn⟩, hqDs, hqDn⟩, ?_⟩
      intro x hx
      have hxW : x ∈
          (Vs ∩ Vn) ∩
            (ds.successor.germ.source ∩ dn.successor.germ.source) := hx.1
      have hxOld : x ∈ s.germ.source ∩ d.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor] using hx.2
      have hxs : s.germ x = ds.successor.germ x :=
        hEqS ⟨hxW.1.1, hxOld.1, hxW.2.1⟩
      have hxn : d.successor.germ x = dn.successor.germ x :=
        hEqN ⟨hxW.1.2, hxOld.2, hxW.2.2⟩
      calc
        s.germ x = ds.successor.germ x := hxs
        _ = dn.successor.germ x := by rw [hsucc]
        _ = d.successor.germ x := hxn.symm
  simpa [DifferentialInducedSuccessor.Data.successor] using hfull

/--
Without assuming that the whole strict common source is preconnected, the
same differential-successor argument closes the connected component of the
common source containing the new anchor.  This isolates connectedness from
the differential path-independence input: no hypothesis about any other
component is needed.
-/
theorem exists_eqOn_anchorComponent_of_successor_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            (∀ q ∈ s.germ.source ∩ d.successor.germ.source,
              s.germ q = d.successor.germ q → q ≠ z →
                ∃ (ds : DifferentialInducedSuccessor.Data s q)
                  (dn : DifferentialInducedSuccessor.Data d.successor q),
                    ‖ds.v‖ < rhoS ∧ ‖dn.v‖ < rhoN ∧
                    ds.successor = dn.successor) →
              EqOn s.germ d.successor.germ
                (connectedComponentIn
                  (s.germ.source ∩ d.successor.germ.source) z) := by
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv s with
    ⟨rhoS, hrhoS, hlocalS⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hlocalS d hd with
    ⟨Vseed, hVseedOpen, hzVseed, hseedLocal⟩
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv d.successor with
    ⟨rhoN, hrhoN, hlocalN⟩
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpath
  have hcomponent :
      EqOn s.germ
        (InducedAlignment.CompatibleStep.nextWithAlignment
          s z d.alignment).germ
        (connectedComponentIn
          (s.germ.source ∩
            (InducedAlignment.CompatibleStep.nextWithAlignment
              s z d.alignment).germ.source) z) := by
    apply
      CartanAdjacentContinuation.chainAdjacent_eqOn_anchorComponent_of_local_rigidity
        s z d.alignment d.anchor_mem_predecessor_source
    intro q hq hEq
    have hq' : q ∈ s.germ.source ∩ d.successor.germ.source := by
      simpa [DifferentialInducedSuccessor.Data.successor] using hq
    have hEq' : s.germ q = d.successor.germ q := by
      simpa [DifferentialInducedSuccessor.Data.successor] using hEq
    by_cases hqz : q = z
    · subst q
      exact ⟨Vseed, hVseedOpen, hzVseed, by
        simpa [DifferentialInducedSuccessor.Data.successor] using hseedLocal⟩
    · rcases hpath q hq' hEq' hqz with
        ⟨ds, dn, hds, hdn, hsucc⟩
      rcases hlocalS ds hds with ⟨Vs, hVsOpen, hqVs, hEqS⟩
      rcases hlocalN dn hdn with ⟨Vn, hVnOpen, hqVn, hEqN⟩
      let W : Set M :=
        (Vs ∩ Vn) ∩
          (ds.successor.germ.source ∩ dn.successor.germ.source)
      have hqDs : q ∈ ds.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor,
          InducedAlignment.CompatibleStep.nextWithAlignment,
          CartanChain.ChainState.germ] using
          CartanMap.anchor_mem_source g q (s.map q) ds.alignment
      have hqDn : q ∈ dn.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor,
          InducedAlignment.CompatibleStep.nextWithAlignment,
          CartanChain.ChainState.germ] using
          CartanMap.anchor_mem_source g q (d.successor.map q) dn.alignment
      refine ⟨W,
        (hVsOpen.inter hVnOpen).inter
          (ds.successor.germ.open_source.inter dn.successor.germ.open_source),
        ⟨⟨hqVs, hqVn⟩, hqDs, hqDn⟩, ?_⟩
      intro x hx
      have hxW : x ∈
          (Vs ∩ Vn) ∩
            (ds.successor.germ.source ∩ dn.successor.germ.source) := hx.1
      have hxOld : x ∈ s.germ.source ∩ d.successor.germ.source := by
        simpa [DifferentialInducedSuccessor.Data.successor] using hx.2
      have hxs : s.germ x = ds.successor.germ x :=
        hEqS ⟨hxW.1.1, hxOld.1, hxW.2.1⟩
      have hxn : d.successor.germ x = dn.successor.germ x :=
        hEqN ⟨hxW.1.2, hxOld.2, hxW.2.2⟩
      calc
        s.germ x = ds.successor.germ x := hxs
        _ = dn.successor.germ x := by rw [hsucc]
        _ = d.successor.germ x := hxn.symm
  simpa [DifferentialInducedSuccessor.Data.successor] using hcomponent

/--
The coordinate bounds need not be assumed on the whole adjacent overlap.
Without any cover premise, local naturality and differential data close the
connected component of the coordinate-controlled common source containing the
new anchor.  Extending this component to the full common source is therefore
cleanly separated from the local analytic argument.
-/
theorem exists_eqOn_coordinateControlled_anchorComponent_of_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            (∀ q ∈ connectedComponentIn
                (CoordinateControlledCommonSource
                  s d.successor rhoS rhoN) z,
              s.germ q = d.successor.germ q → q ≠ z →
                CrossHistorySuccessorAgreement s d.successor q) →
              EqOn s.germ d.successor.germ
                (connectedComponentIn
                  (CoordinateControlledCommonSource
                    s d.successor rhoS rhoN) z) := by
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv s with
    ⟨rhoLS, hrhoLS, hlocalS⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv s with
    ⟨rhoDS, hrhoDS, hdataS⟩
  let rhoS : ℝ := min rhoLS rhoDS
  have hrhoS : 0 < rhoS := lt_min hrhoLS hrhoDS
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  have hdLocal : ‖d.v‖ < rhoLS := hd.trans_le (min_le_left _ _)
  rcases hlocalS d hdLocal with
    ⟨Vseed, hVseedOpen, hzVseed, hseedLocal⟩
  rcases
      DifferentialSuccessorIntervalNaturality.exists_local_eqOn_differentialSuccessor_all
        g hcurv d.successor with
    ⟨rhoLN, hrhoLN, hlocalN⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv d.successor with
    ⟨rhoDN, hrhoDN, hdataN⟩
  let rhoN : ℝ := min rhoLN rhoDN
  have hrhoN : 0 < rhoN := lt_min hrhoLN hrhoDN
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpath
  let S : Set M := CoordinateControlledCommonSource
    s d.successor rhoS rhoN
  let C : Set M := connectedComponentIn S z
  have hzS : z ∈ S := by
    simpa [S] using
      successor_anchor_mem_coordinateControlledCommonSource d hd hrhoN
  have hCsubS : C ⊆ S := by
    simpa [C] using connectedComponentIn_subset S z
  have hCsubOverlap : C ⊆ s.germ.source ∩ d.successor.germ.source := by
    intro q hq
    exact (hCsubS hq).1
  have hsCont : ContinuousOn s.germ C :=
    s.germ.continuousOn.mono (hCsubOverlap.trans inter_subset_left)
  have hnCont : ContinuousOn d.successor.germ C :=
    d.successor.germ.continuousOn.mono
      (hCsubOverlap.trans inter_subset_right)
  have hseed : s.germ z = d.successor.germ z := by
    simpa [DifferentialInducedSuccessor.Data.successor] using
      CartanAdjacentContinuation.chainAdjacent_anchor_seed
        s z d.alignment
  change EqOn s.germ d.successor.germ C
  apply
    CartanOverlapContinuation.eqOn_of_preconnected_of_continuousOn_of_local_rigidity
      (by simpa [C] using
        (isPreconnected_connectedComponentIn : IsPreconnected C))
      hsCont hnCont
      ⟨z, by simpa [C] using mem_connectedComponentIn hzS, hseed⟩
  intro q hqC hEq
  have hqS : q ∈ S := hCsubS hqC
  have hqOverlap : q ∈ s.germ.source ∩ d.successor.germ.source := hqS.1
  by_cases hqz : q = z
  · subst q
    refine ⟨Vseed, hVseedOpen, hzVseed, ?_⟩
    intro x hx
    exact hseedLocal ⟨hx.1, hCsubOverlap hx.2⟩
  · have hcross : CrossHistorySuccessorAgreement s d.successor q :=
      hpath q (by simpa [C, S] using hqC) hEq hqz
    let vS : E :=
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor).symm ((chartAt E s.anchor) q)
    let vN : E :=
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) d.successor.anchor).symm
          ((chartAt E d.successor.anchor) q)
    have hvS : ‖vS‖ < rhoS := by simpa [S, vS] using hqS.2.1
    have hvN : ‖vN‖ < rhoN := by simpa [S, vN] using hqS.2.2
    have hdsNonempty : Nonempty (DifferentialInducedSuccessor.Data s q) :=
      hdataS q hqOverlap.1
        (hvS.trans_le (min_le_right _ _))
    have hdnNonempty :
        Nonempty (DifferentialInducedSuccessor.Data d.successor q) :=
      hdataN q hqOverlap.2
        (hvN.trans_le (min_le_right _ _))
    let ds : DifferentialInducedSuccessor.Data s q :=
      Classical.choice hdsNonempty
    let dn : DifferentialInducedSuccessor.Data d.successor q :=
      Classical.choice hdnNonempty
    have hdsVector : ds.v = vS := by
      let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor
      change ds.v = eM.symm ((chartAt E s.anchor) q)
      rw [show (chartAt E s.anchor) q = eM ds.v by
        simpa [eM, extChartAt_coe] using ds.source_coordinate]
      exact (eM.left_inv ds.source_vector_mem).symm
    have hdnVector : dn.v = vN := by
      let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) d.successor.anchor
      change dn.v = eM.symm ((chartAt E d.successor.anchor) q)
      rw [show (chartAt E d.successor.anchor) q = eM dn.v by
        simpa [eM, extChartAt_coe] using dn.source_coordinate]
      exact (eM.left_inv dn.source_vector_mem).symm
    have hdsLocal : ‖ds.v‖ < rhoLS := by
      rw [hdsVector]
      exact hvS.trans_le (min_le_left _ _)
    have hdnLocal : ‖dn.v‖ < rhoLN := by
      rw [hdnVector]
      exact hvN.trans_le (min_le_left _ _)
    have hsucc : ds.successor = dn.successor :=
      successor_eq_of_crossHistoryAgreement hcross ds dn
    rcases hlocalS ds hdsLocal with ⟨Vs, hVsOpen, hqVs, hEqS⟩
    rcases hlocalN dn hdnLocal with ⟨Vn, hVnOpen, hqVn, hEqN⟩
    let W : Set M :=
      (Vs ∩ Vn) ∩
        (ds.successor.germ.source ∩ dn.successor.germ.source)
    have hqDs : q ∈ ds.successor.germ.source := by
      simpa [DifferentialInducedSuccessor.Data.successor,
        InducedAlignment.CompatibleStep.nextWithAlignment,
        CartanChain.ChainState.germ] using
        CartanMap.anchor_mem_source g q (s.map q) ds.alignment
    have hqDn : q ∈ dn.successor.germ.source := by
      simpa [DifferentialInducedSuccessor.Data.successor,
        InducedAlignment.CompatibleStep.nextWithAlignment,
        CartanChain.ChainState.germ] using
        CartanMap.anchor_mem_source g q (d.successor.map q) dn.alignment
    refine ⟨W,
      (hVsOpen.inter hVnOpen).inter
        (ds.successor.germ.open_source.inter dn.successor.germ.open_source),
      ⟨⟨hqVs, hqVn⟩, hqDs, hqDn⟩, ?_⟩
    intro x hx
    have hxW : x ∈
        (Vs ∩ Vn) ∩
          (ds.successor.germ.source ∩ dn.successor.germ.source) := hx.1
    have hxOld : x ∈ s.germ.source ∩ d.successor.germ.source :=
      hCsubOverlap hx.2
    have hxs : s.germ x = ds.successor.germ x :=
      hEqS ⟨hxW.1.1, hxOld.1, hxW.2.1⟩
    have hxn : d.successor.germ x = dn.successor.germ x :=
      hEqN ⟨hxW.1.2, hxOld.2, hxW.2.2⟩
    calc
      s.germ x = ds.successor.germ x := hxs
      _ = dn.successor.germ x := by rw [hsucc]
      _ = d.successor.germ x := hxn.symm

/-- The controlled-component theorem yields an honest open equality
neighborhood of the successor anchor.  This form is suited to patching or
iterating continuation steps without any cover assumption on the full
adjacent overlap. -/
theorem exists_open_eqOn_coordinateControlled_of_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            (∀ q ∈ connectedComponentIn
                (CoordinateControlledCommonSource
                  s d.successor rhoS rhoN) z,
              s.germ q = d.successor.germ q → q ≠ z →
                CrossHistorySuccessorAgreement s d.successor q) →
              ∃ V : Set M, IsOpen V ∧ z ∈ V ∧
                V ⊆ CoordinateControlledCommonSource
                  s d.successor rhoS rhoN ∧
                EqOn s.germ d.successor.germ V := by
  rcases
      exists_eqOn_coordinateControlled_anchorComponent_of_pathIndependence
        g hcurv s with
    ⟨rhoS, hrhoS, hcomponent⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hcomponent d hd with ⟨rhoN, hrhoN, hcomponentN⟩
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpath
  let S : Set M := CoordinateControlledCommonSource
    s d.successor rhoS rhoN
  let V : Set M := connectedComponentIn S z
  have hzS : z ∈ S := by
    simpa [S] using
      successor_anchor_mem_coordinateControlledCommonSource d hd hrhoN
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · simpa [V, S] using
      coordinateControlled_anchorComponent_isOpen
        s d.successor rhoS rhoN z
  · simpa [V] using mem_connectedComponentIn hzS
  · simpa [V] using connectedComponentIn_subset S z
  · simpa [V, S] using hcomponentN hpath

/-- Quantitative form of the controlled equality patch.  On a closed
Riemannian manifold the open anchor component contains a positive metric ball,
which is the neighborhood shape consumed by finite subdivision and homotopy
grid arguments. -/
theorem exists_metricBall_eqOn_coordinateControlled_of_pathIndependence
    [T2Space RoundSphere3] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            (∀ q ∈ connectedComponentIn
                (CoordinateControlledCommonSource
                  s d.successor rhoS rhoN) z,
              s.germ q = d.successor.germ q → q ≠ z →
                CrossHistorySuccessorAgreement s d.successor q) →
              ∃ r > (0 : ℝ),
                Metric.ball z r ⊆ CoordinateControlledCommonSource
                  s d.successor rhoS rhoN ∧
                EqOn s.germ d.successor.germ (Metric.ball z r) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_open_eqOn_coordinateControlled_of_pathIndependence
      g hcurv s with
    ⟨rhoS, hrhoS, hopen⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hopen d hd with ⟨rhoN, hrhoN, hopenN⟩
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpath
  rcases hopenN hpath with ⟨V, hVOpen, hzV, hVControlled, hEqV⟩
  rcases Metric.isOpen_iff.mp hVOpen z hzV with ⟨r, hr, hballV⟩
  refine ⟨r, hr, hballV.trans hVControlled, ?_⟩
  intro q hq
  exact hEqV (hballV hq)

/-- If the coordinate-controlled common source itself is preconnected, the
component conclusion above is equality on that entire controlled source.  No
coordinate-cover assumption on the larger strict overlap is introduced. -/
theorem exists_eqOn_coordinateControlled_commonSource_of_preconnected_and_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            IsPreconnected (CoordinateControlledCommonSource
              s d.successor rhoS rhoN) →
            (∀ q ∈ CoordinateControlledCommonSource
                s d.successor rhoS rhoN,
              s.germ q = d.successor.germ q → q ≠ z →
                CrossHistorySuccessorAgreement s d.successor q) →
              EqOn s.germ d.successor.germ
                (CoordinateControlledCommonSource
                  s d.successor rhoS rhoN) := by
  rcases
      exists_eqOn_coordinateControlled_anchorComponent_of_pathIndependence
        g hcurv s with
    ⟨rhoS, hrhoS, hcomponent⟩
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  rcases hcomponent d hd with ⟨rhoN, hrhoN, hcomponentN⟩
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpre hpath
  have hEqComponent := hcomponentN (by
    intro q hqComponent hEq hqz
    exact hpath q
      (connectedComponentIn_subset
        (CoordinateControlledCommonSource
          s d.successor rhoS rhoN) z hqComponent)
      hEq hqz)
  have hzControlled : z ∈ CoordinateControlledCommonSource
      s d.successor rhoS rhoN :=
    successor_anchor_mem_coordinateControlledCommonSource d hd hrhoN
  rw [hpre.connectedComponentIn hzControlled] at hEqComponent
  exact hEqComponent

/--
Version with differential data existence discharged by the constant-curvature
field.  The remaining premise now has only two geometric parts:

* the equality locus away from the seed stays in the two uniform
  normal-coordinate balls;
* one pair of differential successors supplied by the two equal-valued
  continuation histories agrees.  Within-history canonicity then identifies
  every other choice with that pair.

Thus neither existence of pointwise derivatives nor local `EqOn` is assumed.
-/
theorem exists_eqOn_common_source_of_preconnected_of_coordinate_cover_and_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            IsPreconnected (s.germ.source ∩ d.successor.germ.source) →
            (∀ q ∈ s.germ.source ∩ d.successor.germ.source,
              s.germ q = d.successor.germ q → q ≠ z →
                ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) s.anchor).symm ((chartAt E s.anchor) q)‖ < rhoS ∧
                ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) d.successor.anchor).symm
                      ((chartAt E d.successor.anchor) q)‖ < rhoN ∧
                CrossHistorySuccessorAgreement s d.successor q) →
              EqOn s.germ d.successor.germ
                (s.germ.source ∩ d.successor.germ.source) := by
  rcases
      exists_eqOn_common_source_of_preconnected_of_successor_pathIndependence
        g hcurv s with
    ⟨rhoLS, hrhoLS, hcontinue⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv s with
    ⟨rhoDS, hrhoDS, hdataS⟩
  let rhoS : ℝ := min rhoLS rhoDS
  have hrhoS : 0 < rhoS := by
    exact lt_min hrhoLS hrhoDS
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  have hdLocal : ‖d.v‖ < rhoLS := hd.trans_le (min_le_left _ _)
  rcases hcontinue d hdLocal with ⟨rhoLN, hrhoLN, hcontinueN⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv d.successor with
    ⟨rhoDN, hrhoDN, hdataN⟩
  let rhoN : ℝ := min rhoLN rhoDN
  have hrhoN : 0 < rhoN := by
    exact lt_min hrhoLN hrhoDN
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hpre hcover
  apply hcontinueN hpre
  intro q hq hEq hqz
  rcases hcover q hq hEq hqz with
    ⟨hvS, hvN, hpath⟩
  let vS : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).symm ((chartAt E s.anchor) q)
  let vN : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) d.successor.anchor).symm
        ((chartAt E d.successor.anchor) q)
  have hdsNonempty : Nonempty (DifferentialInducedSuccessor.Data s q) :=
    hdataS q hq.1
      (by
        change ‖vS‖ < rhoDS
        have hvS' : ‖vS‖ < rhoS := by simpa [vS] using hvS
        exact hvS'.trans_le (min_le_right _ _))
  have hdnNonempty :
      Nonempty (DifferentialInducedSuccessor.Data d.successor q) :=
    hdataN q hq.2
      (by
        change ‖vN‖ < rhoDN
        have hvN' : ‖vN‖ < rhoN := by simpa [vN] using hvN
        exact hvN'.trans_le (min_le_right _ _))
  let ds : DifferentialInducedSuccessor.Data s q := Classical.choice hdsNonempty
  let dn : DifferentialInducedSuccessor.Data d.successor q :=
    Classical.choice hdnNonempty
  have hdsVector : ds.v = vS := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor
    change ds.v = eM.symm ((chartAt E s.anchor) q)
    rw [show (chartAt E s.anchor) q = eM ds.v by
      simpa [eM, extChartAt_coe] using ds.source_coordinate]
    exact (eM.left_inv ds.source_vector_mem).symm
  have hdnVector : dn.v = vN := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) d.successor.anchor
    change dn.v = eM.symm ((chartAt E d.successor.anchor) q)
    rw [show (chartAt E d.successor.anchor) q = eM dn.v by
      simpa [eM, extChartAt_coe] using dn.source_coordinate]
    exact (eM.left_inv dn.source_vector_mem).symm
  have hsucc : ds.successor = dn.successor :=
    successor_eq_of_crossHistoryAgreement hpath ds dn
  refine ⟨ds, dn, ?_, ?_, hsucc⟩
  · rw [hdsVector]
    have hvS' : ‖vS‖ < rhoS := by simpa [vS] using hvS
    exact hvS'.trans_le (min_le_left _ _)
  · rw [hdnVector]
    have hvN' : ‖vN‖ < rhoN := by simpa [vN] using hvN
    exact hvN'.trans_le (min_le_left _ _)

/--
Connected-component version with differential data existence discharged by
the constant-curvature field.  The only remaining pointwise inputs are the
two coordinate bounds and cross-history successor
path-independence; no global connectedness premise is required.
-/
theorem exists_eqOn_anchorComponent_of_coordinate_cover_and_pathIndependence
    [T2Space RoundSphere3]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rhoS > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        ‖d.v‖ < rhoS →
          ∃ rhoN > (0 : ℝ),
            (∀ q ∈ s.germ.source ∩ d.successor.germ.source,
              s.germ q = d.successor.germ q → q ≠ z →
                ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) s.anchor).symm ((chartAt E s.anchor) q)‖ < rhoS ∧
                ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) d.successor.anchor).symm
                      ((chartAt E d.successor.anchor) q)‖ < rhoN ∧
                CrossHistorySuccessorAgreement s d.successor q) →
              EqOn s.germ d.successor.germ
                (connectedComponentIn
                  (s.germ.source ∩ d.successor.germ.source) z) := by
  rcases
      exists_eqOn_anchorComponent_of_successor_pathIndependence
        g hcurv s with
    ⟨rhoLS, hrhoLS, hcontinue⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv s with
    ⟨rhoDS, hrhoDS, hdataS⟩
  let rhoS : ℝ := min rhoLS rhoDS
  have hrhoS : 0 < rhoS := by
    exact lt_min hrhoLS hrhoDS
  refine ⟨rhoS, hrhoS, ?_⟩
  intro z d hd
  have hdLocal : ‖d.v‖ < rhoLS := hd.trans_le (min_le_left _ _)
  rcases hcontinue d hdLocal with ⟨rhoLN, hrhoLN, hcontinueN⟩
  rcases DifferentialSuccessorZero.exists_data_on_ball
      g hcurv d.successor with
    ⟨rhoDN, hrhoDN, hdataN⟩
  let rhoN : ℝ := min rhoLN rhoDN
  have hrhoN : 0 < rhoN := by
    exact lt_min hrhoLN hrhoDN
  refine ⟨rhoN, hrhoN, ?_⟩
  intro hcover
  apply hcontinueN
  intro q hq hEq hqz
  rcases hcover q hq hEq hqz with
    ⟨hvS, hvN, hpath⟩
  let vS : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor).symm ((chartAt E s.anchor) q)
  let vN : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) d.successor.anchor).symm
        ((chartAt E d.successor.anchor) q)
  have hdsNonempty : Nonempty (DifferentialInducedSuccessor.Data s q) :=
    hdataS q hq.1
      (by
        change ‖vS‖ < rhoDS
        have hvS' : ‖vS‖ < rhoS := by simpa [vS] using hvS
        exact hvS'.trans_le (min_le_right _ _))
  have hdnNonempty :
      Nonempty (DifferentialInducedSuccessor.Data d.successor q) :=
    hdataN q hq.2
      (by
        change ‖vN‖ < rhoDN
        have hvN' : ‖vN‖ < rhoN := by simpa [vN] using hvN
        exact hvN'.trans_le (min_le_right _ _))
  let ds : DifferentialInducedSuccessor.Data s q := Classical.choice hdsNonempty
  let dn : DifferentialInducedSuccessor.Data d.successor q :=
    Classical.choice hdnNonempty
  have hdsVector : ds.v = vS := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) s.anchor
    change ds.v = eM.symm ((chartAt E s.anchor) q)
    rw [show (chartAt E s.anchor) q = eM ds.v by
      simpa [eM, extChartAt_coe] using ds.source_coordinate]
    exact (eM.left_inv ds.source_vector_mem).symm
  have hdnVector : dn.v = vN := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) d.successor.anchor
    change dn.v = eM.symm ((chartAt E d.successor.anchor) q)
    rw [show (chartAt E d.successor.anchor) q = eM dn.v by
      simpa [eM, extChartAt_coe] using dn.source_coordinate]
    exact (eM.left_inv dn.source_vector_mem).symm
  have hsucc : ds.successor = dn.successor :=
    successor_eq_of_crossHistoryAgreement hpath ds dn
  refine ⟨ds, dn, ?_, ?_, hsucc⟩
  · rw [hdsVector]
    have hvS' : ‖vS‖ < rhoS := by simpa [vS] using hvS
    exact hvS'.trans_le (min_le_left _ _)
  · rw [hdnVector]
    have hvN' : ‖vN‖ < rhoN := by simpa [vN] using hvN
    exact hvN'.trans_le (min_le_left _ _)

end DifferentialSuccessorAdjacentContinuation
end Poincare
