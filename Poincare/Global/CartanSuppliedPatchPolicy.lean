import Poincare.Global.CartanSuppliedBufferedPairAgreement
import Poincare.Global.CartanSuppliedReachableChain

/-!
# Core selection and sticky supplied chains

The preferred label is external to the geometric state. Selection retains it
exactly while both anchors belong to its cores, and otherwise uses the cover.
The resulting policy supplies steps even at states outside its realized history.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain

namespace CartanSuppliedPatchPolicy
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch

def fallback (B : QuantitativeCover g) (s : CartanChain.ChainState g) : B.Label :=
  (B.source.pick s.anchor, B.target.pick s.target)

def select (B : QuantitativeCover g) (preferred : B.Label)
    (s : CartanChain.ChainState g) : B.Label :=
  @ite _ (B.Valid preferred s) (Classical.propDecidable _) preferred (fallback B s)

def policy (B : QuantitativeCover g) (preferred : ℕ → B.Label) :
    ℕ → CartanChain.ChainState g → Interpretation g :=
  fun n s => B.interp (select B (preferred n) s)

def Sticky (B : QuantitativeCover g) (preferred : ℕ → B.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain (policy B preferred) nodes initial) : Prop :=
  ∀ n, preferred (n + 1) = select B (preferred n) (c.state n)

/-- Retaining a valid preference or choosing covering cores always gives valid anchors. -/
theorem select_valid : ∀ (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g), B.Valid (select B a s) s := by
  intro B a s
  classical
  unfold select
  split_ifs with h
  · exact h
  · exact ⟨Classical.choose_spec (B.source.covers s.anchor),
      Classical.choose_spec (B.target.covers s.target)⟩

/-- H1 applies to the actual alignment at every node-anchored state. -/
theorem stepAvailable : ∀ (S : System g) (a : ℕ → S.cover.Label) (nodes : ℕ → M),
    (letI : MetricSpace M := g.toMetricSpace
     ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
    StepAvailable (policy S.cover a) nodes := by
  intro S a nodes
  letI : MetricSpace M := g.toMetricSpace
  intro hmesh n s hs
  let label := select S.cover (a n) s
  have hv := select_valid S.cover (a n) s
  have hx := interior_subset (S.cover.source.core_subset label.1 hv.1)
  have hp := interior_subset (S.cover.target.core_subset label.2 hv.2)
  have hstep : S.mesh ≤ S.cover.step := by
    have := (four_mul_mesh_le S).1
    have := mesh_pos S
    linarith
  have hz : dist (nodes (n + 1)) s.anchor < S.cover.step := by
    rw [hs]
    exact (hmesh n).trans_le hstep
  exact (S.cover.h1 label.1 label.2 s.anchor hx s.target hp
    s.alignment (nodes (n + 1)) hz).2.2.2

/-- Joint recursion chooses the next state and carries the label actually selected. -/
theorem exists_sticky_chain : ∀ (S : System g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g), initial.anchor = nodes 0 →
    (letI : MetricSpace M := g.toMetricSpace
     ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
    ∃ (a : ℕ → S.cover.Label)
      (c : ReachableChain (policy S.cover a) nodes initial),
      a 0 = fallback S.cover initial ∧ Sticky S.cover a nodes initial c := by
  intro S nodes initial hinitial hmesh
  let Stage (n : ℕ) :=
    {s : CartanChain.ChainState g // s.anchor = nodes n} × S.cover.Label
  let datum (n : ℕ) (r : Stage n) :
      Data (policy S.cover (fun _ => r.2) n r.1.1) r.1.1 (nodes (n + 1)) :=
    Classical.choice (stepAvailable S (fun _ => r.2) nodes hmesh n r.1.1 r.1.2)
  let reached : ∀ n, Stage n :=
    Nat.rec (⟨⟨initial, hinitial⟩, fallback S.cover initial⟩ : Stage 0)
      (fun n r => ⟨⟨(datum n r).successor, rfl⟩, select S.cover r.2 r.1.1⟩)
  let a : ℕ → S.cover.Label := fun n => (reached n).2
  let c : ReachableChain (policy S.cover a) nodes initial := {
    state := fun n => (reached n).1.1
    initial_eq := rfl
    data := fun n => datum n (reached n)
    successor_eq := fun _ => rfl }
  exact ⟨a, c, rfl, fun _ => rfl⟩

/-- Switch agreement around each next node identifies full states across schedules. -/
theorem chains_eq : ∀ (S : System g) (a b : ℕ → S.cover.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g),
    initial.anchor = nodes 0 →
    (letI : MetricSpace M := g.toMetricSpace
     ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
    ∀ (c : ReachableChain (policy S.cover a) nodes initial)
      (d : ReachableChain (policy S.cover b) nodes initial), ∀ n, c.state n = d.state n := by
  intro S a b nodes initial hinitial
  letI : MetricSpace M := g.toMetricSpace
  intro hmesh c d n
  induction n with
  | zero => exact c.initial_eq.trans d.initial_eq.symm
  | succ n ih =>
      let s := c.state n
      let ca := select S.cover (a n) s
      let cb := select S.cover (b n) s
      have ha := select_valid S.cover (a n) s
      have hb := select_valid S.cover (b n) s
      have haB : S.cover.Buffered ca s :=
        ⟨interior_subset (S.cover.source.core_subset ca.1 ha.1),
          interior_subset (S.cover.target.core_subset ca.2 ha.2)⟩
      have hbB : S.cover.Buffered cb s :=
        ⟨interior_subset (S.cover.source.core_subset cb.1 hb.1),
          interior_subset (S.cover.target.core_subset cb.2 hb.2)⟩
      have hagree := (S.switch.agreement ca cb s haB hbB).2
      have hanchor : s.anchor = nodes n :=
        state_anchor_eq_node _ nodes initial c hinitial n
      have hradius : S.mesh ≤ S.switch.radius := by
        have := (four_mul_mesh_le S).2.2.2
        have := mesh_pos S
        linarith
      have hz : nodes (n + 1) ∈ ball s.anchor S.switch.radius := by
        rw [mem_ball, hanchor]
        exact (hmesh n).trans_le hradius
      have heq : EqOn (map (policy S.cover a n (c.state n)) (c.state n))
          (map (policy S.cover b n (d.state n)) (d.state n))
          (ball s.anchor S.switch.radius) := by
        rw [← ih]
        exact hagree
      rw [c.successor_eq n, d.successor_eq n]
      exact CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open
        _ _ _ _ (nodes (n + 1)) (c.data n) (d.data n)
        (ball s.anchor S.switch.radius) isOpen_ball hz heq

end CartanSuppliedPatchPolicy
end Poincare
