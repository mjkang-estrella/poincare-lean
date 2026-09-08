import Poincare.Global.CartanSuppliedWholeCellRealization

/-!
# Transport through supplied subdivision blocks

Open agreement at each inserted node identifies the full differential successor.
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
namespace CartanSuppliedSubdivisionTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

/-- A finite block lying within one mesh of its initial anchor has the same
full state as every direct supplied datum in a valid initial patch. -/
theorem block_state_eq (S : System g) (initial : CartanChain.ChainState g)
    (nodes : ℕ → M) (preferred : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover preferred) nodes initial)
    (hinitial : initial.anchor = nodes 0) (m N : ℕ) (a : S.cover.Label)
    (ha : S.cover.Valid a (c.state m)) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ k ≤ N, dist (nodes (m + k)) (c.state m).anchor < S.mesh) →
    ∀ d : Data (S.cover.interp a) (c.state m) (nodes (m + N)),
      c.state (m + N) = d.successor := by
  letI : MetricSpace M := g.toMetricSpace
  intro hsmall
  have hpos := mesh_pos S
  have hbound := four_mul_mesh_le S
  have hdirect : ∀ k ≤ N,
      Nonempty (Data (S.cover.interp a) (c.state m) (nodes (m + k))) := by
    intro k hk
    exact (S.cover.h1 a.1 a.2 _
      (interior_subset (S.cover.source.core_subset a.1 ha.1)) _
      (interior_subset (S.cover.target.core_subset a.2 ha.2))
      (c.state m).alignment _ (lt_of_lt_of_le (hsmall k hk) (by linarith [hbound.1]))).2.2.2
  have hanchor := state_anchor_eq_node _ nodes initial c hinitial m
  suffices h : ∀ k ≤ N, ∀ d : Data (S.cover.interp a) (c.state m) (nodes (m + k)),
      c.state (m + k) = d.successor from h N le_rfl
  intro k
  induction k with
  | zero =>
      intro _ d
      have hz : nodes (m + 0) = (c.state m).anchor := by simpa using hanchor.symm
      have hzero : ∀ z, z = (c.state m).anchor →
          ∀ e : Data (S.cover.interp a) (c.state m) z, e.successor = c.state m := by
        intro z hz e
        subst z
        exact CartanSuppliedDifferentialTransfer.patch_successor_at_anchor
          _ _ _ _ (S.cover.source.patch a.1) (S.cover.target.patch a.2)
          (S.cover.source.cutoff a.1) (S.cover.target.cutoff a.2) _ e
      exact (hzero _ hz d).symm
  | succ k ih =>
      intro hk
      simp only [← Nat.add_assoc]
      intro d
      obtain ⟨e⟩ := hdirect k (by omega)
      have he := ih (by omega) e
      let b := select S.cover (preferred (m + k)) (c.state (m + k))
      have hb : S.cover.Valid b e.successor := by
        rw [← he]
        exact select_valid _ _ _
      have hagree := (transition_eqOn S a b (c.state m) (nodes (m + k)) e ha hb
        (by have := hsmall k (by omega); linarith)).2
      have hz : nodes (m + (k + 1)) ∈ ball (nodes (m + k)) (4 * S.mesh) := by
        rw [mem_ball]
        have hdist := dist_triangle_right (nodes (m + (k + 1)))
          (nodes (m + k)) (c.state m).anchor
        have hnext := hsmall (k + 1) hk
        have hprev := hsmall k (by omega)
        linarith
      have heq : EqOn (map (S.cover.interp a) (c.state m))
          (map (policy S.cover preferred (m + k) (c.state (m + k))) (c.state (m + k)))
          (ball (nodes (m + k)) (4 * S.mesh)) := by
        change EqOn _ (map (S.cover.interp b) _) _
        rw [he]
        exact hagree
      rw [c.successor_eq (m + k)]
      exact CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open
        _ _ _ _ _ (c.data (m + k)) d _ isOpen_ball
        (by simpa only [Nat.add_assoc] using hz) heq.symm

/-- Transport to a monotone sampled chain, without imposing strictness on its
inserted samples or any terminal-index condition on the factor map. -/
theorem refinement_chain_state_eq (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p)
    (t : ℕ → unitInterval) (htzero : t 0 = 0) (htmono : Monotone t)
    (preferred : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover preferred) (fun k => p (t k)) initial)
    (f : ℕ → ℕ) (hfzero : f 0 = 0) (hfmono : Monotone f)
    (htimes : ∀ n, R.subdivision.time n = t (f n)) :
    ∀ n, R.chain.state n = c.state (f n) := by
  letI : MetricSpace M := g.toMetricSpace
  have hinitial : initial.anchor = p (t 0) := by simp [htzero]
  intro n
  induction n with
  | zero => rw [hfzero, R.chain.initial_eq, c.initial_eq]
  | succ n ih =>
      have hf : f n ≤ f (n + 1) := hfmono (Nat.le_succ n)
      have hsmall : ∀ k ≤ f (n + 1) - f n,
          dist (p (t (f n + k))) (c.state (f n)).anchor < S.mesh := by
        intro k hk
        rw [state_anchor_eq_node _ _ _ c hinitial]
        have hcell : t (f n + k) ∈
            Icc (R.subdivision.time n) (R.subdivision.time (n + 1)) := by
          rw [htimes n, htimes (n + 1)]
          exact ⟨htmono (by omega), htmono (by omega)⟩
        rw [← htimes n]
        exact R.subdivision.wholeCell n _ _ hcell
          ⟨le_rfl, R.subdivision.mono (Nat.le_succ n)⟩
      have hblock := block_state_eq S initial (fun k => p (t k)) preferred c
        hinitial (f n) (f (n + 1) - f n)
        (select S.cover (R.preferred n) (R.chain.state n))
        (by rw [← ih]; exact select_valid _ _ _) hsmall
      dsimp only at hblock
      rw [Nat.add_sub_of_le hf, ← htimes (n + 1), ← ih] at hblock
      exact (R.chain.successor_eq n).trans (hblock (R.chain.data n)).symm

end CartanSuppliedSubdivisionTransport
end Poincare
