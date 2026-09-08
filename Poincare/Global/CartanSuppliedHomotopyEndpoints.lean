import Poincare.Global.CartanSuppliedSubdivisionTransport
import Poincare.Global.DifferentialSuccessorAdjacentContinuation

/-!
# Homotopy invariance of supplied endpoints

Closed grid cells control all their points before any supplied chain is chosen.
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
namespace CartanSuppliedHomotopyEndpoints
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization CartanSuppliedSubdivisionTransport

def GridSmall (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q) (t : ℕ → unitInterval) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m n (a b c d : unitInterval),
    a ∈ Icc (t m) (t (m + 1)) → b ∈ Icc (t m) (t (m + 1)) →
    c ∈ Icc (t n) (t (n + 1)) → d ∈ Icc (t n) (t (n + 1)) →
    dist (H (a, c)) (H (b, d)) < S.mesh

/-- Half-mesh balls on the compact homotopy image give pairwise closed-cell control. -/
theorem exists_grid : ∀ (S : System g) {x y : M} {p q : Path x y}
    (H : p.Homotopy q),
  ∃ (t : ℕ → unitInterval) (k : ℕ), t 0 = 0 ∧ Monotone t ∧
    (∀ n ≥ k, t n = 1) ∧ GridSmall S H t := by
  intro S x y p q H
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨t, htzero, htmono, ⟨k, httail⟩, hcell⟩ :=
    DifferentialSuccessorAdjacentContinuation.exists_homotopy_metricBall_grid
      g H.toContinuousMap (fun z : unitInterval × unitInterval => H z)
      (fun _ => S.mesh / 2) (fun z => ⟨z, by simpa using half_pos (mesh_pos S)⟩)
  refine ⟨t, k, htzero, htmono, httail, ?_⟩
  intro m n a b c d ha hb hc hd
  obtain ⟨z, hz⟩ := hcell m n
  have h₁ := hz a ha c hc
  have h₂ := hz b hb d hd
  change dist (H (a, c)) (H z) < S.mesh / 2 at h₁
  change dist (H (b, d)) (H z) < S.mesh / 2 at h₂
  have := dist_triangle_right (H (a, c)) (H (b, d)) (H z)
  linarith

/-- Vertical supplied data identifies every upper-row state. The two transition
balls are produced from H2 and patch switching at the actual reached states. -/
theorem ladder_state_eq (S : System g) (initial : CartanChain.ChainState g)
    (u v : ℕ → M) (a b : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover a) u initial)
    (e : ReachableChain (policy S.cover b) v initial)
    (hu : initial.anchor = u 0) (hv : initial.anchor = v 0) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ n, dist (u (n + 1)) (u n) < S.mesh) →
    (∀ n, dist (v n) (u n) < S.mesh) →
    (∀ n, dist (v (n + 1)) (v n) < S.mesh) →
    ∀ n, ∀ d : Data (policy S.cover a n (c.state n)) (c.state n) (v n),
      e.state n = d.successor := by
  letI : MetricSpace M := g.toMetricSpace
  intro hbottom hvertical htop
  have hpos := mesh_pos S
  have hanchor := state_anchor_eq_node _ _ _ c hu
  have hsupply : ∀ n, Nonempty
      (Data (policy S.cover a n (c.state n)) (c.state n) (v n)) := by
    intro n
    let label := select S.cover (a n) (c.state n)
    have hvalid := select_valid S.cover (a n) (c.state n)
    exact (S.cover.h1 label.1 label.2 _
      (interior_subset (S.cover.source.core_subset label.1 hvalid.1)) _
      (interior_subset (S.cover.target.core_subset label.2 hvalid.2))
      (c.state n).alignment (v n) (by
        rw [hanchor]
        have := (four_mul_mesh_le S).1
        have := hvertical n
        linarith)).2.2.2
  intro n
  induction n with
  | zero =>
      intro d
      have hz : v 0 = (c.state 0).anchor := hv.symm.trans (hanchor 0 |>.trans hu.symm).symm
      let label := select S.cover (a 0) (c.state 0)
      have hzero : ∀ z, z = (c.state 0).anchor →
          ∀ d : Data (S.cover.interp label) (c.state 0) z,
            d.successor = c.state 0 := by
        intro z hz d
        subst z
        exact CartanSuppliedDifferentialTransfer.patch_successor_at_anchor
          _ _ _ _ (S.cover.source.patch label.1) (S.cover.target.patch label.2)
          (S.cover.source.cutoff label.1) (S.cover.target.cutoff label.2) _ d
      exact (e.initial_eq.trans c.initial_eq.symm).trans (hzero _ hz d).symm
  | succ n ih =>
      intro d
      obtain ⟨r⟩ := hsupply n
      have hr := ih r
      let A := select S.cover (a n) (c.state n)
      let B := select S.cover (a (n + 1)) (c.state (n + 1))
      let C := select S.cover (b n) (e.state n)
      have hA : S.cover.Valid A (c.state n) := select_valid _ _ _
      have hB : S.cover.Valid B (c.data n).successor := by
        rw [← c.successor_eq n]; exact select_valid _ _ _
      have hC : S.cover.Valid C r.successor := by
        rw [← hr]; exact select_valid _ _ _
      have hbot := (transition_eqOn S A B (c.state n) (u (n + 1))
        (c.data n) hA hB (by rw [hanchor]; have := hbottom n; linarith)).2
      have hrung := (transition_eqOn S A C (c.state n) (v n)
        r hA hC (by rw [hanchor]; have := hvertical n; linarith)).2
      have hbot' : EqOn (map (policy S.cover a n (c.state n)) (c.state n))
          (map (policy S.cover a (n + 1) (c.state (n + 1))) (c.state (n + 1)))
          (ball (u (n + 1)) (4 * S.mesh)) := by
        change EqOn _ (map (S.cover.interp B) _) _
        rw [c.successor_eq n]
        exact hbot
      have hrung' : EqOn (map (policy S.cover a n (c.state n)) (c.state n))
          (map (policy S.cover b n (e.state n)) (e.state n))
          (ball (v n) (4 * S.mesh)) := by
        change EqOn _ (map (S.cover.interp C) _) _
        rw [hr]
        exact hrung
      let W := ball (u (n + 1)) (4 * S.mesh) ∩ ball (v n) (4 * S.mesh)
      have hW : IsOpen W := isOpen_ball.inter isOpen_ball
      have hz : v (n + 1) ∈ W := by
        constructor
        · rw [mem_ball]; have := hvertical (n + 1); linarith
        · rw [mem_ball]; have := htop n; linarith
      have heq : EqOn (map (policy S.cover b n (e.state n)) (e.state n))
          (map (policy S.cover a (n + 1) (c.state (n + 1))) (c.state (n + 1))) W :=
        fun z hz => (hrung' hz.2).symm.trans (hbot' hz.1)
      rw [e.successor_eq n]
      exact CartanSuppliedDifferentialTransfer.successor_eq_of_eqOn_open
        _ _ _ _ _ (e.data n) d W hW hz heq

end CartanSuppliedHomotopyEndpoints
end Poincare
