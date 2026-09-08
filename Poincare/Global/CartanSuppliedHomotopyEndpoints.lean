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

/-- Iterating supplied ladders compares the boundary rows, with zero rungs
at their common endpoint preserving the full geometric state. -/
theorem grid_endpoint_eq : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} {p q : Path initial.anchor y} (H : p.Homotopy q)
    (t : ℕ → unitInterval) (k : ℕ),
  t 0 = 0 → Monotone t → (∀ n ≥ k, t n = 1) → GridSmall S H t →
  ∀ (a : ℕ → ℕ → S.cover.Label)
    (c : ∀ m, ReachableChain (policy S.cover (a m))
      (fun n => H (t m, t n)) initial),
    (c 0).state k = (c k).state k := by
  intro S initial y p q H t k htzero htmono httail hsmall a c
  letI : MetricSpace M := g.toMetricSpace
  have hleft : ∀ n, t n ∈ Icc (t n) (t (n + 1)) :=
    fun n => ⟨le_rfl, htmono (Nat.le_succ n)⟩
  have hright : ∀ n, t (n + 1) ∈ Icc (t n) (t (n + 1)) :=
    fun n => ⟨htmono (Nat.le_succ n), le_rfl⟩
  have hinitial : ∀ m, initial.anchor = H (t m, t 0) := by
    intro m; rw [htzero]; exact (H.source (t m)).symm
  have hpos := mesh_pos S
  have hadj : ∀ m, (c m).state k = (c (m + 1)).state k := by
    intro m
    have hbottom : ∀ n, dist (H (t m, t (n + 1))) (H (t m, t n)) < S.mesh :=
      fun n => hsmall m n _ _ _ _ (hleft m) (hleft m) (hright n) (hleft n)
    have hvertical : ∀ n, dist (H (t (m + 1), t n)) (H (t m, t n)) < S.mesh :=
      fun n => hsmall m n _ _ _ _ (hright m) (hleft m) (hleft n) (hleft n)
    have htop : ∀ n, dist (H (t (m + 1), t (n + 1)))
        (H (t (m + 1), t n)) < S.mesh :=
      fun n => hsmall m n _ _ _ _ (hright m) (hright m) (hright n) (hleft n)
    let label := select S.cover (a m k) ((c m).state k)
    have hvalid := select_valid S.cover (a m k) ((c m).state k)
    have hanchor := state_anchor_eq_node _ _ _ (c m) (hinitial m) k
    obtain ⟨d⟩ : Nonempty (Data (S.cover.interp label) ((c m).state k)
        (H (t (m + 1), t k))) :=
      (S.cover.h1 label.1 label.2 _
        (interior_subset (S.cover.source.core_subset label.1 hvalid.1)) _
        (interior_subset (S.cover.target.core_subset label.2 hvalid.2))
        ((c m).state k).alignment _ (by
          rw [hanchor]
          have := hvertical k
          have := (four_mul_mesh_le S).1
          linarith)).2.2.2
    have heq := ladder_state_eq S initial _ _ (a m) (a (m + 1))
      (c m) (c (m + 1)) (hinitial m) (hinitial (m + 1))
      hbottom hvertical htop k d
    have hz : H (t (m + 1), t k) = ((c m).state k).anchor := by
      rw [hanchor, httail k le_rfl, H.target, H.target]
    have hzero : ∀ z, z = ((c m).state k).anchor →
        ∀ d : Data (S.cover.interp label) ((c m).state k) z,
          d.successor = (c m).state k := by
      intro z hz d
      subst z
      exact CartanSuppliedDifferentialTransfer.patch_successor_at_anchor
        _ _ _ _ (S.cover.source.patch label.1) (S.cover.target.patch label.2)
        (S.cover.source.cutoff label.1) (S.cover.target.cutoff label.2) _ d
    exact ((heq.trans (hzero _ hz d))).symm
  have hiterate : ∀ m, (c 0).state k = (c m).state k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => exact ih.trans (hadj m)
  exact hiterate k

/-- A small homotopy grid can retain every sample of both boundary realizations.
The bounded monotone factor maps also account for repeated terminal samples. -/
theorem exists_grid_refining (S : System g) (initial : CartanChain.ChainState g)
    {y : M} {p q : Path initial.anchor y} (H : p.Homotopy q)
    (R : Realization S initial p) (T : Realization S initial q) :
    ∃ (t : ℕ → unitInterval) (k : ℕ) (f h : ℕ → ℕ),
      t 0 = 0 ∧ Monotone t ∧ (∀ n ≥ k, t n = 1) ∧ GridSmall S H t ∧
      Monotone f ∧ Monotone h ∧ f 0 = 0 ∧ h 0 = 0 ∧
      (∀ n, f n ≤ k) ∧ (∀ n, h n ≤ k) ∧
      (∀ n, R.subdivision.time n = t (f n)) ∧
      (∀ n, T.subdivision.time n = t (h n)) := by
  obtain ⟨small, smallK, hs0, hsmono, hstail, hsmall⟩ := exists_grid S H
  obtain ⟨seed, seedK, fR, fT, _hseedK, hseed0, hseedmono, hseedtail,
      hfRmono, hfTmono, hfR0, hfT0, _hfRbound, _hfTbound,
      hfRvalue, hfTvalue, _hRbracket, _hTbracket⟩ :=
    DifferentialSuccessorFiniteSubdivisionRefinement.exists_common_monotone_refinement
      R.subdivision.time T.subdivision.time R.subdivision.zero T.subdivision.zero
      R.subdivision.mono T.subdivision.mono R.subdivision.terminal T.subdivision.terminal
      R.subdivision.tail T.subdivision.tail
  obtain ⟨t, k, fseed, fsmall, _hk, ht0, htmono, httail,
      hfseedmono, _hfsmallmono, hfseed0, _hfsmall0, hfseedbound, _hfsmallbound,
      hfseedvalue, _hfsmallvalue, _hseedbracket, hsmallbracket⟩ :=
    DifferentialSuccessorFiniteSubdivisionRefinement.exists_common_monotone_refinement
      seed small hseed0 hs0 hseedmono hsmono seedK smallK hseedtail hstail
  refine ⟨t, k, fseed ∘ fR, fseed ∘ fT, ht0, htmono, httail, ?_,
    hfseedmono.comp hfRmono, hfseedmono.comp hfTmono,
    by simp [hfR0, hfseed0], by simp [hfT0, hfseed0],
    fun n => hfseedbound (fR n), fun n => hfseedbound (fT n),
    fun n => (hfRvalue n).symm.trans (hfseedvalue (fR n)).symm,
    fun n => (hfTvalue n).symm.trans (hfseedvalue (fT n)).symm⟩
  intro m n a b c d ha hb hc hd
  obtain ⟨i, hi0, hi1⟩ := hsmallbracket m
  obtain ⟨j, hj0, hj1⟩ := hsmallbracket n
  exact hsmall i j a b c d ⟨hi0.trans ha.1, ha.2.trans hi1⟩
    ⟨hi0.trans hb.1, hb.2.trans hi1⟩ ⟨hj0.trans hc.1, hc.2.trans hj1⟩
    ⟨hj0.trans hd.1, hd.2.trans hj1⟩

/-- Boundary transport includes the constant tail between an embedded terminal
sample and the grid terminal index. The sampled chain may have repeated nodes. -/
theorem endpoint_eq_sampled_chain (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p)
    (t : ℕ → unitInterval) (k : ℕ) (htzero : t 0 = 0) (htmono : Monotone t)
    (nodes : ℕ → M) (hnodes : nodes = fun n => p (t n))
    (a : ℕ → S.cover.Label) (c : ReachableChain (policy S.cover a) nodes initial)
    (f : ℕ → ℕ) (hfzero : f 0 = 0) (hfmono : Monotone f)
    (htimes : ∀ n, R.subdivision.time n = t (f n))
    (hfbound : f R.subdivision.terminal ≤ k) :
    R.endpoint = c.state k := by
  subst nodes
  have hinitial : initial.anchor = p (t 0) := by simp [htzero]
  have hR := refinement_chain_state_eq S initial p R t htzero htmono
    a c f hfzero hfmono htimes R.subdivision.terminal
  have hterminal : t (f R.subdivision.terminal) = 1 := by
    rw [← htimes, R.subdivision.tail _ le_rfl]
  have hconstant : ∀ j ≤ k - f R.subdivision.terminal,
      p (t (f R.subdivision.terminal + j)) = p (t (f R.subdivision.terminal)) := by
    intro j _hj
    have ht : t (f R.subdivision.terminal + j) = t (f R.subdivision.terminal) :=
      le_antisymm (by rw [hterminal]; exact (t _).property.2)
        (htmono (by omega))
    rw [ht]
  have hc := state_eq_of_constant_nodes S initial (fun n => p (t n))
    a c hinitial (f R.subdivision.terminal) (k - f R.subdivision.terminal) hconstant
  rw [Nat.add_sub_of_le hfbound] at hc
  exact hR.trans hc.symm

/-- Arbitrary supplied boundary realizations have equal endpoints along every
relative-endpoint path homotopy. -/
theorem endpoint_eq_of_homotopy : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    {p q : Path initial.anchor y}, p.Homotopy q →
  ∀ (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint := by
  intro S initial y p q H R T
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨t, k, f, h, htzero, htmono, httail, hsmall, hfmono, hhmono,
      hfzero, hhzero, hfbound, hhbound, hftimes, hhtimes⟩ :=
    exists_grid_refining S initial H R T
  have hinitial : ∀ m, initial.anchor = H (t m, t 0) := by
    intro m; rw [htzero]; exact (H.source (t m)).symm
  have hstep : ∀ m n, dist (H (t m, t (n + 1))) (H (t m, t n)) < S.mesh := by
    intro m n
    exact hsmall m n _ _ _ _
      ⟨le_rfl, htmono (Nat.le_succ m)⟩ ⟨le_rfl, htmono (Nat.le_succ m)⟩
      ⟨htmono (Nat.le_succ n), le_rfl⟩ ⟨le_rfl, htmono (Nat.le_succ n)⟩
  choose a c _ha _hc using
    (fun m => exists_sticky_chain S (fun n => H (t m, t n)) initial (hinitial m) (hstep m))
  have hR : R.endpoint = (c 0).state k :=
    endpoint_eq_sampled_chain S initial p R t k htzero htmono
      (fun n => H (t 0, t n)) (by funext n; simp [htzero])
      (a 0) (c 0) f hfzero hfmono hftimes (hfbound _)
  have hT : T.endpoint = (c k).state k :=
    endpoint_eq_sampled_chain S initial q T t k htzero htmono
      (fun n => H (t k, t n)) (by funext n; simp [httail k le_rfl])
      (a k) (c k) h hhzero hhmono hhtimes (hhbound _)
  exact hR.trans ((grid_endpoint_eq S initial H t k htzero htmono httail hsmall a c).trans hT.symm)

/-- Source simple connectivity supplies the sole homotopy input. -/
theorem endpoint_eq [SimplyConnectedSpace M] : ∀ (S : System g)
    (initial : CartanChain.ChainState g) {y : M}
    (p q : Path initial.anchor y)
    (R : Realization S initial p) (T : Realization S initial q),
    R.endpoint = T.endpoint := by
  intro S initial y p q R T
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p q
  exact endpoint_eq_of_homotopy S initial H R T

end CartanSuppliedHomotopyEndpoints
end Poincare
