import Poincare.Global.CartanSuppliedSubdivisionTransport

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
namespace CartanSuppliedTerminalTransport
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanSuppliedWholeCellRealization

open CartanSuppliedSubdivisionTransport

/-- The path component of the positive mesh ball supplies short terminal paths. -/
theorem exists_short_paths : ∀ (S : System g) (x : M),
  ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
    ∀ z ∈ W, ∃ q : Path x z,
      letI : MetricSpace M := g.toMetricSpace
      ∀ t : unitInterval, dist (q t) x < S.mesh := by
  intro S x
  letI : MetricSpace M := g.toMetricSpace
  letI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace E M
  refine ⟨pathComponentIn (ball x S.mesh) x, isOpen_ball.pathComponentIn x,
    mem_pathComponentIn_self (mem_ball_self (mesh_pos S)), ?_⟩
  intro z hz
  exact ⟨hz.somePath, hz.somePath_mem⟩

/-- Every actual terminal datum has the full endpoint state of a short path. -/
theorem short_path_endpoint : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (q : Path initial.anchor y) (R : Realization S initial q),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ t : unitInterval, dist (q t) initial.anchor < S.mesh) →
  ∀ d : Data (S.cover.interp (fallback S.cover initial)) initial y,
    R.endpoint = d.successor := by
  intro S initial y q R hsmall
  have hinitial : initial.anchor = q (R.subdivision.time 0) := by
    simp [R.subdivision.zero]
  have hv : S.cover.Valid (fallback S.cover initial) initial :=
    ⟨Classical.choose_spec (S.cover.source.covers initial.anchor),
      Classical.choose_spec (S.cover.target.covers initial.target)⟩
  have hb := block_state_eq S initial (fun n => q (R.subdivision.time n))
    R.preferred R.chain hinitial 0 R.subdivision.terminal
    (fallback S.cover initial) (by rw [R.chain.initial_eq]; exact hv)
  dsimp only at hb
  simp only [Nat.zero_add, R.chain.initial_eq] at hb
  have ht := hb (fun k _ => hsmall (R.subdivision.time k))
  have transport : ∀ (s : CartanChain.ChainState g) (z : M),
      s = initial → z = y →
      (∀ d : Data (S.cover.interp (fallback S.cover initial)) s z,
        R.endpoint = d.successor) →
      ∀ d : Data (S.cover.interp (fallback S.cover initial)) initial y,
        R.endpoint = d.successor := by
    intro s z hs hz
    subst s
    subst z
    exact id
  exact transport _ _ R.chain.initial_eq
    (by simp [R.subdivision.tail _ le_rfl]) ht


/-- The second half-interval embedding used to concatenate subdivisions. -/
def secondTime (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

open CartanRootedOverlapReparameterizedBoundary (halfTime)

omit inst [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Recover the first path at its half-interval parameter. -/
theorem trans_halfTime {x y z : M} (p : Path x y) (q : Path y z)
    (t : unitInterval) : (p.trans q) (halfTime t) = p t := by
  rw [Path.trans_apply, dif_pos (by dsimp [halfTime]; linarith [t.2.2])]
  congr 1
  apply Subtype.ext
  change 2 * ((t : ℝ) / 2) = (t : ℝ)
  ring

omit inst [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Recover the second path, including the shared midpoint. -/
theorem trans_secondTime {x y z : M} (p : Path x y) (q : Path y z)
    (t : unitInterval) : (p.trans q) (secondTime t) = q t := by
  have hv : (p.trans q).extend ((secondTime t : unitInterval) : ℝ) =
      q.extend (2 * (secondTime t : ℝ) - 1) :=
    Path.extend_trans_of_half_le p q (by dsimp [secondTime]; linarith [t.2.1])
  have he : 2 * (secondTime t : ℝ) - 1 = (t : ℝ) := by dsimp [secondTime]; ring
  simpa only [he, Path.extend_extends'] using hv

/-- Concatenating whole-cell subdivisions preserves their sample nodes and mesh. -/
theorem exists_trans_subdivision {x y z : M} (p : Path x y) (q : Path y z)
    {r : ℝ} (A : Subdivision (g := g) p r) (B : Subdivision (g := g) q r) :
    ∃ D : Subdivision (g := g) (p.trans q) r,
      D.terminal = A.terminal + B.terminal ∧
      (∀ n ≤ A.terminal, D.time n = halfTime (A.time n)) ∧
      (∀ n, D.time (A.terminal + n) = secondTime (B.time n)) := by
  let times : ℕ → unitInterval := fun n =>
    if n < A.terminal then halfTime (A.time n)
    else secondTime (B.time (n - A.terminal))
  have hleft : ∀ n ≤ A.terminal, times n = halfTime (A.time n) := by
    intro n hn
    by_cases h : n < A.terminal
    · simp [times, h]
    · have he : n = A.terminal := by omega
      subst n
      simp only [times, lt_self_iff_false, ↓reduceIte, Nat.sub_self, B.zero,
        A.tail _ le_rfl]
      apply Subtype.ext
      norm_num [secondTime, halfTime]
  have hright : ∀ n, times (A.terminal + n) = secondTime (B.time n) := by
    intro n
    simp [times, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  have hright' : ∀ n, A.terminal ≤ n → times n = secondTime (B.time (n - A.terminal)) := by
    intro n hn
    simp [times, Nat.not_lt.mpr hn]
  have hmono : Monotone times := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n < A.terminal
    · rw [hleft n (by omega), hleft (n + 1) (by omega)]
      change (A.time n : ℝ) / 2 ≤ (A.time (n + 1) : ℝ) / 2
      exact div_le_div_of_nonneg_right (A.mono (Nat.le_succ n)) (by norm_num)
    · rw [hright' n (by omega), hright' (n + 1) (by omega)]
      change (1 + (B.time (n - A.terminal) : ℝ)) / 2 ≤
        (1 + (B.time (n + 1 - A.terminal) : ℝ)) / 2
      have hh := B.mono (show n - A.terminal ≤ n + 1 - A.terminal by omega)
      change (B.time (n - A.terminal) : ℝ) ≤ _ at hh
      linarith
  have hzero : times 0 = 0 := by
    rw [hleft 0 (Nat.zero_le _), A.zero]
    apply Subtype.ext
    norm_num [halfTime]
  have hstrict : ∀ n < A.terminal + B.terminal, times n < times (n + 1) := by
    intro n hn
    by_cases h : n < A.terminal
    · rw [hleft n (by omega), hleft (n + 1) (by omega)]
      change (A.time n : ℝ) / 2 < (A.time (n + 1) : ℝ) / 2
      exact div_lt_div_of_pos_right (A.strict n h) (by norm_num)
    · rw [hright' n (by omega), hright' (n + 1) (by omega)]
      have he : n + 1 - A.terminal = (n - A.terminal) + 1 := by omega
      rw [he]
      have hh := B.strict (n - A.terminal) (by omega)
      change (B.time (n - A.terminal) : ℝ) < _ at hh
      change (1 + (B.time (n - A.terminal) : ℝ)) / 2 <
        (1 + (B.time (n - A.terminal + 1) : ℝ)) / 2
      linarith
  have htail : ∀ n ≥ A.terminal + B.terminal, times n = 1 := by
    intro n hn
    rw [hright' n (by omega), B.tail _ (by omega)]
    apply Subtype.ext
    norm_num [secondTime]
  have hwhole : letI : MetricSpace M := g.toMetricSpace
      ∀ n (a b : unitInterval), a ∈ Icc (times n) (times (n + 1)) →
        b ∈ Icc (times n) (times (n + 1)) → dist ((p.trans q) a) ((p.trans q) b) < r := by
    letI : MetricSpace M := g.toMetricSpace
    intro n a b ha hb
    by_cases hn : n < A.terminal
    · rw [hleft n (by omega), hleft (n + 1) (by omega)] at ha hb
      have ha' : (A.time n : ℝ) / 2 ≤ (a : ℝ) ∧
          (a : ℝ) ≤ (A.time (n + 1) : ℝ) / 2 := ha
      have hb' : (A.time n : ℝ) / 2 ≤ (b : ℝ) ∧
          (b : ℝ) ≤ (A.time (n + 1) : ℝ) / 2 := hb
      let aa : unitInterval := ⟨2 * (a : ℝ), by constructor <;> linarith [a.2.1, (A.time (n+1)).2.2]⟩
      let bb : unitInterval := ⟨2 * (b : ℝ), by constructor <;> linarith [b.2.1, (A.time (n+1)).2.2]⟩
      have hea : halfTime aa = a := by apply Subtype.ext; dsimp [halfTime, aa]; ring
      have heb : halfTime bb = b := by apply Subtype.ext; dsimp [halfTime, bb]; ring
      rw [← hea, ← heb, trans_halfTime, trans_halfTime]
      apply A.wholeCell n aa bb
      · change (A.time n : ℝ) ≤ 2 * (a : ℝ) ∧ 2 * (a : ℝ) ≤ (A.time (n+1) : ℝ)
        constructor <;> linarith
      · change (A.time n : ℝ) ≤ 2 * (b : ℝ) ∧ 2 * (b : ℝ) ≤ (A.time (n+1) : ℝ)
        constructor <;> linarith
    · have he : n + 1 - A.terminal = (n - A.terminal) + 1 := by omega
      rw [hright' n (by omega), hright' (n + 1) (by omega), he] at ha hb
      have ha' : (1 + (B.time (n - A.terminal) : ℝ)) / 2 ≤ (a : ℝ) ∧
          (a : ℝ) ≤ (1 + (B.time (n - A.terminal + 1) : ℝ)) / 2 := ha
      have hb' : (1 + (B.time (n - A.terminal) : ℝ)) / 2 ≤ (b : ℝ) ∧
          (b : ℝ) ≤ (1 + (B.time (n - A.terminal + 1) : ℝ)) / 2 := hb
      let aa : unitInterval := ⟨2 * (a : ℝ) - 1, by constructor <;> linarith [a.2.2, (B.time (n-A.terminal)).2.1]⟩
      let bb : unitInterval := ⟨2 * (b : ℝ) - 1, by constructor <;> linarith [b.2.2, (B.time (n-A.terminal)).2.1]⟩
      have hea : secondTime aa = a := by apply Subtype.ext; dsimp [secondTime, aa]; ring
      have heb : secondTime bb = b := by apply Subtype.ext; dsimp [secondTime, bb]; ring
      rw [← hea, ← heb, trans_secondTime, trans_secondTime]
      apply B.wholeCell (n - A.terminal) aa bb
      · change (B.time (n-A.terminal) : ℝ) ≤ 2 * (a : ℝ) - 1 ∧
          2 * (a : ℝ) - 1 ≤ (B.time (n-A.terminal+1) : ℝ)
        constructor <;> linarith
      · change (B.time (n-A.terminal) : ℝ) ≤ 2 * (b : ℝ) - 1 ∧
          2 * (b : ℝ) - 1 ≤ (B.time (n-A.terminal+1) : ℝ)
        constructor <;> linarith
  exact ⟨⟨times, A.terminal + B.terminal, hzero, hmono, hstrict, htail, hwhole⟩,
    rfl, hleft, hright⟩

/-- Matching a finite segment compares full states even with a different initial state. -/
theorem segment_state_eq (S : System g) (initial middle : CartanChain.ChainState g)
    (nodes other : ℕ → M) (a b : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover a) nodes initial)
    (d : ReachableChain (policy S.cover b) other middle)
    (hc : initial.anchor = nodes 0) (hd : middle.anchor = other 0)
    (m K : ℕ) (hstart : c.state m = middle)
    (hnodes : ∀ n ≤ K, nodes (m + n) = other n) :
    (letI : MetricSpace M := g.toMetricSpace
     ∀ n < K, dist (other (n + 1)) (other n) < S.mesh) →
    ∀ n ≤ K, c.state (m + n) = d.state n := by
  letI : MetricSpace M := g.toMetricSpace
  intro hmesh n
  induction n with
  | zero => intro _; simpa using hstart.trans d.initial_eq.symm
  | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hb := block_state_eq S initial nodes a c hc (m + n) 1
        (select S.cover (b n) (d.state n)) (by rw [hi]; exact select_valid _ _ _)
      have hsmall : ∀ k ≤ 1, dist (nodes (m + n + k)) (c.state (m + n)).anchor < S.mesh := by
        intro k hk
        rw [hi, state_anchor_eq_node _ _ _ d hd]
        rcases Nat.eq_zero_or_pos k with hkzero | hkpos
        · subst k
          rw [Nat.add_zero, hnodes n (by omega), dist_self]
          exact mesh_pos S
        · have hkone : k = 1 := by omega
          subst k
          rw [Nat.add_assoc, hnodes (n + 1) hn]
          exact hmesh n (by omega)
      have hh := hb hsmall
      rw [Nat.add_assoc, hnodes (n + 1) hn, hi] at hh
      exact (hh (d.data n)).trans (d.successor_eq n).symm

end CartanSuppliedTerminalTransport
end Poincare
