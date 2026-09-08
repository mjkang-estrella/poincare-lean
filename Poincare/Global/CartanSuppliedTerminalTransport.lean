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

end CartanSuppliedTerminalTransport
end Poincare
