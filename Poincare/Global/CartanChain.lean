import Poincare.Global.CartanContinuation
import Poincare.Global.UniformNormalRadius
import Mathlib.Topology.Path

/-!
# Cartan continuation chains along subdivided paths

This module records the next globalization bookkeeping layer after
`CartanContinuation`.  The genuinely metric part is the compactness
subdivision: a continuous path in the unit interval admits a finite monotone
subdivision whose consecutive image points are closer than any prescribed
positive radius.  Applying the uniform normal-radius theorem gives the same
subdivision with a common normal-coordinate image for each consecutive pair.

The Cartan-chain layer is intentionally staged at the same boundary as
`CartanContinuation`: the missing rigid-10 theorem is represented by an
explicit `EqOn` compatibility between a Cartan germ and its re-anchored
successor.  The definitions below then iterate re-anchored germs and prove the
single-insertion endpoint comparison that later refinement induction will use.
-/

noncomputable section

open Metric Set
open scoped ContDiff Manifold Topology unitInterval

namespace Poincare
namespace CartanChain

universe u

section Subdivision

variable {X : Type u} [MetricSpace X]

/--
A continuous path on the compact unit interval admits a finite monotone
subdivision whose consecutive image points are closer than the prescribed
positive radius.

The subdivision is represented as a monotone sequence `t : ℕ → I` which is
eventually equal to `1`; only finitely many non-stationary intervals occur.
-/
theorem exists_monotone_unitInterval_subdivision_dist_lt
    (γ : C(I, X)) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℕ → I,
      t 0 = 0 ∧
        Monotone t ∧
          (∃ m, ∀ n ≥ m, t n = 1) ∧
            ∀ n, dist (γ (t n)) (γ (t (n + 1))) < r := by
  let c : I → Set I := fun s => γ ⁻¹' Metric.ball (γ s) (r / 2)
  have hhalf : 0 < r / 2 := half_pos hr
  have hc_open : ∀ s : I, IsOpen (c s) := by
    intro s
    exact Metric.isOpen_ball.preimage γ.continuous
  have hc_cover : (univ : Set I) ⊆ ⋃ s : I, c s := by
    intro x _hx
    refine mem_iUnion.2 ⟨x, ?_⟩
    simpa [c] using (Metric.mem_ball_self (x := γ x) hhalf)
  rcases exists_monotone_Icc_subset_open_cover_unitInterval
      (c := c) hc_open hc_cover with
    ⟨t, ht0, ht_mono, ht_eventual, ht_sub⟩
  refine ⟨t, ht0, ht_mono, ht_eventual, ?_⟩
  intro n
  rcases ht_sub n with ⟨center, hcenter⟩
  have hle : t n ≤ t (n + 1) := ht_mono (Nat.le_succ n)
  have hn : t n ∈ Icc (t n) (t (n + 1)) := ⟨le_rfl, hle⟩
  have hn_succ : t (n + 1) ∈ Icc (t n) (t (n + 1)) := ⟨hle, le_rfl⟩
  have hleft : dist (γ (t n)) (γ center) < r / 2 := by
    simpa [c] using hcenter hn
  have hright : dist (γ center) (γ (t (n + 1))) < r / 2 := by
    simpa [c, dist_comm] using hcenter hn_succ
  calc
    dist (γ (t n)) (γ (t (n + 1))) ≤
        dist (γ (t n)) (γ center) + dist (γ center) (γ (t (n + 1))) :=
      dist_triangle _ _ _
    _ < r / 2 + r / 2 := add_lt_add hleft hright
    _ = r := by rw [add_halves]

end Subdivision

section UniformNormalSubdivision

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
Uniform normal-radius subdivision for a path.  The radius is the compactness
radius from `UniformNormalRadius`; every consecutive pair in the subdivision is
closer than that radius and therefore lies in one common normal-coordinate
image.
-/
theorem exists_uniform_normal_subdivision
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (γ : C(I, M)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), ∃ t : ℕ → I,
      t 0 = 0 ∧
        Monotone t ∧
          (∃ m, ∀ n ≥ m, t n = 1) ∧
            (∀ n, dist (γ (t n)) (γ (t (n + 1))) < r) ∧
              ∀ n, ∃ x₀ : M,
                γ (t n) ∈ GeodesicTransport.normalCoordinateImage g x₀ ∧
                  γ (t (n + 1)) ∈
                    GeodesicTransport.normalCoordinateImage g x₀ := by
  letI : MetricSpace M := g.toMetricSpace
  rcases GeodesicTransport.exists_uniform_common_normalCoordinateImage_of_dist_lt
      (g := g) with
    ⟨r, hr_pos, hr_common⟩
  rcases exists_monotone_unitInterval_subdivision_dist_lt
      (γ := γ) hr_pos with
    ⟨t, ht0, ht_mono, ht_eventual, ht_close⟩
  refine ⟨r, hr_pos, t, ht0, ht_mono, ht_eventual, ht_close, ?_⟩
  intro n
  exact hr_common (γ (t n)) (γ (t (n + 1))) (ht_close n)

end UniformNormalSubdivision

section Chains

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]
variable (g : ClosedSmoothRiemannianMetric 3 M)

/-- One Cartan continuation state: an anchor, its continued target value, and a tangent alignment. -/
structure ChainState where
  anchor : M
  target : RoundSphere3
  alignment : CartanMap.TangentAlignment g anchor target

namespace ChainState

variable {g}

/-- The open Cartan germ carried by a chain state. -/
def germ (s : ChainState g) : OpenPartialHomeomorph M RoundSphere3 :=
  CartanMap.openPartialHomeomorph g s.anchor s.target s.alignment

/-- The total Cartan map carried by a chain state. -/
def map (s : ChainState g) : M → RoundSphere3 :=
  CartanMap.cartanMap g s.anchor s.target s.alignment

/--
The re-anchored successor state at a new source point.  The target is supplied
by the previous state's Cartan map, and tangent-alignment existence supplies the
new alignment.
-/
def next (s : ChainState g) (x₁ : M) : ChainState g where
  anchor := x₁
  target := s.map x₁
  alignment :=
    Classical.choice
      (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := x₁) (p₀ := s.map x₁))

@[simp]
theorem next_anchor (s : ChainState g) (x₁ : M) :
    (s.next x₁).anchor = x₁ :=
  rfl

@[simp]
theorem next_target (s : ChainState g) (x₁ : M) :
    (s.next x₁).target = s.map x₁ :=
  rfl

@[simp]
theorem germ_next (s : ChainState g) (x₁ : M) :
    (s.next x₁).germ =
      CartanContinuation.reanchoredOpenPartialHomeomorph
        g s.anchor s.target s.alignment x₁
        (Classical.choice
          (CartanMap.tangentAlignment_nonempty
            (g := g) (x₀ := x₁) (p₀ := s.map x₁))) :=
  rfl

/--
Rigid-10 staging hypothesis for one chain step: the current germ and its
re-anchored successor agree on their common source.  This is the exact `EqOn`
shape consumed by `CartanContinuation.twoStep_*`.
-/
def RigidStepCompatible (s : ChainState g) (x₁ : M) : Prop :=
  EqOn s.germ (s.next x₁).germ (s.germ.source ∩ (s.next x₁).germ.source)

/-- The restricted-source two-step conclusion from the rigid staging hypothesis. -/
theorem next_restr_eqOnSource_of_rigidStepCompatible
    {s : ChainState g} {x₁ : M} (h : RigidStepCompatible s x₁) :
    s.germ.restr (s.next x₁).germ.source ≈
      (s.next x₁).germ.restr s.germ.source := by
  simpa [RigidStepCompatible, germ, next, map,
    CartanContinuation.reanchoredOpenPartialHomeomorph] using
    CartanContinuation.twoStep_restr_eqOnSource_of_differential_action
      (g := g) (x₀ := s.anchor) (p₀ := s.target) (L₀ := s.alignment)
      (x₁ := x₁)
      (L₁ := Classical.choice
        (CartanMap.tangentAlignment_nonempty
          (g := g) (x₀ := x₁) (p₀ := s.map x₁)))
      h

/-- Pointwise two-step equality for the successor Cartan map on the common source. -/
theorem next_map_eq_of_rigidStepCompatible
    {s : ChainState g} {x₁ x₂ : M} (h : RigidStepCompatible s x₁)
    (hx₂ : x₂ ∈ s.germ.source ∩ (s.next x₁).germ.source) :
    (s.next x₁).map x₂ = s.map x₂ := by
  simpa [RigidStepCompatible, germ, next, map,
    CartanContinuation.reanchoredOpenPartialHomeomorph] using
    CartanContinuation.twoStep_cartanMap_eq_of_differential_action
      (g := g) (x₀ := s.anchor) (p₀ := s.target) (L₀ := s.alignment)
      (x₁ := x₁) (x₂ := x₂)
      (L₁ := Classical.choice
        (CartanMap.tangentAlignment_nonempty
          (g := g) (x₀ := x₁) (p₀ := s.map x₁)))
      h hx₂

end ChainState

/-- The initial chain state at the base anchor and target. -/
def initialState (x₀ : M) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g x₀ p₀) : ChainState g where
  anchor := x₀
  target := p₀
  alignment := L₀

/-- Iterate re-anchoring over a sequence of source nodes. -/
def chainState (nodes : ℕ → M) (initial : ChainState g) : ℕ → ChainState g
  | 0 => initial
  | n + 1 => (chainState nodes initial n).next (nodes (n + 1))

@[simp]
theorem chainState_zero (nodes : ℕ → M) (initial : ChainState g) :
    chainState g nodes initial 0 = initial :=
  rfl

@[simp]
theorem chainState_succ (nodes : ℕ → M) (initial : ChainState g) (n : ℕ) :
    chainState g nodes initial (n + 1) =
      (chainState g nodes initial n).next (nodes (n + 1)) :=
  rfl

/-- The Cartan germ at the `n`th state of an iterated chain. -/
def chainGerm (nodes : ℕ → M) (initial : ChainState g) (n : ℕ) :
    OpenPartialHomeomorph M RoundSphere3 :=
  (chainState g nodes initial n).germ

/-- Rigid-10 compatibility for every step in an iterated chain. -/
def ChainRigidCompatible (nodes : ℕ → M) (initial : ChainState g) : Prop :=
  ∀ n, (chainState g nodes initial n).RigidStepCompatible (nodes (n + 1))

/-- Every rigid-compatible chain step has the two-step restricted-source agreement. -/
theorem chain_step_restr_eqOnSource
    {nodes : ℕ → M} {initial : ChainState g}
    (h : ChainRigidCompatible g nodes initial) (n : ℕ) :
    (chainGerm g nodes initial n).restr (chainGerm g nodes initial (n + 1)).source ≈
      (chainGerm g nodes initial (n + 1)).restr
        (chainGerm g nodes initial n).source := by
  simpa [chainGerm] using
    ChainState.next_restr_eqOnSource_of_rigidStepCompatible
      (g := g) (s := chainState g nodes initial n) (x₁ := nodes (n + 1)) (h n)

/-- Chain states along a path subdivision `t : ℕ → I`. -/
def pathChainState (γ : C(I, M)) (t : ℕ → I) (p₀ : RoundSphere3)
    (L₀ : CartanMap.TangentAlignment g (γ (t 0)) p₀) : ℕ → ChainState g :=
  chainState g (fun n => γ (t n)) (initialState g (γ (t 0)) p₀ L₀)

/--
The endpoint target value is unchanged by inserting one intermediate anchor,
provided the original germ and the inserted re-anchored germ agree on the
common source containing the endpoint.
-/
theorem endpoint_target_eq_insert
    {s : ChainState g} {y z : M}
    (h : s.RigidStepCompatible y)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source) :
    (s.next z).target = ((s.next y).next z).target := by
  have hmap :
      (s.next y).map z = s.map z :=
    ChainState.next_map_eq_of_rigidStepCompatible (g := g) h hz
  simpa [ChainState.next] using hmap.symm

/--
Single-insertion endpoint germ comparison.  The two endpoint targets agree by
two-step compatibility; equality of the endpoint tangent-alignment data is the
remaining rigid/determinacy input needed to identify the endpoint germs.
-/
theorem endpoint_germ_eq_insert_of_alignment
    {s : ChainState g} {y z : M}
    (h : s.RigidStepCompatible y)
    (hz : z ∈ s.germ.source ∩ (s.next y).germ.source)
    (hL : HEq (s.next z).alignment ((s.next y).next z).alignment) :
    (s.next z).germ = ((s.next y).next z).germ := by
  have hp : (s.next z).target = ((s.next y).next z).target :=
    endpoint_target_eq_insert (g := g) h hz
  simpa [ChainState.germ, ChainState.next] using
    CartanContinuation.openPartialHomeomorph_eq_of_anchor_data_eq
      (g := g) (x₀ := z)
      (p₁ := (s.next z).target)
      (p₂ := ((s.next y).next z).target)
      hp
      (L₁ := (s.next z).alignment)
      (L₂ := ((s.next y).next z).alignment)
      hL

end Chains

end CartanChain
end Poincare
