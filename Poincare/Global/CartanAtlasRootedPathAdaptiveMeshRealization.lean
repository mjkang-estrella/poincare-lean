import Poincare.Global.CartanAtlasRootedPathSkeleton
import Poincare.Global.CartanAtlasRootedAdaptiveClosenessTransport
import Poincare.Global.DifferentialSuccessorZero
import Poincare.Global.DifferentialSuccessorFiniteSubdivisionRefinement
import Mathlib.Topology.UnitInterval

/-!
# Rooted path realization from pointwise adaptive successor radii

This module discharges the compact path-image part of the rooted Cartan
continuation problem.  A positive successor radius is allowed to vary from
point to point along a path.  The Lebesgue-number subdivision of the unit
interval selects finitely many of those local balls; their finite infimum is
a common positive mesh datum.

The chain construction is history-sensitive.  Its local hypothesis asks for
successor data only from states anchored at the left endpoint of the current
cell.  A dependent recursion then selects data at the one state actually
reached.  It does not use the older `StepAvailable` policy at states with an
unrelated anchor.  After the terminal subdivision index, the sampled path is
stationary and the canonical zero-vector datum supplies the infinite tail
required by `ReachableChain`.

The remaining geometric input is visible in
`hlocal`: a radius selected at a path point must work for every continuation
history whose actual anchor is the left sample in that local ball.  Thus the
theorems below remove the compactness and finite-minimum bookkeeping without
claiming that constant curvature alone has already established the required
uniformity across changing histories.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanAtlasRootedPathAdaptiveMeshRealization

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedReachableEndpointTransport
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteSubdivisionRefinement

section PointwiseMetricSubdivision

variable {X : Type v} [MetricSpace X]

/--
A positive radius at every point of a compact path has a finite subordinate
subdivision.  In addition to the usual monotone, eventually-terminal sample
sequence, the theorem retains one center for each relevant cell and a common
positive lower bound for the finitely many selected radii.

The cell conclusion controls the whole path image of the parameter interval,
not merely its two endpoints.  This is the form needed by later insertion and
homotopy refinements.
-/
theorem exists_monotone_subdivision_subordinate_to_pointwise_path_balls
    (gamma : C(unitInterval, X)) (radius : unitInterval -> Real)
    (hradius : forall u : unitInterval, 0 < radius u) :
    exists (t : Nat -> unitInterval) (k : Nat)
        (center : Fin (k + 1) -> unitInterval) (eta : Real),
      t 0 = 0 ∧
        Monotone t ∧
          (∀ n ≥ k, t n = 1) ∧
            0 < eta ∧
              (forall i : Fin (k + 1), eta <= radius (center i)) ∧
                forall (i : Fin (k + 1)) (u : unitInterval),
                  u ∈ Icc (t i) (t (i + 1)) ->
                    dist (gamma u) (gamma (center i)) < radius (center i) := by
  classical
  let cover : unitInterval -> Set unitInterval := fun c =>
    gamma ⁻¹' Metric.ball (gamma c) (radius c)
  have hopen : forall c : unitInterval, IsOpen (cover c) := by
    intro c
    exact Metric.isOpen_ball.preimage gamma.continuous
  have hcover : (Set.univ : Set unitInterval) ⊆ ⋃ c, cover c := by
    intro u _hu
    refine Set.mem_iUnion.2 <| Exists.intro u ?_
    simpa [cover] using
      (Metric.mem_ball_self (x := gamma u) (hradius u))
  rcases exists_monotone_Icc_subset_open_cover_unitInterval
      (c := cover) hopen hcover with
    ⟨t, htzero, htmono, ⟨k, htone⟩, hcell⟩
  choose selected hselected using hcell
  let selectedRadius : Fin (k + 1) -> Real := fun i => radius (selected i)
  let eta : Real :=
    Finset.univ.inf' Finset.univ_nonempty selectedRadius
  have heta : 0 < eta := by
    dsimp [eta]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius (selected i)
  refine ⟨t, k, fun i => selected i, eta, htzero, htmono, htone,
    heta, ?_, ?_⟩
  · intro i
    dsimp [eta, selectedRadius]
    exact Finset.inf'_le selectedRadius (Finset.mem_univ i)
  · intro i u hu
    simpa [cover] using hselected i hu

end PointwiseMetricSubdivision

section FiniteRealizedChain

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Extend a finite supply of successor data at correctly anchored states to an
infinite `ReachableChain` when the node sequence is stationary after `k`.

The dependent state recursion carries the invariant `state.anchor = nodes n`.
Consequently `hstep` is invoked only at the actual recursively reached state.
For `n ≥ k`, stationarity identifies the next node with that anchor and
`DifferentialSuccessorZero.anchorData` supplies the step.
-/
noncomputable def reachableChain_of_finite_anchored_step_supply
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : Nat -> M) (initial : CartanChain.ChainState g) (k : Nat)
    (hinitial : initial.anchor = nodes 0)
    (hstationary : ∀ n ≥ k, nodes n = nodes k)
    (hstep : forall i : Fin k, forall s : CartanChain.ChainState g,
      s.anchor = nodes i -> Nonempty (Data s (nodes (i + 1)))) :
    ReachableChain nodes initial := by
  classical
  let stepData : forall (n : Nat) (s : CartanChain.ChainState g),
      s.anchor = nodes n -> Data s (nodes (n + 1)) := by
    intro n s hs
    by_cases hn : n < k
    · exact Classical.choice (hstep ⟨n, hn⟩ s hs)
    · have hkn : k <= n := Nat.le_of_not_gt hn
      have hnext : nodes (n + 1) = nodes n := by
        calc
          nodes (n + 1) = nodes k :=
            hstationary (n + 1) (hkn.trans (Nat.le_succ n))
          _ = nodes n := (hstationary n hkn).symm
      have hnextAnchor : nodes (n + 1) = s.anchor :=
        hnext.trans hs.symm
      simpa only [hnextAnchor] using DifferentialSuccessorZero.anchorData s
  let state : forall n : Nat,
      {s : CartanChain.ChainState g // s.anchor = nodes n} := by
    intro n
    induction n with
    | zero => exact ⟨initial, hinitial⟩
    | succ n state_n =>
        let d := stepData n state_n.1 state_n.2
        exact ⟨d.successor, d.successor_anchor⟩
  refine
    { state := fun n => (state n).1
      initial_eq := rfl
      data := fun n => stepData n (state n).1 (state n).2
      successor_eq := ?_ }
  intro n
  rfl

end FiniteRealizedChain

section PathRealization

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/--
Pointwise, history-compatible successor radii produce one finite realized
chain along a path, together with a common positive mesh datum for all of its
selected cells.

`hlocal c u v s` is local rather than globally uniform: its radius depends on
the selected center `c`.  It quantifies only over predecessor states anchored
at the actual left path point `gamma u`.  The output chain itself stores data
only on the recursively realized history.
-/
theorem exists_reachableChain_with_common_pointwise_mesh_of_successor_radii
    (g : ClosedSmoothRiemannianMetric 3 M)
    (gamma : C(unitInterval, M)) (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = gamma 0) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : unitInterval -> Real),
      (forall c : unitInterval, 0 < radius c) ->
      (forall (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < radius c ->
        dist (gamma v) (gamma c) < radius c ->
        s.anchor = gamma u ->
          Nonempty (Data s (gamma v))) ->
      exists (t : Nat -> unitInterval) (k : Nat)
          (center : Fin (k + 1) -> unitInterval) (eta : Real),
        t 0 = 0 ∧
          Monotone t ∧
            (∀ n ≥ k, t n = 1) ∧
              0 < eta ∧
                (forall i : Fin (k + 1), eta <= radius (center i)) ∧
                  (forall (i : Fin (k + 1)) (u : unitInterval),
                    u ∈ Icc (t i) (t (i + 1)) ->
                      dist (gamma u) (gamma (center i)) < radius (center i)) ∧
                    Nonempty
                      (ReachableChain (fun n => gamma (t n)) initial) := by
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal
  rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
      gamma radius hradius with
    ⟨t, k, center, eta, htzero, htmono, htone, heta, hetaLower,
      hcell⟩
  have hfinite : forall i : Fin k, forall s : CartanChain.ChainState g,
      s.anchor = gamma (t i) ->
        Nonempty (Data s (gamma (t (i + 1)))) := by
    intro i s hs
    let i' : Fin (k + 1) := i.castSucc
    have hle : t i <= t (i + 1) := htmono (Nat.le_succ i)
    have hleft :
        dist (gamma (t i)) (gamma (center i')) < radius (center i') :=
      hcell i' (t i) ⟨le_rfl, hle⟩
    have hright :
        dist (gamma (t (i + 1))) (gamma (center i')) < radius (center i') :=
      hcell i' (t (i + 1)) ⟨hle, le_rfl⟩
    exact hlocal (center i') (t i) (t (i + 1)) s hleft hright hs
  have hstationary : ∀ n ≥ k,
      gamma (t n) = gamma (t k) := by
    intro n hn
    rw [htone n hn, htone k le_rfl]
  have hchain : ReachableChain (fun n => gamma (t n)) initial :=
    reachableChain_of_finite_anchored_step_supply
      (fun n => gamma (t n)) initial k (by simpa [htzero] using hinitial)
        hstationary hfinite
  exact ⟨t, k, center, eta, htzero, htmono, htone, heta, hetaLower,
    hcell, ⟨hchain⟩⟩

/--
The pointwise-radius realization can be chosen with every adjacent sampled
path edge smaller than the same positive finite-history minimum `eta`.

First choose a cover-subordinate subdivision and take the finite infimum of
its selected local radii.  Independently choose a subdivision subordinate to
constant balls of radius `eta / 2`, then take the finite sorted common
refinement.  Each refined cell remains inside one original successor cell,
while its two endpoint images lie in one `eta / 2` ball.  Thus the refined
nodes both realize a chain and satisfy the uniform strict metric bound.
-/
theorem exists_reachableChain_with_uniform_small_mesh_of_successor_radii
    (g : ClosedSmoothRiemannianMetric 3 M)
    (gamma : C(unitInterval, M)) (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = gamma 0) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : unitInterval -> Real),
      (forall c : unitInterval, 0 < radius c) ->
      (forall (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < radius c ->
        dist (gamma v) (gamma c) < radius c ->
        s.anchor = gamma u ->
          Nonempty (Data s (gamma v))) ->
      exists (t : Nat -> unitInterval) (k : Nat) (eta : Real),
        0 < k ∧
          t 0 = 0 ∧
            Monotone t ∧
              (∀ n ≥ k, t n = 1) ∧
                0 < eta ∧
                  (exists c : unitInterval, eta <= radius c) ∧
                    (forall n : Nat,
                      dist (gamma (t n)) (gamma (t (n + 1))) < eta) ∧
                      Nonempty
                        (ReachableChain (fun n => gamma (t n)) initial) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal
  rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
      gamma radius hradius with
    ⟨seed, seedK, seedCenter, eta, hseedZero, hseedMono, hseedOne,
      heta, hetaLower, hseedCell⟩
  have hhalf : 0 < eta / 2 := half_pos heta
  rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
      gamma (fun _ => eta / 2) (fun _ => hhalf) with
    ⟨fine, fineK, fineCenter, _fineMinimum, hfineZero, hfineMono,
      hfineOne, _hfineMinimumPos, _hfineMinimumLower, hfineCell⟩
  rcases exists_common_monotone_refinement
      seed fine hseedZero hfineZero hseedMono hfineMono seedK fineK
        hseedOne hfineOne with
    ⟨t, k, _seedFactor, _fineFactor, hk, htzero, htmono, htone,
      _hseedFactorMono, _hfineFactorMono, _hseedFactorZero,
      _hfineFactorZero, _hseedFactorBound, _hfineFactorBound,
      _hseedFactorValue, _hfineFactorValue, hseedBracket,
      hfineBracket⟩
  have hsuccessorCell : forall n : Nat, exists c : unitInterval,
      eta <= radius c ∧
        dist (gamma (t n)) (gamma c) < radius c ∧
          dist (gamma (t (n + 1))) (gamma c) < radius c := by
    intro n
    rcases hseedBracket n with ⟨j, hjleft, hjright⟩
    by_cases hj : j <= seedK
    · let i : Fin (seedK + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
      have hnmem : t n ∈ Icc (seed i) (seed (i + 1)) :=
        ⟨hjleft, (htmono (Nat.le_succ n)).trans hjright⟩
      have hnextmem : t (n + 1) ∈ Icc (seed i) (seed (i + 1)) :=
        ⟨hjleft.trans (htmono (Nat.le_succ n)), hjright⟩
      exact ⟨seedCenter i, hetaLower i,
        hseedCell i (t n) hnmem,
        hseedCell i (t (n + 1)) hnextmem⟩
    · have hseedKj : seedK <= j := le_of_not_ge hj
      have hone_le : (1 : unitInterval) <= t n := by
        simpa [hseedOne j hseedKj] using hjleft
      have htn : t n = 1 := le_antisymm (t n).property.2 hone_le
      have htnext : t (n + 1) = 1 := by
        apply Subtype.ext
        exact le_antisymm (t (n + 1)).property.2
          (hone_le.trans (htmono (Nat.le_succ n)))
      let last : Fin (seedK + 1) := Fin.last seedK
      have honeMem : (1 : unitInterval) ∈
          Icc (seed last) (seed (last + 1)) := by
        simpa [last, hseedOne seedK le_rfl,
          hseedOne (seedK + 1) (Nat.le_succ seedK)]
      have hterminalClose := hseedCell last 1 honeMem
      exact ⟨seedCenter last, hetaLower last,
        by simpa [htn] using hterminalClose,
        by simpa [htnext] using hterminalClose⟩
  have hfinite : forall i : Fin k, forall s : CartanChain.ChainState g,
      s.anchor = gamma (t i) ->
        Nonempty (Data s (gamma (t (i + 1)))) := by
    intro i s hs
    rcases hsuccessorCell i with ⟨c, _hetaRadius, hleft, hright⟩
    exact hlocal c (t i) (t (i + 1)) s hleft hright hs
  have hstationary : ∀ n ≥ k,
      gamma (t n) = gamma (t k) := by
    intro n hn
    rw [htone n hn, htone k le_rfl]
  have hchain : ReachableChain (fun n => gamma (t n)) initial :=
    reachableChain_of_finite_anchored_step_supply
      (fun n => gamma (t n)) initial k (by simpa [htzero] using hinitial)
        hstationary hfinite
  have hsmall : forall n : Nat,
      dist (gamma (t n)) (gamma (t (n + 1))) < eta := by
    intro n
    rcases hfineBracket n with ⟨j, hjleft, hjright⟩
    by_cases hj : j <= fineK
    · let i : Fin (fineK + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
      have hnmem : t n ∈ Icc (fine i) (fine (i + 1)) :=
        ⟨hjleft, (htmono (Nat.le_succ n)).trans hjright⟩
      have hnextmem : t (n + 1) ∈ Icc (fine i) (fine (i + 1)) :=
        ⟨hjleft.trans (htmono (Nat.le_succ n)), hjright⟩
      have hleft := hfineCell i (t n) hnmem
      have hright := hfineCell i (t (n + 1)) hnextmem
      calc
        dist (gamma (t n)) (gamma (t (n + 1))) <=
            dist (gamma (t n)) (gamma (fineCenter i)) +
              dist (gamma (t (n + 1))) (gamma (fineCenter i)) :=
          dist_triangle_right _ _ _
        _ < eta / 2 + eta / 2 := add_lt_add hleft hright
        _ = eta := by ring
    · have hfineKj : fineK <= j := le_of_not_ge hj
      have hone_le : (1 : unitInterval) <= t n := by
        simpa [hfineOne j hfineKj] using hjleft
      have htn : t n = 1 := le_antisymm (t n).property.2 hone_le
      have htnext : t (n + 1) = 1 := by
        apply Subtype.ext
        exact le_antisymm (t (n + 1)).property.2
          (hone_le.trans (htmono (Nat.le_succ n)))
      simpa [htn, htnext] using heta
  exact ⟨t, k, eta, hk, htzero, htmono, htone, heta,
    ⟨seedCenter 0, hetaLower 0⟩, hsmall, ⟨hchain⟩⟩

/--
The realized subdivision may be required to have any prescribed positive
metric mesh.  Clip every pointwise successor radius by `mesh / 2` and apply
the common-refinement theorem above.  Its finite minimum is bounded by the
clipped radius at one selected center, hence is strictly smaller than `mesh`.

This is the useful quantifier order for rooted construction: no positive
lower bound over all path points or all source points is needed.  Compactness
is applied separately to each fixed path after the requested mesh has been
chosen.
-/
theorem exists_reachableChain_with_prescribed_mesh_of_successor_radii
    (g : ClosedSmoothRiemannianMetric 3 M)
    (gamma : C(unitInterval, M)) (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = gamma 0) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : unitInterval -> Real),
      (forall c : unitInterval, 0 < radius c) ->
      (forall (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < radius c ->
        dist (gamma v) (gamma c) < radius c ->
        s.anchor = gamma u ->
          Nonempty (Data s (gamma v))) ->
      forall mesh : Real, 0 < mesh ->
        exists (t : Nat -> unitInterval) (k : Nat),
          0 < k ∧
            t 0 = 0 ∧
              Monotone t ∧
                (∀ n ≥ k, t n = 1) ∧
                  (forall n : Nat,
                    dist (gamma (t n)) (gamma (t (n + 1))) < mesh) ∧
                    Nonempty
                      (ReachableChain (fun n => gamma (t n)) initial) := by
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal mesh hmesh
  let clipped : unitInterval -> Real := fun c => min (radius c) (mesh / 2)
  have hclipped : forall c : unitInterval, 0 < clipped c := by
    intro c
    exact lt_min (hradius c) (half_pos hmesh)
  have hlocalClipped :
      forall (c u v : unitInterval) (s : CartanChain.ChainState g),
        dist (gamma u) (gamma c) < clipped c ->
        dist (gamma v) (gamma c) < clipped c ->
        s.anchor = gamma u ->
          Nonempty (Data s (gamma v)) := by
    intro c u v s hu hv hs
    apply hlocal c u v s
    · exact hu.trans_le (min_le_left _ _)
    · exact hv.trans_le (min_le_left _ _)
    · exact hs
  rcases exists_reachableChain_with_uniform_small_mesh_of_successor_radii
      g gamma initial hinitial clipped hclipped hlocalClipped with
    ⟨t, k, eta, hk, htzero, htmono, htone, heta,
      ⟨c, hetaClipped⟩, hsmall, hchain⟩
  have hetaMesh : eta < mesh := by
    calc
      eta <= clipped c := hetaClipped
      _ <= mesh / 2 := min_le_right _ _
      _ < mesh := half_lt_self hmesh
  exact ⟨t, k, hk, htzero, htmono, htone,
    fun n => (hsmall n).trans hetaMesh, hchain⟩

/--
Apply the one-path construction simultaneously to every path in an automatic
rooted skeleton.  Classical choice is used only after the per-path compactness
theorem has produced a finite realized chain.

The conclusion retains, for every path, its selected cell centers and the
common positive finite minimum of their radii.  Its first component is exactly
the `RootedPathChainRealization` consumed by rooted endpoint transport.
-/
theorem exists_rootedPathChainRealization_with_common_pointwise_mesh_of_successor_radii
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : M -> unitInterval -> Real),
      (forall x : M, forall c : unitInterval, 0 < radius x c) ->
      (forall (x : M) (c u v : unitInterval)
          (s : CartanChain.ChainState g),
        dist (skeleton.path x u) (skeleton.path x c) < radius x c ->
        dist (skeleton.path x v) (skeleton.path x c) < radius x c ->
        s.anchor = skeleton.path x u ->
          Nonempty (Data s (skeleton.path x v))) ->
      exists realization : RootedPathChainRealization skeleton,
        exists center : forall x : M,
            Fin (realization.terminalIndex x + 1) -> unitInterval,
          exists eta : M -> Real,
            (forall x : M, 0 < eta x) ∧
              (forall x : M,
                forall i : Fin (realization.terminalIndex x + 1),
                  eta x <= radius x (center x i)) ∧
                forall (x : M)
                    (i : Fin (realization.terminalIndex x + 1))
                    (u : unitInterval),
                  u ∈ Icc (realization.nodeTime x i)
                    (realization.nodeTime x (i + 1)) ->
                  dist (skeleton.path x u) (skeleton.path x (center x i)) <
                    radius x (center x i) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal
  have hpath : forall x : M,
      exists (t : Nat -> unitInterval) (k : Nat)
          (center : Fin (k + 1) -> unitInterval) (eta : Real),
        t 0 = 0 ∧
          Monotone t ∧
            (∀ n ≥ k, t n = 1) ∧
              0 < eta ∧
                (forall i : Fin (k + 1), eta <= radius x (center i)) ∧
                  (forall (i : Fin (k + 1)) (u : unitInterval),
                    u ∈ Icc (t i) (t (i + 1)) ->
                      dist (skeleton.path x u) (skeleton.path x (center i)) <
                        radius x (center i)) ∧
                    Nonempty
                      (ReachableChain
                        (fun n => skeleton.path x (t n)) skeleton.root) := by
    intro x
    exact
      exists_reachableChain_with_common_pointwise_mesh_of_successor_radii
        g (skeleton.path x) skeleton.root (by simp) (radius x)
          (hradius x) (hlocal x)
  choose t k center eta htzero htmono htone heta hetaLower hcell hchain
    using hpath
  let realization : RootedPathChainRealization skeleton :=
    { nodeTime := t
      nodeTime_zero := htzero
      terminalIndex := k
      nodeTime_terminal := fun x => htone x (k x) le_rfl
      chain := fun x => Classical.choice (hchain x) }
  refine ⟨realization, center, eta, heta, hetaLower, ?_⟩
  intro x i u hu
  exact hcell x i u hu

/--
Every path in a rooted skeleton can be realized with one globally prescribed
positive metric mesh.  The finite subdivision and reached chain may depend on
the endpoint `x`, but the strict edge bound `mesh` does not.

This is stronger than taking a minimum over all source points: each compact
path is refined independently after the common mesh is fixed.  What remains
in `hlocal` is exactly the history-compatible local successor supply.
-/
theorem exists_rootedPathChainRealization_with_prescribed_mesh_of_successor_radii
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : M -> unitInterval -> Real),
      (forall x : M, forall c : unitInterval, 0 < radius x c) ->
      (forall (x : M) (c u v : unitInterval)
          (s : CartanChain.ChainState g),
        dist (skeleton.path x u) (skeleton.path x c) < radius x c ->
        dist (skeleton.path x v) (skeleton.path x c) < radius x c ->
        s.anchor = skeleton.path x u ->
          Nonempty (Data s (skeleton.path x v))) ->
      forall mesh : Real, 0 < mesh ->
        exists realization : RootedPathChainRealization skeleton,
          (forall x : M, 0 < realization.terminalIndex x) ∧
            (forall x : M, Monotone (realization.nodeTime x)) ∧
              (forall x : M, ∀ n ≥ realization.terminalIndex x,
                realization.nodeTime x n = 1) ∧
                forall (x : M) (n : Nat),
                  dist
                    (skeleton.path x (realization.nodeTime x n))
                    (skeleton.path x (realization.nodeTime x (n + 1))) <
                      mesh := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal mesh hmesh
  have hpath : forall x : M,
      exists (t : Nat -> unitInterval) (k : Nat),
        0 < k ∧
          t 0 = 0 ∧
            Monotone t ∧
              (∀ n ≥ k, t n = 1) ∧
                (forall n : Nat,
                  dist (skeleton.path x (t n))
                    (skeleton.path x (t (n + 1))) < mesh) ∧
                  Nonempty
                    (ReachableChain
                      (fun n => skeleton.path x (t n)) skeleton.root) := by
    intro x
    exact
      exists_reachableChain_with_prescribed_mesh_of_successor_radii
        g (skeleton.path x) skeleton.root (by simp) (radius x)
          (hradius x) (hlocal x) mesh hmesh
  choose t k hk htzero htmono htone hsmall hchain using hpath
  let realization : RootedPathChainRealization skeleton :=
    { nodeTime := t
      nodeTime_zero := htzero
      terminalIndex := k
      nodeTime_terminal := fun x => htone x (k x) le_rfl
      chain := fun x => Classical.choice (hchain x) }
  exact ⟨realization, hk, htmono, htone, hsmall⟩

/--
Forgetting the retained mesh certificate gives the rooted finite-chain
realization boundary used by the endpoint and adaptive-closeness modules.
-/
theorem nonempty_rootedPathChainRealization_of_successor_radii
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g) :
    letI : MetricSpace M := g.toMetricSpace
    forall (radius : M -> unitInterval -> Real),
      (forall x : M, forall c : unitInterval, 0 < radius x c) ->
      (forall (x : M) (c u v : unitInterval)
          (s : CartanChain.ChainState g),
        dist (skeleton.path x u) (skeleton.path x c) < radius x c ->
        dist (skeleton.path x v) (skeleton.path x c) < radius x c ->
        s.anchor = skeleton.path x u ->
          Nonempty (Data s (skeleton.path x v))) ->
      Nonempty (RootedPathChainRealization skeleton) := by
  letI : MetricSpace M := g.toMetricSpace
  intro radius hradius hlocal
  rcases
      exists_rootedPathChainRealization_with_common_pointwise_mesh_of_successor_radii
        skeleton radius hradius hlocal with
    ⟨realization, _center, _eta, _heta, _hlower, _hcell⟩
  exact ⟨realization⟩

end PathRealization

end CartanAtlasRootedPathAdaptiveMeshRealization
end Poincare
