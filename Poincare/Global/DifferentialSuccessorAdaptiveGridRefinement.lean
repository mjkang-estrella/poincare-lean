import Poincare.Global.DifferentialSuccessorAdaptiveMeshCoordinates
import Poincare.Global.DifferentialSuccessorFiniteInsertionRefinement

/-!
# Cover-small adaptive grids which retain a realized subdivision

The ordinary compact-square subdivision theorem produces a new fine grid but
forgets the nodes of a previously realized grid.  Combining it with the finite
common-refinement theorem gives a stronger result: every old parameter value
is retained, while every new closed grid cell remains inside one cell of the
cover-subordinate fine grid.

This removes the purely geometric half of the adaptive feedback problem.  A
post-realization equality-patch cover can now be answered by a genuinely
refining grid rather than an unrelated candidate grid.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorAdaptiveGridRefinement

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorFiniteSubdivisionRefinement

/-- A metric-ball cover of a homotopy image admits a subordinate grid which
retains every node of a prescribed eventually stationary monotone
subdivision. -/
theorem exists_refining_homotopy_metricBall_grid
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (H : C(unitInterval × unitInterval, M))
    {J : Type*} (center : J → M) (radius : J → ℝ)
    (seed : ℕ → unitInterval) (hseedZero : seed 0 = 0)
    (hseedMono : Monotone seed) (seedK : ℕ)
    (hseedOne : ∀ n ≥ seedK, seed n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    (∀ q : unitInterval × unitInterval,
      ∃ j : J, H q ∈ Metric.ball (center j) (radius j)) →
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
        (∀ n, r (e n) = seed n) ∧
        ∀ n m, ∃ j : J,
          ∀ s ∈ Icc (r n) (r (n + 1)),
            ∀ u ∈ Icc (r m) (r (m + 1)),
              H (s, u) ∈ Metric.ball (center j) (radius j) := by
  letI : MetricSpace M := g.toMetricSpace
  intro hcover
  let c : J → Set (unitInterval × unitInterval) := fun j ↦
    H ⁻¹' Metric.ball (center j) (radius j)
  have hcOpen : ∀ j : J, IsOpen (c j) := by
    intro j
    exact Metric.isOpen_ball.preimage H.continuous
  have hcCover : (univ : Set (unitInterval × unitInterval)) ⊆ ⋃ j, c j := by
    intro q _hq
    rcases hcover q with ⟨j, hj⟩
    exact mem_iUnion.2 ⟨j, hj⟩
  rcases exists_common_refinement_subordinate_to_open_cover_prod
      seed hseedZero hseedMono seedK hseedOne hcOpen hcCover with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, hcell⟩
  refine ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
    heBound, heValue, ?_⟩
  intro n m
  rcases hcell n m with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro s hs u hu
  exact hj ⟨hs, hu⟩

/-- Every homotopy rectangle admits an arbitrarily fine metric grid which is
also a common refinement of a prescribed realized subdivision.

The factor map `e` records the old nodes exactly.  Horizontal and vertical
edge estimates hold on the refining grid itself, not on a separate candidate
sequence. -/
theorem exists_refining_homotopy_grid_adjacent_dist_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    {eta : ℝ} (heta : 0 < eta)
    (seed : ℕ → unitInterval) (hseedZero : seed 0 = 0)
    (hseedMono : Monotone seed) (seedK : ℕ)
    (hseedOne : ∀ n ≥ seedK, seed n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
        (∀ n, r (e n) = seed n) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F r n (m + 1))
            (homotopyGridRow F r n m) < eta) ∧
        ∀ n m : ℕ,
          dist (homotopyGridRow F r (n + 1) (m + 1))
            (homotopyGridRow F r n (m + 1)) < eta := by
  letI : MetricSpace M := g.toMetricSpace
  let H : C(unitInterval × unitInterval, M) := F.toHomotopy.toContinuousMap
  have hcover : ∀ q : unitInterval × unitInterval,
      ∃ center : unitInterval × unitInterval,
        H q ∈ Metric.ball (H center) (eta / 2) := by
    intro q
    refine ⟨q, ?_⟩
    simpa [Metric.mem_ball] using half_pos heta
  rcases exists_refining_homotopy_metricBall_grid g H
      (fun q : unitInterval × unitInterval ↦ H q)
      (fun _ : unitInterval × unitInterval ↦ eta / 2)
      seed hseedZero hseedMono seedK hseedOne hcover with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, hcell⟩
  refine ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
    heBound, heValue, ?_, ?_⟩
  · intro n m
    rcases hcell n m with ⟨q, hq⟩
    have hnleft : r n ∈ Icc (r n) (r (n + 1)) :=
      ⟨le_rfl, hrMono (Nat.le_succ n)⟩
    have hmleft : r m ∈ Icc (r m) (r (m + 1)) :=
      ⟨le_rfl, hrMono (Nat.le_succ m)⟩
    have hmright : r (m + 1) ∈ Icc (r m) (r (m + 1)) :=
      ⟨hrMono (Nat.le_succ m), le_rfl⟩
    have hright := hq (r n) hnleft (r (m + 1)) hmright
    have hleft := hq (r n) hnleft (r m) hmleft
    rw [Metric.mem_ball] at hright hleft
    change dist (H (r n, r (m + 1))) (H (r n, r m)) < eta
    calc
      dist (H (r n, r (m + 1))) (H (r n, r m)) ≤
          dist (H (r n, r (m + 1))) (H q) +
            dist (H (r n, r m)) (H q) :=
        dist_triangle_right _ _ _
      _ < eta / 2 + eta / 2 := add_lt_add hright hleft
      _ = eta := by ring
  · intro n m
    rcases hcell n m with ⟨q, hq⟩
    have hnleft : r n ∈ Icc (r n) (r (n + 1)) :=
      ⟨le_rfl, hrMono (Nat.le_succ n)⟩
    have hnright : r (n + 1) ∈ Icc (r n) (r (n + 1)) :=
      ⟨hrMono (Nat.le_succ n), le_rfl⟩
    have hmright : r (m + 1) ∈ Icc (r m) (r (m + 1)) :=
      ⟨hrMono (Nat.le_succ m), le_rfl⟩
    have hupper := hq (r (n + 1)) hnright (r (m + 1)) hmright
    have hlower := hq (r n) hnleft (r (m + 1)) hmright
    rw [Metric.mem_ball] at hupper hlower
    change dist (H (r (n + 1), r (m + 1)))
      (H (r n, r (m + 1))) < eta
    calc
      dist (H (r (n + 1), r (m + 1)))
          (H (r n, r (m + 1))) ≤
          dist (H (r (n + 1), r (m + 1))) (H q) +
            dist (H (r n, r (m + 1))) (H q) :=
        dist_triangle_right _ _ _
      _ < eta / 2 + eta / 2 := add_lt_add hupper hlower
      _ = eta := by ring

/-- If the realized seed grid has no repeated values before its terminal
index, the cover-small response grid retains it through a strictly increasing
factor map on that entire finite prefix.  This is the index property needed
to realize the refinement by genuine node insertions. -/
theorem exists_refining_homotopy_grid_adjacent_dist_lt_strict_factor
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    {eta : ℝ} (heta : 0 < eta)
    (seed : ℕ → unitInterval) (hseedZero : seed 0 = 0)
    (hseedMono : Monotone seed) (seedK : ℕ)
    (hseedOne : ∀ n ≥ seedK, seed n = 1)
    (hseedStrict : ∀ n < seedK, seed n < seed (n + 1)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
        (∀ n, r (e n) = seed n) ∧
        (∀ n < seedK, e n < e (n + 1)) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F r n (m + 1))
            (homotopyGridRow F r n m) < eta) ∧
        ∀ n m : ℕ,
          dist (homotopyGridRow F r (n + 1) (m + 1))
            (homotopyGridRow F r n (m + 1)) < eta := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_refining_homotopy_grid_adjacent_dist_lt g F heta
      seed hseedZero hseedMono seedK hseedOne with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, hhorizontal, hvertical⟩
  refine ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
    heBound, heValue, ?_, hhorizontal, hvertical⟩
  intro n hn
  exact factorMap_strict_step_of_strict_source heMono heValue
    (hseedStrict n hn)

end DifferentialSuccessorAdaptiveGridRefinement
end Poincare
