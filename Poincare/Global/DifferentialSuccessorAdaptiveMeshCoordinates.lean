import Poincare.Global.DifferentialSuccessorAdaptiveHomotopyGrid

/-!
# Metric mesh control of differential-successor coordinates

The adaptive homotopy-grid theorem asks that the normal coordinates stored by
the finitely many actual successor data lie in one common coordinate ball.
This file derives that condition from ordinary metric closeness of consecutive
grid vertices.

For one predecessor state, the stored vector is the inverse normal coordinate
of the new anchor.  Continuity of that inverse coordinate at the predecessor
anchor therefore turns every prescribed vector radius into a positive metric
radius.  Taking a finite minimum makes this estimate uniform over the exact
bottom and rung histories used by a finite recursive grid.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorAdaptiveMeshCoordinates

universe u

local notation "E" => ClosedSmoothModel 3
local notation "Iₘ" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold Iₘ ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveHomotopyGrid

/-- A differential chain whose initial anchor is its zeroth node stays
anchored at the node carrying its index. -/
theorem differentialChain_chainState_anchor_eq_node
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (step : DifferentialInducedSuccessor.Chain.StepAvailable
      (g := g) nodes)
    (hzero : initial.anchor = nodes 0) :
    ∀ n : ℕ,
      (DifferentialInducedSuccessor.Chain.chainState
        nodes initial step n).anchor = nodes n := by
  intro n
  cases n with
  | zero => simpa using hzero
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        differentialChain_chainState_succ_anchor nodes initial step n

/-- For one predecessor state, sufficiently small metric displacement of a
new anchor forces every compatible differential-successor datum at that
anchor to have a prescribed small old normal coordinate. -/
theorem exists_distance_radius_for_data_vector_norm_lt
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {rho : ℝ} (hrho : 0 < rho) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
        dist z s.anchor < epsilon → ‖d.v‖ < rho := by
  letI : MetricSpace M := g.toMetricSpace
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let normalCoordinate : M → E := fun z ↦
    e.symm ((chartAt E s.anchor) z)
  have htarget : (chartAt E s.anchor) s.anchor ∈ e.target := by
    simpa [e, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) s.anchor
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E s.anchor) z) s.anchor := by
    simpa [extChartAt_coe] using continuousAt_extChartAt («I» := Iₘ) s.anchor
  have hnormal : ContinuousAt normalCoordinate s.anchor := by
    exact (e.continuousAt_symm htarget).comp hchart
  have hnormal_zero : normalCoordinate s.anchor = (0 : E) := by
    simpa [normalCoordinate, e] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero
        g s.anchor
  have hpreimage :
      normalCoordinate ⁻¹' Metric.ball (0 : E) rho ∈ 𝓝 s.anchor := by
    apply hnormal.preimage_mem_nhds
    rw [hnormal_zero]
    exact Metric.ball_mem_nhds (0 : E) hrho
  rcases Metric.mem_nhds_iff.mp hpreimage with
    ⟨epsilon, hepsilon, hball⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro z d hdist
  have hzball : z ∈ Metric.ball s.anchor epsilon := by
    simpa [Metric.mem_ball] using hdist
  have hzpre : normalCoordinate z ∈ Metric.ball (0 : E) rho :=
    hball hzball
  have hcoord : normalCoordinate z = d.v := by
    change e.symm ((chartAt E s.anchor) z) = d.v
    rw [show (chartAt E s.anchor) z = e d.v by
      simpa [e, extChartAt_coe] using d.source_coordinate]
    exact e.left_inv d.source_vector_mem
  rw [hcoord] at hzpre
  simpa [Metric.mem_ball, dist_eq_norm] using hzpre

/-- The metric radius controlling a successor coordinate depends only on the
predecessor anchor, not on the remaining fields of the predecessor state.

This is the anchor-uniform form needed to separate geometric subdivision from
the recursively generated successor histories: after an anchor `x` is fixed,
one radius works for every chain state anchored at `x` and every compatible
successor datum. -/
theorem exists_distance_radius_for_all_states_at_anchor
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M)
    {rho : ℝ} (hrho : 0 < rho) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (s : CartanChain.ChainState g), s.anchor = x →
        ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
          dist z x < epsilon → ‖d.v‖ < rho := by
  letI : MetricSpace M := g.toMetricSpace
  let e := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) x
  let normalCoordinate : M → E := fun z ↦
    e.symm ((chartAt E x) z)
  have htarget : (chartAt E x) x ∈ e.target := by
    simpa [e, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E x) z) x := by
    simpa [extChartAt_coe] using continuousAt_extChartAt («I» := Iₘ) x
  have hnormal : ContinuousAt normalCoordinate x := by
    exact (e.continuousAt_symm htarget).comp hchart
  have hnormal_zero : normalCoordinate x = (0 : E) := by
    simpa [normalCoordinate, e] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have hpreimage :
      normalCoordinate ⁻¹' Metric.ball (0 : E) rho ∈ 𝓝 x := by
    apply hnormal.preimage_mem_nhds
    rw [hnormal_zero]
    exact Metric.ball_mem_nhds (0 : E) hrho
  rcases Metric.mem_nhds_iff.mp hpreimage with
    ⟨epsilon, hepsilon, hball⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro s hs z d hdist
  have hzball : z ∈ Metric.ball x epsilon := by
    simpa [Metric.mem_ball] using hdist
  have hzpre : normalCoordinate z ∈ Metric.ball (0 : E) rho :=
    hball hzball
  have hcoord : normalCoordinate z = d.v := by
    change e.symm ((chartAt E x) z) = d.v
    rw [show (chartAt E x) z = e d.v by
      simpa [e, hs, extChartAt_coe] using d.source_coordinate]
    exact e.left_inv (by
      simpa [e, hs] using d.source_vector_mem)
  rw [hcoord] at hzpre
  simpa [Metric.mem_ball, dist_eq_norm] using hzpre

/-- A finite set of anchors admits one metric radius that controls successor
coordinates for every predecessor state lying over those anchors. -/
theorem exists_uniform_distance_radius_for_finite_anchors
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (anchor : iota → M) {rho : ℝ} (hrho : 0 < rho) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (i : iota) (s : CartanChain.ChainState g),
        s.anchor = anchor i →
        ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
          dist z (anchor i) < epsilon → ‖d.v‖ < rho := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hlocal : ∀ i : iota, ∃ epsilon > (0 : ℝ),
      ∀ (s : CartanChain.ChainState g), s.anchor = anchor i →
        ∀ {z : M} (d : DifferentialInducedSuccessor.Data s z),
          dist z (anchor i) < epsilon → ‖d.v‖ < rho := fun i ↦
    exists_distance_radius_for_all_states_at_anchor g (anchor i) hrho
  choose radius hradius hcontrol using hlocal
  let epsilon : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨epsilon, hepsilon, ?_⟩
  intro i s hs z d hdist
  apply hcontrol i s hs d
  exact hdist.trans_le
    (Finset.inf'_le radius (Finset.mem_univ i))

/-- A finite family of predecessor states admits one common metric radius
forcing all compatible successor coordinates into a prescribed vector ball. -/
theorem exists_uniform_distance_radius_for_finite_data_vectors
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (state : iota → CartanChain.ChainState g)
    {rho : ℝ} (hrho : 0 < rho) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (i : iota) {z : M}
        (d : DifferentialInducedSuccessor.Data (state i) z),
        dist z (state i).anchor < epsilon → ‖d.v‖ < rho := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hlocal : ∀ i : iota, ∃ epsilon > (0 : ℝ),
      ∀ {z : M} (d : DifferentialInducedSuccessor.Data (state i) z),
        dist z (state i).anchor < epsilon → ‖d.v‖ < rho := fun i ↦
    exists_distance_radius_for_data_vector_norm_lt (state i) hrho
  choose radius hradius hcontrol using hlocal
  let epsilon : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradius i
  refine ⟨epsilon, hepsilon, ?_⟩
  intro i z d hdist
  apply hcontrol i d
  exact hdist.trans_le
    (Finset.inf'_le radius (Finset.mem_univ i))

/-- Curvature and an ordinary horizontal/vertical mesh bound automatically
discharge the two explicit small-successor-coordinate premises of the finite
recursive grid theorem.  The coordinate radius is chosen from the finite set
of geometric grid anchors and is therefore independent of the recursively
generated states.  The returned second radius is the equality-patch mesh
radius; no coordinate norm assumptions remain in the public statement. -/
theorem exists_coordinate_mesh_radius_for_recursive_grid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval)
    (htzero : t 0 = 0)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < epsilon) →
      (∀ m : Fin (k + 1), ∀ j : Fin k,
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < epsilon) →
      ∃ delta > (0 : ℝ),
        (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) < delta) →
        (∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 2))
            (homotopyGridRow F t (m + 1) (j + 1)) < delta) →
        DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t 0) initial (step 0) (k + 1) =
          DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t (k + 1)) initial (step (k + 1))
              (k + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  let gridAnchor :
      ((Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin k)) →
        M
    | Sum.inl mj =>
        homotopyGridRow F t mj.1 mj.2
    | Sum.inr mj =>
        homotopyGridRow F t mj.1 (mj.2 + 1)
  rcases
      exists_mesh_radius_for_recursive_grid_of_curvature_and_small_successors
        hcurv F initial t step k htone with
    ⟨rho, hrho, hfinish⟩
  rcases exists_uniform_distance_radius_for_finite_anchors
      gridAnchor hrho with
    ⟨epsilon, hepsilon, hcoordinate⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hhorizontal hvertical
  have hrowZero : ∀ m : ℕ,
      initial.anchor = homotopyGridRow F t m 0 := by
    intro m
    simpa [homotopyGridRow, htzero] using hinitial
  have hbottomSmall : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      ‖(Classical.choice
        (step m j
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) j))).v‖ < rho := by
    intro m j
    let b := DifferentialInducedSuccessor.Chain.chainState
      (homotopyGridRow F t m) initial (step m) j
    let d : DifferentialInducedSuccessor.Data b
        (homotopyGridRow F t m (j + 1)) :=
      Classical.choice (step m j b)
    apply hcoordinate (Sum.inl (m, j)) b (by
      simpa [gridAnchor, b] using
        differentialChain_chainState_anchor_eq_node
          (homotopyGridRow F t m) initial (step m) (hrowZero m) j) d
    have hanchor : b.anchor = homotopyGridRow F t m j := by
      simpa [b] using
        differentialChain_chainState_anchor_eq_node
          (homotopyGridRow F t m) initial (step m) (hrowZero m) j
    simpa [gridAnchor, b, d, hanchor] using hhorizontal m j
  have hrungSmall : ∀ m : Fin (k + 1), ∀ j : Fin k,
      ‖(Classical.choice
        (step (m + 1) j
          (DifferentialInducedSuccessor.Chain.chainState
            (homotopyGridRow F t m) initial (step m) (j + 1)))).v‖ < rho := by
    intro m j
    let b := DifferentialInducedSuccessor.Chain.chainState
      (homotopyGridRow F t m) initial (step m) (j + 1)
    let d : DifferentialInducedSuccessor.Data b
        (homotopyGridRow F t (m + 1) (j + 1)) :=
      Classical.choice (step (m + 1) j b)
    apply hcoordinate (Sum.inr (m, j)) b (by
      simpa [gridAnchor, b] using
        differentialChain_chainState_anchor_eq_node
          (homotopyGridRow F t m) initial (step m) (hrowZero m) (j + 1)) d
    have hanchor : b.anchor = homotopyGridRow F t m (j + 1) := by
      simpa [b] using
        differentialChain_chainState_anchor_eq_node
          (homotopyGridRow F t m) initial (step m) (hrowZero m) (j + 1)
    simpa [gridAnchor, b, d, hanchor] using hvertical m j
  exact hfinish hbottomSmall hrungSmall

/-- The coordinate-control radius and the equality-patch radius can be
collapsed to one common mesh size.  Horizontal bounds are requested on all
rows used by either a bottom edge or an upper rung edge; vertical bounds are
requested on all columns used by either coordinate control or an opposite
vertex. -/
theorem exists_common_mesh_radius_for_recursive_grid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1) {x y : M}
    {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval)
    (htzero : t 0 = 0)
    (step : ∀ m : ℕ,
      DifferentialInducedSuccessor.Chain.StepAvailable (g := g)
        (homotopyGridRow F t m))
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < eta) →
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < eta) →
      DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t 0) initial (step 0) (k + 1) =
        DifferentialInducedSuccessor.Chain.chainState
          (homotopyGridRow F t (k + 1)) initial (step (k + 1))
            (k + 1) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_coordinate_mesh_radius_for_recursive_grid_of_curvature
      hcurv F initial hinitial t htzero step k htone with
    ⟨epsilon, hepsilon, hcoordinate⟩
  let Horizontal : ℝ → Prop := fun r ↦
    ∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t m (j + 1))
        (homotopyGridRow F t m j) < r
  let Vertical : ℝ → Prop := fun r ↦
    ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t (m + 1) (j + 1))
        (homotopyGridRow F t m (j + 1)) < r
  by_cases hmesh : Horizontal epsilon ∧ Vertical epsilon
  · have hhorizontalCoordinate :
        ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j) < epsilon := by
      intro m j
      exact hmesh.1 m.castSucc j
    have hverticalCoordinate :
        ∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) < epsilon := by
      intro m j
      exact hmesh.2 m j.castSucc
    rcases hcoordinate hhorizontalCoordinate hverticalCoordinate with
      ⟨delta, hdelta, hpatch⟩
    let eta : ℝ := min epsilon delta
    have heta : 0 < eta := lt_min hepsilon hdelta
    refine ⟨eta, heta, ?_⟩
    intro hhorizontal hvertical
    apply hpatch
    · intro m j
      exact (hvertical m j).trans_le (min_le_right epsilon delta)
    · intro m j
      have h := hhorizontal m.succ j.succ
      exact h.trans_le (min_le_right epsilon delta)
  · refine ⟨epsilon, hepsilon, ?_⟩
    intro hhorizontal hvertical
    exfalso
    apply hmesh
    exact ⟨hhorizontal, hvertical⟩

/-- Independently of the recursive successor histories, every continuous
homotopy rectangle admits an eventually stationary monotone subdivision whose
horizontal and vertical adjacent vertices are uniformly closer than a
prescribed positive radius.

This is the geometric subdivision half of the adaptive argument.  Applying it
to the state-dependent radius returned above still requires controlling the
feedback from changing the subdivision to changing the recursive states. -/
theorem exists_homotopy_grid_adjacent_dist_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    {eta : ℝ} (heta : 0 < eta) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ (t : ℕ → unitInterval) (k : ℕ),
      t 0 = 0 ∧ Monotone t ∧ (∀ n ≥ k, t n = 1) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F t n (m + 1))
            (homotopyGridRow F t n m) < eta) ∧
        (∀ n m : ℕ,
          dist (homotopyGridRow F t (n + 1) (m + 1))
            (homotopyGridRow F t n (m + 1)) < eta) := by
  letI : MetricSpace M := g.toMetricSpace
  let H : C(unitInterval × unitInterval, M) := F.toHomotopy.toContinuousMap
  have hcover : ∀ q : unitInterval × unitInterval,
      ∃ center : unitInterval × unitInterval,
        H q ∈ Metric.ball (H center) (eta / 2) := by
    intro q
    refine ⟨q, ?_⟩
    simpa [Metric.mem_ball] using half_pos heta
  rcases exists_homotopy_metricBall_grid g H
      (fun q : unitInterval × unitInterval ↦ H q)
      (fun _ : unitInterval × unitInterval ↦ eta / 2) hcover with
    ⟨t, htzero, htmono, ⟨k, htone⟩, hcell⟩
  refine ⟨t, k, htzero, htmono, htone, ?_, ?_⟩
  · intro n m
    rcases hcell n m with ⟨q, hq⟩
    have hnleft : t n ∈ Set.Icc (t n) (t (n + 1)) :=
      ⟨le_rfl, htmono (Nat.le_succ n)⟩
    have hmleft : t m ∈ Set.Icc (t m) (t (m + 1)) :=
      ⟨le_rfl, htmono (Nat.le_succ m)⟩
    have hmright : t (m + 1) ∈ Set.Icc (t m) (t (m + 1)) :=
      ⟨htmono (Nat.le_succ m), le_rfl⟩
    have hright := hq (t n) hnleft (t (m + 1)) hmright
    have hleft := hq (t n) hnleft (t m) hmleft
    rw [Metric.mem_ball] at hright hleft
    change dist (H (t n, t (m + 1))) (H (t n, t m)) < eta
    calc
      dist (H (t n, t (m + 1))) (H (t n, t m)) ≤
          dist (H (t n, t (m + 1))) (H q) +
            dist (H (t n, t m)) (H q) := dist_triangle_right _ _ _
      _ < eta / 2 + eta / 2 := add_lt_add hright hleft
      _ = eta := by ring
  · intro n m
    rcases hcell n m with ⟨q, hq⟩
    have hnleft : t n ∈ Set.Icc (t n) (t (n + 1)) :=
      ⟨le_rfl, htmono (Nat.le_succ n)⟩
    have hnright : t (n + 1) ∈ Set.Icc (t n) (t (n + 1)) :=
      ⟨htmono (Nat.le_succ n), le_rfl⟩
    have hmright : t (m + 1) ∈ Set.Icc (t m) (t (m + 1)) :=
      ⟨htmono (Nat.le_succ m), le_rfl⟩
    have hupper := hq (t (n + 1)) hnright (t (m + 1)) hmright
    have hlower := hq (t n) hnleft (t (m + 1)) hmright
    rw [Metric.mem_ball] at hupper hlower
    change dist (H (t (n + 1), t (m + 1)))
      (H (t n, t (m + 1))) < eta
    calc
      dist (H (t (n + 1), t (m + 1))) (H (t n, t (m + 1))) ≤
          dist (H (t (n + 1), t (m + 1))) (H q) +
            dist (H (t n, t (m + 1))) (H q) := dist_triangle_right _ _ _
      _ < eta / 2 + eta / 2 := add_lt_add hupper hlower
      _ = eta := by ring

end DifferentialSuccessorAdaptiveMeshCoordinates
end Poincare
