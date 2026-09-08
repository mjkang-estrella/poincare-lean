import Poincare.Global.FixedChartMappedGeodesicAssembly
import Poincare.Global.ControlledChartInstance

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
open CartanSuppliedDifferentialSuccessor

namespace CartanSuppliedFinitePatchCover
structure PatchCover (g : ClosedSmoothRiemannianMetric 3 M) where
  count : ℕ
  center : Fin count → M
  zone : Fin count → Set E
  patch : ∀ i, FixedChartUniformSourceNormal.Patch g (center i) (zone i)
  cutoff : ∀ i, zone i ⊆ IsometryInstantiate.cutoffOneLocus (center i)
  core : Fin count → Set M
  buffer : Fin count → Set M
  openCore : Fin count → Set M
  core_compact : ∀ i, IsCompact (core i)
  buffer_compact : ∀ i, IsCompact (buffer i)
  openCore_open : ∀ i, IsOpen (openCore i)
  openCore_subset : ∀ i, openCore i ⊆ core i
  core_subset : ∀ i, core i ⊆ interior (buffer i)
  buffer_subset : ∀ i, buffer i ⊆ (patch i).anchors
  lebesgue : ℝ
  lebesgue_pos : 0 < lebesgue
  ball_cover : letI : MetricSpace M := g.toMetricSpace
    ∀ x : M, ∃ i, ball x lebesgue ⊆ openCore i
  covers : ∀ x : M, ∃ i, x ∈ core i

def PatchCover.pick (C : PatchCover g) (x : M) : Fin C.count :=
  Classical.choose (C.covers x)

def Controlled (charts : ChartedSpace E M) (d : MetricSpace M) : Prop :=
  charts.atlas.Finite ∧ letI : MetricSpace M := d
    ∃ δ > (0 : ℝ), ∀ x : M, ball x δ ⊆ (charts.chartAt x).source

structure QuantitativeCover (g : ClosedSmoothRiemannianMetric 3 M) where
  source : PatchCover g
  target : PatchCover roundSphereMetric3
  step : ℝ
  evaluation : ℝ
  retention : ℝ
  step_pos : 0 < step
  evaluation_pos : 0 < evaluation
  retention_pos : 0 < retention
  h1 : ∀ i j, FixedChartLocalSuccessorExistence.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j) step
  h2 : ∀ i j, FixedChartLocalSuccessorEquality.OnCompact
    (patch (source.patch i) (target.patch j)) (source.buffer i) (target.buffer j)
    step evaluation
  retained : letI : MetricSpace M := g.toMetricSpace
    ∀ i j (s : CartanChain.ChainState g),
      s.anchor ∈ source.core i → s.target ∈ target.core j →
      ∀ z : M, dist z s.anchor < retention →
        z ∈ interior (source.buffer i) ∧
        map (patch (source.patch i) (target.patch j)) s z ∈ interior (target.buffer j)

def QuantitativeCover.Label (B : QuantitativeCover g) :=
  Fin B.source.count × Fin B.target.count

def QuantitativeCover.interp (B : QuantitativeCover g) (a : B.Label) : Interpretation g :=
  patch (B.source.patch a.1) (B.target.patch a.2)

def QuantitativeCover.Valid (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.core a.1 ∧ s.target ∈ B.target.core a.2

def QuantitativeCover.Buffered (B : QuantitativeCover g) (a : B.Label)
    (s : CartanChain.ChainState g) : Prop :=
  s.anchor ∈ B.source.buffer a.1 ∧ s.target ∈ B.target.buffer a.2

/-- Nested closed metric balls refine the open patch anchors to a finite cover. -/
theorem exists_patchCover : ∀ g : ClosedSmoothRiemannianMetric 3 M,
    Nonempty (PatchCover g) := by
  intro g
  classical
  letI : MetricSpace M := g.toMetricSpace
  let C (x : M) := Classical.choice (FixedChartUniformSourceNormal.exists_patch g x
    (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x))
  have hr : ∀ x : M, ∃ r > (0 : ℝ), ball x r ⊆ (C x).anchors := fun x =>
    Metric.mem_nhds_iff.mp ((C x).isOpen_anchors.mem_nhds (C x).center_mem_anchors)
  choose r hr hsub using hr
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => ball x (r x / 4)) (fun _ => isOpen_ball)
    (by intro x _; exact mem_iUnion.mpr ⟨x, mem_ball_self (div_pos (hr x) (by norm_num))⟩)
  have hcover : (univ : Set M) ⊆ ⋃ i : s, ball (i : M) (r i / 4) := by
    simpa only [iUnion_subtype] using hs
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i : s => isOpen_ball (x := (i : M)) (ε := r i / 4)) hcover
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hfinite : ∀ x : M, ∃ i : Fin (Fintype.card s),
      ball x δ ⊆ ball (e i : M) (r (e i) / 4) := by
    intro x
    obtain ⟨i, hi⟩ := hballs x (mem_univ x)
    exact ⟨e.symm i, by simpa using hi⟩
  refine ⟨{
    count := Fintype.card s
    center := fun i => (e i : M)
    zone := fun i => IsometryInstantiate.cutoffOneLocus (e i : M)
    patch := fun i => C (e i)
    cutoff := fun _ => Subset.rfl
    core := fun i => closedBall (e i : M) (r (e i) / 4)
    buffer := fun i => closedBall (e i : M) (r (e i) / 2)
    openCore := fun i => ball (e i : M) (r (e i) / 4)
    core_compact := fun _ => isClosed_closedBall.isCompact
    buffer_compact := fun _ => isClosed_closedBall.isCompact
    openCore_open := fun _ => isOpen_ball
    openCore_subset := fun _ => ball_subset_closedBall
    core_subset := ?_
    buffer_subset := ?_
    lebesgue := δ
    lebesgue_pos := hδ
    ball_cover := hfinite
    covers := ?_ }⟩
  · intro i
    exact (closedBall_subset_ball (by have := hr (e i); linarith)).trans
      ball_subset_interior_closedBall
  · intro i
    exact (closedBall_subset_ball (by have := hr (e i); linarith)).trans (hsub (e i))
  · intro x
    obtain ⟨i, hi⟩ := hfinite x
    exact ⟨i, ball_subset_closedBall (hi (mem_ball_self hδ))⟩

/-- A finite family of positive radii has a positive common lower bound. -/
theorem exists_positive_lower_bound {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ δ > (0 : ℝ), ∀ i, δ ≤ r i := by
  classical
  have h : ∀ s : Finset ι, ∃ δ > (0 : ℝ), ∀ i ∈ s, δ ≤ r i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, hle⟩ := ih
      refine ⟨min (r a) δ, lt_min (hr a) hδ, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hle i hi)
  obtain ⟨δ, hδ, hle⟩ := h Finset.univ
  exact ⟨δ, hδ, fun i => hle i (Finset.mem_univ i)⟩

end CartanSuppliedFinitePatchCover
end Poincare
