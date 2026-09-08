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

/-- Buffer-pair estimates and core retention have radii fixed before any chain state. -/
theorem exists_quantitativeCover : HasConstantSectionalCurvature3 g 1 →
    Nonempty (QuantitativeCover g) := by
  intro hcurv
  classical
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨C⟩ := exists_patchCover g
  obtain ⟨D⟩ := exists_patchCover roundSphereMetric3
  let A := Fin C.count × Fin D.count
  have hpairs : ∀ a : A, ∃ η > (0 : ℝ), ∃ ε > (0 : ℝ),
      FixedChartLocalSuccessorExistence.OnCompact (patch (C.patch a.1) (D.patch a.2))
        (C.buffer a.1) (D.buffer a.2) η ∧
      FixedChartLocalSuccessorEquality.OnCompact (patch (C.patch a.1) (D.patch a.2))
        (C.buffer a.1) (D.buffer a.2) η ε := by
    intro a
    exact FixedChartLocalSuccessorEquality.exists_radii
      (C.center a.1) (D.center a.2) (C.zone a.1) (D.zone a.2)
      (C.patch a.1) (D.patch a.2) hcurv (C.cutoff a.1) (D.cutoff a.2)
      (C.buffer a.1) (D.buffer a.2) (C.buffer_compact a.1) (C.buffer_subset a.1)
      (D.buffer_compact a.2) (D.buffer_subset a.2)
  choose η hη ε hε hdata hequality using hpairs
  obtain ⟨step, hstep, hstep_le⟩ := exists_positive_lower_bound η hη
  obtain ⟨evaluation, hevaluation, hevaluation_le⟩ := exists_positive_lower_bound ε hε
  have hretention : ∀ a : A, ∃ ρ > (0 : ℝ),
      ∀ s : CartanChain.ChainState g,
        s.anchor ∈ C.core a.1 → s.target ∈ D.core a.2 →
        ∀ z : M, dist z s.anchor < ρ →
          z ∈ interior (C.buffer a.1) ∧
          map (patch (C.patch a.1) (D.patch a.2)) s z ∈ interior (D.buffer a.2) := by
    intro a
    obtain ⟨ρ, hρ, hretain⟩ :=
      FixedChartLocalSuccessorEquality.exists_uniform_domain_radius_into_open
        (C.patch a.1) (D.patch a.2) (C.core a.1) (D.core a.2)
        (C.core_compact a.1)
        ((C.core_subset a.1).trans (interior_subset.trans (C.buffer_subset a.1)))
        (D.core_compact a.2)
        ((D.core_subset a.2).trans (interior_subset.trans (D.buffer_subset a.2)))
        (interior (C.buffer a.1)) (interior (D.buffer a.2))
        isOpen_interior (C.core_subset a.1) isOpen_interior (D.core_subset a.2)
    refine ⟨ρ, hρ, ?_⟩
    rintro ⟨x, p, L⟩ hx hp z hz
    obtain ⟨hzW, hzZ, _⟩ := hretain x hx p hp L z hz
    exact ⟨hzW, hzZ⟩
  choose ρ hρ hretain using hretention
  obtain ⟨retention, hretention_pos, hretention_le⟩ := exists_positive_lower_bound ρ hρ
  refine ⟨{
    source := C
    target := D
    step := step
    evaluation := evaluation
    retention := retention
    step_pos := hstep
    evaluation_pos := hevaluation
    retention_pos := hretention_pos
    h1 := ?_
    h2 := ?_
    retained := ?_ }⟩
  · intro i j x hx p hp L z hz
    exact hdata (i, j) x hx p hp L z (hz.trans_le (hstep_le (i, j)))
  · intro i j x hx p hp L z d hz
    obtain ⟨hsource, heq⟩ :=
      hequality (i, j) x hx p hp L z d (hz.trans_le (hstep_le (i, j)))
    exact ⟨(ball_subset_ball (hevaluation_le (i, j))).trans hsource,
      heq.mono (ball_subset_ball (hevaluation_le (i, j)))⟩
  · intro i j s hx hp z hz
    exact hretain (i, j) s hx hp z (hz.trans_le (hretention_le (i, j)))

end CartanSuppliedFinitePatchCover
end Poincare
