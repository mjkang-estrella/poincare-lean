import Poincare.Global.CartanSuppliedFinitePatchCover

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

namespace CartanSuppliedUniformPatchSwitch
open CartanSuppliedFinitePatchCover

structure SwitchControl (B : QuantitativeCover g) where
  radius : ℝ
  radius_pos : 0 < radius
  agreement : letI : MetricSpace M := g.toMetricSpace
    ∀ (a b : B.Label) (s : CartanChain.ChainState g),
      B.Buffered a s → B.Buffered b s →
      ball s.anchor radius ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor radius)

structure System (g : ClosedSmoothRiemannianMetric 3 M) where
  cover : QuantitativeCover g
  switch : SwitchControl cover

def System.mesh (S : System g) : ℝ :=
  min S.cover.step (min S.cover.evaluation
    (min S.cover.retention S.switch.radius)) / 32

/-- Buffered interpretations represent the same germ at their common geometric anchor. -/
theorem buffered_eventuallyEq : ∀ (B : QuantitativeCover g)
    (a b : B.Label) (s : CartanChain.ChainState g),
    B.Buffered a s → B.Buffered b s →
    map (B.interp a) s =ᶠ[𝓝 s.anchor] map (B.interp b) s := by
  intro B a b s ha hb
  have hlocal : ∀ c : B.Label, B.Buffered c s →
      map (B.interp c) s =ᶠ[𝓝 s.anchor] s.map := by
    intro c hc
    exact CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic
      (B.source.center c.1) (B.target.center c.2)
      (B.source.zone c.1) (B.target.zone c.2)
      (B.source.patch c.1) (B.target.patch c.2)
      (B.source.cutoff c.1) (B.target.cutoff c.2) s
      (B.source.buffer_subset c.1 hc.1) (B.target.buffer_subset c.2 hc.2)
  exact (hlocal a ha).trans (hlocal b hb).symm

/-- H1 already supplies one common source ball for every buffered patch pair. -/
theorem buffered_common_source (B : QuantitativeCover g) (a b : B.Label)
    (s : CartanChain.ChainState g) (ha : B.Buffered a s) (hb : B.Buffered b s) :
    letI : MetricSpace M := g.toMetricSpace
    ball s.anchor B.step ⊆ (germ (B.interp a) s).source ∩
      (germ (B.interp b) s).source := by
  letI : MetricSpace M := g.toMetricSpace
  intro z hz
  exact ⟨(B.h1 a.1 a.2 s.anchor ha.1 s.target ha.2 s.alignment z hz).2.2.1,
    (B.h1 b.1 b.2 s.anchor hb.1 s.target hb.2 s.alignment z hz).2.2.1⟩

/-- At each fixed state, a finite minimum works for every buffered label pair.
The radius here is still selected after the state, including its alignment. -/
theorem exists_state_switch_radius (B : QuantitativeCover g)
    (s : CartanChain.ChainState g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ρ > (0 : ℝ), ∀ a b : B.Label, B.Buffered a s → B.Buffered b s →
      ball s.anchor ρ ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor ρ) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hpairs : ∀ c : B.Label × B.Label, ∃ r > (0 : ℝ),
      B.Buffered c.1 s → B.Buffered c.2 s →
      ball s.anchor r ⊆ (germ (B.interp c.1) s).source ∩
        (germ (B.interp c.2) s).source ∧
      EqOn (map (B.interp c.1) s) (map (B.interp c.2) s) (ball s.anchor r) := by
    intro c
    by_cases ha : B.Buffered c.1 s
    · by_cases hb : B.Buffered c.2 s
      · obtain ⟨r, hr, heq⟩ := Metric.mem_nhds_iff.mp
          (buffered_eventuallyEq B c.1 c.2 s ha hb)
        refine ⟨min r B.step, lt_min hr B.step_pos, fun _ _ => ⟨?_, ?_⟩⟩
        · exact (ball_subset_ball (min_le_right _ _)).trans
            (buffered_common_source B c.1 c.2 s ha hb)
        · exact fun _ hz => heq (ball_subset_ball (min_le_left _ _) hz)
      · exact ⟨1, zero_lt_one, fun _ h => (hb h).elim⟩
    · exact ⟨1, zero_lt_one, fun h => (ha h).elim⟩
  letI : Fintype B.Label := inferInstanceAs
    (Fintype (Fin B.source.count × Fin B.target.count))
  choose r hr hagree using hpairs
  obtain ⟨ρ, hρ, hle⟩ := exists_positive_lower_bound r hr
  refine ⟨ρ, hρ, ?_⟩
  intro a b ha hb
  obtain ⟨hs, he⟩ := hagree (a, b) ha hb
  exact ⟨(ball_subset_ball (hle (a, b))).trans hs,
    he.mono (ball_subset_ball (hle (a, b)))⟩

/-- All four geometric radii contribute a positive operating mesh. -/
theorem mesh_pos : ∀ S : System g, 0 < S.mesh := by
  intro S
  exact div_pos (lt_min S.cover.step_pos (lt_min S.cover.evaluation_pos
    (lt_min S.cover.retention_pos S.switch.radius_pos))) (by norm_num)

end CartanSuppliedUniformPatchSwitch
end Poincare
