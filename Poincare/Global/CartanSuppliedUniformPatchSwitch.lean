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

end CartanSuppliedUniformPatchSwitch
end Poincare
