import Poincare.Global.FixedChartLocalSuccessorExistence
import Poincare.Global.DifferentialSuccessorAdjacentContinuation

/-!
# Uniform common sources for supplied differential successors

The full-ball domain estimate is unconditional. Uniform equality of the
reanchored supplied maps is a separate analytic requirement.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartLocalSuccessorEquality
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3)
    (η ε : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : Data Q ⟨x, p, L⟩ z), dist z x < η →
      Metric.ball z ε ⊆ (germ Q ⟨x, p, L⟩).source ∩ (germ Q d.successor).source ∧
      EqOn (map Q ⟨x, p, L⟩) (map Q d.successor) (Metric.ball z ε)

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Small endpoint velocities stay in any prescribed open neighborhood of
all anchors in a compact set, with one radius chosen before those anchors. -/
theorem exists_uniform_endpoint_radius_into_open {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (W : Set M) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ W := by
  have he : ∀ᶠ v : E in 𝓝 0, ∀ x ∈ K,
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ W := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hxC := hKC hx
    have hxchart : x ∈ (chartAt E x₀).source := by
      simpa only [extChartAt_source] using hxC.1
    let f : E × M → E × E := fun q => (extChartAt I x₀ q.2, C.T⁻¹ • q.1)
    have hf : ContinuousAt f (0, x) :=
      ((continuousAt_extChartAt' hxC.1).comp continuousAt_snd).prodMk
        (continuousAt_const.smul continuousAt_fst)
    have hf0 : f (0, x) = (extChartAt I x₀ x, 0) := by simp [f]
    have hsrc : f (0, x) ∈ C.P.source := by
      rw [hf0]
      exact C.zero_mem_source _ hxC.2
    have hp : ContinuousAt (fun q => (C.P (f q)).2) (0, x) :=
      ((C.P.continuousAt hsrc).comp hf).snd
    have hp0 : (C.P (f (0, x))).2 = extChartAt I x₀ x := by
      rw [hf0, C.stationary _ hxC.2]
    have htarget : (C.P (f (0, x))).2 ∈ (chartAt E x₀).target := by
      rw [hp0]
      exact (chartAt E x₀).map_source hxchart
    have hc : ContinuousAt (fun q : E × M => C.endpoint q.2 q.1) (0, x) := by
      exact ((chartAt E x₀).continuousAt_symm htarget).comp
        (f := fun q : E × M => (C.P (f q)).2) hp
    have he0 : C.endpoint x (0 : E) = x := C.endpoint_zero x hxC
    have hret : ∀ᶠ q : E × M in 𝓝 (0, x), C.endpoint q.2 q.1 ∈ W := by
      apply hc.tendsto
      simpa only [he0] using hW.mem_nhds (hKW hx)
    filter_upwards [hf.tendsto (C.P.open_source.mem_nhds hsrc),
      hp.tendsto ((chartAt E x₀).open_target.mem_nhds htarget), hret] with q hq ht hr
    exact ⟨⟨⟨mem_univ _, hq⟩, ht⟩, hr⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ρ, hρ, fun x hx v hv => hball (by simpa using hv) x hx⟩

end FixedChartLocalSuccessorEquality
end Poincare
