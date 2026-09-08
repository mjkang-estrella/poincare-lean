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

/-- Both successor anchors stay in prescribed open neighborhoods of the
compact predecessor anchors. The radius also retains the actual germ source. -/
theorem exists_uniform_domain_radius_into_open
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors)
    (W : Set M) (Z : Set RoundSphere3)
    (hW : IsOpen W) (hKW : K ⊆ W) (hZ : IsOpen Z) (hHZ : H ⊆ Z) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
        z ∈ W ∧ map (patch C D) ⟨x, p, L⟩ z ∈ Z ∧
        z ∈ (germ (patch C D) ⟨x, p, L⟩).source := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨B, hB, hbound⟩ :=
    FixedChartLocalSuccessorExistence.exists_uniform_linear_bound C D K H hK hKC hH hHD
  obtain ⟨ρ, hρ, htarget⟩ := exists_uniform_endpoint_radius_into_open D H hH hHD Z hZ hHZ
  obtain ⟨η, hη, hsource⟩ :=
    FixedChartLocalSuccessorExistence.exists_uniform_normal_radius C K hK hKC (div_pos hρ hB)
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro x hx p hp L z hz
  have hzW : z ∈ W :=
    hδW (mem_cthickening_of_dist_le z x δ K hx (hz.trans_le (min_le_left _ _)).le)
  obtain ⟨_, hzN, hv⟩ := hsource x hx z (hz.trans_le (min_le_right _ _))
  have hnorm : ‖linear (patch C D) ⟨x, p, L⟩ (C.normal x z)‖ < ρ := by
    calc
      _ ≤ ‖(linear (patch C D) ⟨x, p, L⟩ : E →L[ℝ] E)‖ * ‖C.normal x z‖ :=
        (linear (patch C D) ⟨x, p, L⟩ : E →L[ℝ] E).le_opNorm _
      _ ≤ B * ‖C.normal x z‖ :=
        mul_le_mul_of_nonneg_right (hbound x hx p hp L) (norm_nonneg _)
      _ < ρ := by simpa only [mul_comm B] using (lt_div_iff₀ hB).mp hv
  obtain ⟨htsrc, htZ⟩ := htarget p hp _ hnorm
  exact ⟨hzW, htZ, hzN, mem_univ _, htsrc⟩

/-- A full ball lies in both actual sources, with both radii chosen before
all moving anchors, alignments, and differential witnesses. -/
theorem exists_uniform_common_source_radii
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
        (d : Data (patch C D) ⟨x, p, L⟩ z), dist z x < η →
        ball z ε ⊆ (germ (patch C D) ⟨x, p, L⟩).source ∩
          (germ (patch C D) d.successor).source := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨K', hK', hKK', hK'C⟩ := exists_compact_between hK C.isOpen_anchors hKC
  obtain ⟨H', hH', hHH', hH'D⟩ := exists_compact_between hH D.isOpen_anchors hHD
  obtain ⟨ηr, hηr, hretain⟩ := exists_uniform_domain_radius_into_open C D K H hK hKC hH hHD
    (interior K') (interior H') isOpen_interior hKK' isOpen_interior hHH'
  obtain ⟨ηo, hηo, hold⟩ :=
    FixedChartLocalSuccessorExistence.exists_uniform_domain_radius C D K H hK hKC hH hHD
  obtain ⟨ηn, hηn, hnew⟩ :=
    FixedChartLocalSuccessorExistence.exists_uniform_domain_radius C D K' H' hK' hK'C hH' hH'D
  refine ⟨min ηr (ηo / 2), lt_min hηr (half_pos hηo),
    min (ηo / 2) ηn, lt_min (half_pos hηo) hηn, ?_⟩
  intro x hx p hp L z d hz y hy
  obtain ⟨hzK', hpH', _⟩ := hretain x hx p hp L z (hz.trans_le (min_le_left _ _))
  have hyz : dist y z < min (ηo / 2) ηn := hy
  have hyx : dist y x < ηo := by
    have hz' := hz.trans_le (min_le_right ηr (ηo / 2))
    have hy' := hyz.trans_le (min_le_left (ηo / 2) ηn)
    calc
      dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < ηo := by linarith
  refine ⟨(hold x hx p hp L y hyx).2.2, ?_⟩
  exact (hnew z (interior_subset hzK') (map (patch C D) ⟨x, p, L⟩ z)
    (interior_subset hpH') d.alignment y (hyz.trans_le (min_le_right _ _))).2.2

end FixedChartLocalSuccessorEquality
end Poincare
