import Poincare.Global.CartanSuppliedDifferentialTransfer
import Poincare.Global.TangentAlignmentFiberCompactness
import Poincare.Global.UniformTangentAlignmentRigidity

/-!
# Compact control of retained normal domains

These estimates concern the actual retained patch domains. The uniform
strict differential and metric-pullback witnesses needed for successor data
are not constructed here.
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

namespace FixedChartLocalSuccessorExistence
open CartanSuppliedDifferentialSuccessor
variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def OnCompact (Q : Interpretation g) (K : Set M) (H : Set RoundSphere3) (η : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ (x : M), x ∈ K → ∀ (p : RoundSphere3), p ∈ H →
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ Q.sourceAnchors ∧ map Q ⟨x, p, L⟩ z ∈ Q.targetAnchors ∧
    z ∈ (germ Q ⟨x, p, L⟩).source ∧ Nonempty (Data Q ⟨x, p, L⟩ z)

/-- A compact set of retained anchors has a common normal source radius,
with retained successor anchors and arbitrarily small normal vectors. -/
theorem exists_uniform_normal_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ z : M, dist z x < η →
      z ∈ C.anchors ∧ z ∈ (C.normal x).source ∧ ‖C.normal x z‖ < ρ := by
  letI : MetricSpace M := g.toMetricSpace
  let W : Set (M × M) := C.rawLocalFamily.controlledSourceLocus ρ ∩
    Prod.snd ⁻¹' C.anchors
  have hW : IsOpen W :=
    (C.rawLocalFamily.isOpen_controlledSourceLocus ρ).inter
      (C.isOpen_anchors.preimage continuous_snd)
  have hdiag : IsCompact ((fun x : M => (x, x)) '' K) :=
    hK.image (continuous_id.prodMk continuous_id)
  have hsub : (fun x : M => (x, x)) '' K ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨⟨hKC hx, C.anchor_mem_normal_source x (hKC hx)⟩, ?_⟩, hKC hx⟩
    change C.normal x x ∈ ball (0 : E) ρ
    rw [C.normal_anchor x (hKC hx)]
    exact mem_ball_self hρ
  obtain ⟨η, hη, hηW⟩ := hdiag.exists_cthickening_subset_open hW hsub
  refine ⟨η, hη, ?_⟩
  intro x hx z hz
  have hmem : (x, z) ∈ cthickening η ((fun x : M => (x, x)) '' K) := by
    apply mem_cthickening_of_dist_le (x, z) (x, x) η
      ((fun x : M => (x, x)) '' K) ⟨x, hx, rfl⟩
    simpa [Prod.dist_eq] using hz.le
  have hw := hηW hmem
  refine ⟨hw.2, hw.1.1.2, ?_⟩
  simpa [CartanSourceExponential.LocalFamily.controlledSourceLocus,
    FixedChartUniformSourceNormal.Patch.rawLocalFamily, mem_ball, dist_eq_norm] using hw.1.2

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Small velocities share the actual endpoint domain over a compact anchor
set, and their endpoints remain available as new anchors. -/
theorem exists_uniform_endpoint_radius {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) :
    ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ v : E, ‖v‖ < ρ →
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ C.anchors := by
  have he : ∀ᶠ v : E in 𝓝 0, ∀ x ∈ K,
      v ∈ (C.endpoint x).source ∧ C.endpoint x v ∈ C.anchors := by
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
    have hret : ∀ᶠ q : E × M in 𝓝 (0, x), C.endpoint q.2 q.1 ∈ C.anchors := by
      apply hc.tendsto
      simpa only [he0] using C.isOpen_anchors.mem_nhds hxC
    filter_upwards [hf.tendsto (C.P.open_source.mem_nhds hsrc),
      hp.tendsto ((chartAt E x₀).open_target.mem_nhds htarget), hret] with q hq ht hr
    exact ⟨⟨⟨mem_univ _, hq⟩, ht⟩, hr⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨ρ, hρ, fun x hx v hv => hball (by simpa using hv) x hx⟩

omit [CompactSpace M] [ConnectedSpace M] in
/-- The fixed host metric is uniformly comparable to the model norm on
every compact retained anchor set. -/
theorem exists_uniform_host_metric_comparison {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (K : Set M) (hK : IsCompact K) (hKC : K ⊆ C.anchors) :
    ∃ a > (0 : ℝ), ∃ b > (0 : ℝ), ∀ x ∈ K, ∀ v : E,
      a * ‖v‖ ^ 2 ≤ CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) v v ∧
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) v v ≤ b * ‖v‖ ^ 2 := by
  let G : M → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x)
  have hG : ContinuousOn G K := by
    intro x hx
    exact ((UniformAnchoredFTransition.chartMetric_contDiffAt_one_of_mem_target
      g x₀ ((extChartAt I x₀).map_source (hKC hx).1)).continuousAt.comp
        (continuousAt_extChartAt' (hKC hx).1)).continuousWithinAt
  have hcompact : IsCompact (K ×ˢ sphere (0 : E) 1) := hK.prod (isCompact_sphere 0 1)
  have hcontinuous : ContinuousOn (fun q : M × E => G q.1 q.2 q.2)
      (K ×ˢ sphere (0 : E) 1) :=
    ((hG.comp continuousOn_fst (fun _ hq => hq.1)).clm_apply continuousOn_snd).clm_apply
      continuousOn_snd
  have hpositive : ∀ q ∈ K ×ˢ sphere (0 : E) 1, 0 < G q.1 q.2 q.2 := by
    intro q hq
    apply CovariantDerivative.chartMetric_posDef g.inner (fun y v hv => g.pos y v hv) x₀
      (isInvertible_mfderivWithin_extChartAt_symm
        ((extChartAt I x₀).map_source (hKC hq.1).1))
    have hn : ‖q.2‖ = 1 := by simpa using hq.2
    intro hz
    simp [hz] at hn
  obtain ⟨a, ha, halower⟩ := hcompact.exists_forall_le' hcontinuous hpositive
  have hbounded : Bornology.IsBounded (G '' K) := (hK.image_of_continuousOn hG).isBounded
  obtain ⟨b, hb, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨a, ha, b, hb, ?_⟩
  intro x hx v
  constructor
  · by_cases hv : v = 0
    · simp [hv]
    have hn := norm_ne_zero_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv
    have hr : ‖v‖ • w = v := by
      simp [w, smul_smul, hn]
    have he : G x v v = ‖v‖ ^ 2 * G x w w := by
      conv_lhs => rw [← hr]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    change a * ‖v‖ ^ 2 ≤ G x v v
    rw [he, mul_comm a]
    exact mul_le_mul_of_nonneg_left (halower (x, w) ⟨hx, hw⟩) (sq_nonneg _)
  · have hbG : ‖G x‖ ≤ b := hbound _ ⟨x, hx, rfl⟩
    change G x v v ≤ b * ‖v‖ ^ 2
    calc
      G x v v ≤ ‖G x v v‖ := Real.le_norm_self _
      _ ≤ ‖G x‖ * ‖v‖ * ‖v‖ := (G x).le_opNorm₂ v v
      _ ≤ b * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The retained frame transports the host metric to the preferred anchor metric. -/
theorem patchFrame_metric {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (hx : x ∈ C.anchors) (u v : E) :
    CartanMap.sourceAnchorChartMetric g x (patchFrame C x u) (patchFrame C x v) =
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) u v := by
  have hframe : (patchFrame C x : E →L[ℝ] E) =
      FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x := by
    unfold patchFrame
    rw [dif_pos hx]
    exact Classical.choose_spec
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx)
  have hy : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈ (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  have ht := GeodesicTransport.chartMetric_chartTransitionDeriv g x₀ x
    ((extChartAt I x₀).map_source hx.1) hy u v
  have hpoint : GeodesicTransport.chartTransition x₀ x (extChartAt I x₀ x) =
      extChartAt I x x := by
    change extChartAt I x ((extChartAt I x₀).symm (extChartAt I x₀ x)) = _
    rw [(extChartAt I x₀).left_inv hx.1]
  rw [hpoint] at ht
  change CartanMap.sourceAnchorChartMetric g x
    ((patchFrame C x : E →L[ℝ] E) u) ((patchFrame C x : E →L[ℝ] E) v) = _
  rw [hframe]
  exact ht

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Framed alignments preserve the two fixed host metrics at the moving anchors. -/
theorem linear_metric {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (x : M) (hx : x ∈ C.anchors) (p : RoundSphere3) (hp : p ∈ D.anchors)
    (L : CartanMap.TangentAlignment g x p) (u v : E) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ (extChartAt I p₀ p)
      (linear (patch C D) ⟨x, p, L⟩ u) (linear (patch C D) ⟨x, p, L⟩ v) =
      CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x) u v := by
  calc
    _ = CartanMap.targetAnchorChartMetric p
        (patchFrame D p (linear (patch C D) ⟨x, p, L⟩ u))
        (patchFrame D p (linear (patch C D) ⟨x, p, L⟩ v)) :=
      (patchFrame_metric D p hp _ _).symm
    _ = CartanMap.targetAnchorChartMetric p
        (L (patchFrame C x u)) (L (patchFrame C x v)) := by simp [linear, patch]
    _ = CartanMap.sourceAnchorChartMetric g x (patchFrame C x u) (patchFrame C x v) :=
      L.map_app _ _
    _ = _ := patchFrame_metric C x hx u v

end FixedChartLocalSuccessorExistence
end Poincare
